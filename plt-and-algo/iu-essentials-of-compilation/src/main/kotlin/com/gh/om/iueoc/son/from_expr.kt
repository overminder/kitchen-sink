package com.gh.om.iueoc.son

import com.gh.om.iueoc.AnnExpr
import com.gh.om.iueoc.AnnS
import com.gh.om.iueoc.EocError
import com.gh.om.iueoc.ExprLam
import com.gh.om.iueoc.ExprOp
import com.gh.om.iueoc.ExprVar
import com.gh.om.iueoc.LetKind
import com.gh.om.iueoc.PrimOp
import com.gh.om.iueoc.SourceLoc
import com.gh.om.iueoc.wrap

// Data class for hashcode and equals
private data class ValueNodeEqWrapper(
    val opCode: OpCode,
    val parameter: Any?,
    // Looks really inefficient lol
    // Ordering is important -- `a - b` is not the same as `b - a`.
    val inputs: List<NodeId>
)

typealias NodeEnv = MutableMap<String, NodeId>

// Freshly created nodes are not inserted into the graph yet:
// - No valid id
// - Inputs / outputs not yet populated.
// Steps to insert a node:
// 1. For value nodes: populate the inputs, and do GVN. If GVN returns an existing one, use that.
//    Otherwise assign an Id to this fresh node, put into GVN cache, and use it.
// 2. For control nodes: (partially) populate its inputs and outputs, and we are good.

class EnvChain(
    private val bindings: NodeEnv = mutableMapOf(),
    private val parent: EnvChain? = null
) {

    fun extend(newBindings: NodeEnv): EnvChain {
        return EnvChain(newBindings, this)
    }

    // Useful for determining the available free vars when making closures
    fun flatten(): NodeEnv {
        val out: NodeEnv = mutableMapOf()
        tailrec fun go(e: EnvChain) {
            e.bindings.forEach { (key, value) ->
                if (key !in out) {
                    out[key] = value
                }
            }
            if (e.parent != null) {
                go(e.parent)
            }
        }
        go(this)
        return out
    }

    operator fun get(name: String, loc: SourceLoc): NodeId {
        var here: EnvChain = this
        while (true) {
            val value = here.bindings[name]
            if (value == null) {
                val next = here.parent
                EocError.ensure(next != null, loc) {
                    "Unbound var $name. All vars: ${flatten().keys}"
                }
                here = next
            } else {
                return value
            }
        }
    }
}

interface MultiGraph {
    val graphs: Map<GraphId, AnnS<Graph>>
}

/**
 * Do closure conversion by collecting nested lambdas.
 */
class MultiGraphBuilder : MultiGraph {
    override val graphs
        get() = _graphs

    private var idGen: Int = FIRST_ID
    fun nextId(): Int = idGen++
    private val _graphs = mutableMapOf<GraphId, AnnS<GraphBuilder>>()

    private operator fun get(id: GraphId): GraphBuilder {
        return requireNotNull(_graphs[id]) {
            "$id not found. All ids: ${_graphs.keys}"
        }.unwrap
    }

    /**
     * @param outerEnv Flattened free vars from the outer lexical scope.
     * @param name The function name
     */
    fun build(
        outerEnv: EnvChain?,
        name: String?,
        args: List<AnnS<String>>,
        body: List<AnnExpr>,
        rootAnn: SourceLoc
    ): GraphBuilder {
        val outerFlatEnv = outerEnv?.let {
            outerEnv.flatten() - args.map { it.unwrap }
        }.orEmpty()

        val gb = GraphBuilder(this, name)
        val gid = nextId()
        _graphs[gid] = rootAnn.wrap(gb)

        val env = gb.populateArgs(args, outerFlatEnv.keys)
        gb.doFunctionBody(gid, body, env)
        GraphVerifier(gb).verifyFullyBuilt()
        return gb
    }

    /**
     * @param outerEnv The env to be enclosed by the lambda
     */
    fun buildLam(outerEnv: EnvChain, lam: ExprLam.Lam, ann: SourceLoc): Pair<GraphId, List<String>> {
        val g = build(outerEnv, lam.name, lam.args, lam.body, ann)

        // Compact free vars in lambda
        val usedFreeVars = g.compactFreeVars()

        return g.id to usedFreeVars
    }

    companion object {
        const val FIRST_ID = 1
        const val FRESH_ID = -2
        fun isValidId(graphId: GraphId): Boolean {
            return graphId >= FIRST_ID
        }
    }
}

typealias GraphId = Int

class GraphBuilder(private val multiGraphBuilder: MultiGraphBuilder, override val name: String?) : Graph {
    private var idGen: Int = NodeIds.FIRST_ID_IN_GRAPH
    private fun nextId(): Int = idGen++

    override val nodes: MutNodeMap = mutableMapOf()

    override val start: NodeId
    override val end: NodeId
    private val dead: NodeId

    override var id: GraphId = MultiGraphBuilder.FRESH_ID
        private set

    // Although nodes are mutable, we don't mutate value nodes during graph building.
    private val gvnCache = mutableMapOf<ValueNodeEqWrapper, NodeId>()

    private var currentRegion: NodeId? = null
    private var currentMemory: NodeId

    init {
        start = assignId(Nodes.start()).id
        end = assignId(Nodes.end()).id
        dead = assignId(Nodes.dead()).id
        currentMemory = assignId(Nodes.memory()).id

        get(currentMemory).addInput(get(start), EdgeKind.Value, populating = true)
    }

    private fun startRegion(nPreds: Int = 1, nPhis: Int = 0): Node {
        // require(currentRegion == null)
        val region = Nodes.region(nPreds = nPreds, nPhis = nPhis)
        currentRegion = assignId(region).id
        return region
    }

    private fun assertCurrentRegion(): NodeId {
        return requireNotNull(currentRegion)
    }

    private fun projectMemoryFrom(node: Node) {
        val updatedMemory = assignId(Nodes.memory())
        updatedMemory.addInput(node, EdgeKind.Value, populating = true)
        currentMemory = updatedMemory.id
    }

    fun populateArgs(args: Collection<AnnS<String>>, freeVars: Collection<String>): EnvChain {
        val env: NodeEnv = mutableMapOf()

        freeVars.withIndex().associateTo(env) { (index, freeVar) ->
            val extra = FreeVarOpExtra(freeVar, index)
            val node = assignId(Nodes.freeVar(extra))
            node.addInput(get(start), EdgeKind.Value, populating = true)
            freeVar to node.id
        }

        args.withIndex().associateTo(env) { (index, arg) ->
            val extra = ArgumentOpExtra(arg.unwrap, index)
            val node = assignId(Nodes.argument(extra))
            node.addInput(get(start), EdgeKind.Value, populating = true)
            arg.unwrap to node.id
        }

        return EnvChain(env)
    }

    fun doFunctionBody(graphId: GraphId, body: List<AnnExpr>, env: EnvChain) {
        require(id == MultiGraphBuilder.FRESH_ID)
        id = graphId

        startRegion().addInput(get(start), EdgeKind.Control, populating = true)

        // Evaluate and throw away result values for body[:-1]
        body.take(body.size - 1).forEach {
            doExpr(it, env)
        }
        val returnValue = get(doExpr(body.last(), env))
        val exitRegion = get(assertCurrentRegion())

        val returnNode = assignId(Nodes.ret())
        returnNode.addInput(get(currentMemory), EdgeKind.Value, populating = true)
        returnNode.addInput(returnValue, EdgeKind.Value, populating = true)
        returnNode.addInput(exitRegion, EdgeKind.Control, populating = true)

        get(end).addInput(returnNode, EdgeKind.Control, populating = true)
    }

    fun doExpr(annE: AnnExpr, env: EnvChain): NodeId {
        return when (val e = annE.unwrap) {
            is ExprOp.If -> {
                // Evaluate condValue, set up condJump
                val condValue = doExpr(e.cond, env)
                val condJump = assignId(Nodes.condJump())
                condJump.addInput(get(condValue), EdgeKind.Value, populating = true)
                condJump.addInput(get(assertCurrentRegion()), EdgeKind.Control, populating = true)

                // Make projections
                val ifT = assignId(Nodes.ifT())
                val ifF = assignId(Nodes.ifF())
                ifT.addInput(condJump, EdgeKind.Control, populating = true)
                ifF.addInput(condJump, EdgeKind.Control, populating = true)

                // True branch
                startRegion().addInput(ifT, EdgeKind.Control, populating = true)
                val tValue = doExpr(e.ifT, env)
                val tValueRegion = assertCurrentRegion()
                val tMemory = currentMemory
                val tJump = assignId(Nodes.jump())
                tJump.addInput(get(tValueRegion), EdgeKind.Control, populating = true)

                // False branch
                startRegion().addInput(ifF, EdgeKind.Control, populating = true)
                val fValue = doExpr(e.ifF, env)
                val fValueRegion = assertCurrentRegion()
                val fMemory = currentMemory
                val fJump = assignId(Nodes.jump())
                fJump.addInput(get(fValueRegion), EdgeKind.Control, populating = true)

                joinControlFlow(tValue, tMemory, fValue, fMemory, tJump, fJump)
            }
            is ExprOp.Let -> {
                val newEnv = when (e.kind) {
                    LetKind.Basic -> {
                        val newBindings = e.vs.zip(e.es).associateTo(mutableMapOf()) { (name, rhs) ->
                            val value = doExpr(rhs, env)
                            name.unwrap to value
                        }
                        env.extend(newBindings)
                    }
                    LetKind.Seq -> {
                        val newBindings: NodeEnv = mutableMapOf()
                        val newEnv = env.extend(newBindings)
                        // Mutate the current env on the go.
                        e.vs.zip(e.es).associateTo(newBindings) { (name, rhs) ->
                            val value = doExpr(rhs, newEnv)
                            name.unwrap to value
                        }
                        newEnv
                    }
                    LetKind.Rec -> {
                        EocError.todo(annE.ann, "letrec not yet implemented")
                    }
                }
                doExpr(e.body, newEnv)
            }
            is ExprOp.Op -> {
                val values = e.args.map { doExpr(it, env) }
                when (e.op.unwrap) {
                    PrimOp.FxAdd -> {
                        tryGvn(Nodes.fxAdd(), values)
                    }
                    PrimOp.FxLessThan -> {
                        tryGvn(Nodes.fxLessThan(), values)
                    }
                    PrimOp.BoxMk -> {
                        val valueToBox = values.first()
                        val boxNode = assignId(Nodes.boxLit())
                        boxNode.addInput(get(valueToBox), EdgeKind.Value, populating = true)
                        boxNode.id
                    }
                    PrimOp.BoxGet -> {
                        val boxValue = values.first()
                        val getter = assignId(Nodes.boxGet())
                        getter.addInput(get(currentMemory), EdgeKind.Value, populating = true)
                        getter.addInput(get(boxValue), EdgeKind.Value, populating = true)
                        getter.id
                    }
                    PrimOp.BoxSet -> {
                        val (boxValue, newValue) = values
                        val setter = assignId(Nodes.boxSet())
                        setter.addInput(get(currentMemory), EdgeKind.Value, populating = true)
                        setter.addInput(get(boxValue), EdgeKind.Value, populating = true)
                        setter.addInput(get(newValue), EdgeKind.Value, populating = true)
                        projectMemoryFrom(setter)
                        setter.id
                    }
                }
            }
            is ExprVar.B -> {
                tryGvn(Nodes.boolLit(e.value))
            }
            is ExprVar.I -> {
                tryGvn(Nodes.intLit(e.value))
            }
            is ExprVar.Sym -> {
                tryGvn(Nodes.symbolLit(e.name))
            }
            is ExprVar.V -> env[e.name, annE.ann]
            is ExprLam.Ap -> {
                EocError.todo(annE.ann, "Not implemented: $e")
            }
            is ExprLam.Lam -> {
                val (gid, freeVarNames) = multiGraphBuilder.buildLam(env, e, annE.ann)
                val lambdaNode = assignId(Nodes.lambdaLit(gid))
                val inputs = freeVarNames.map {
                    // This should never fail, as the checking was done earlier in buildLam.
                    env[it, annE.ann]
                }
                inputs.forEach {
                    lambdaNode.addInput(get(it), EdgeKind.Value)
                }
                lambdaNode.id
            }
        }
    }

    private fun joinControlFlow(
        tValue: NodeId,
        tMemory: NodeId,
        fValue: NodeId,
        fMemory: NodeId,
        tJump: Node,
        fJump: Node
    ): NodeId {
        val needPhi = tValue != fValue
        val needMemoryPhi = tMemory != fMemory
        // Make a region as a join point
        // v8/hotspot's Merge node may be able to simplify the structure.
        // Both branches may be returning the same thing. In that case we don't need a phi.
        val joinRegion = startRegion(nPreds = 2, nPhis = needPhi.b2i + needMemoryPhi.b2i)
        joinRegion.addInput(tJump, EdgeKind.Control, populating = true)
        joinRegion.addInput(fJump, EdgeKind.Control, populating = true)
        if (needMemoryPhi) {
            val memoryPhi = assignId(Nodes.memoryPhi(2))
            memoryPhi.addInput(joinRegion, EdgeKind.Control, populating = true)
            memoryPhi.addInput(get(tMemory), EdgeKind.Value, populating = true)
            memoryPhi.addInput(get(fMemory), EdgeKind.Value, populating = true)
            currentMemory = memoryPhi.id
        }
        return if (needPhi) {
            val phi = assignId(Nodes.phi(2))
            phi.addInput(joinRegion, EdgeKind.Control, populating = true)
            phi.addInput(get(tValue), EdgeKind.Value, populating = true)
            phi.addInput(get(fValue), EdgeKind.Value, populating = true)
            phi.id
        } else {
            tValue
        }
    }

    private fun assignId(node: Node): Node {
        node.assignId(nextId())
        nodes[node.id] = node
        return node
    }

    /**
     * Try to use an existing value node from the graph. The value node should be pure.
     * [n] should be fresh, and its [valueInputs] are inserted to [n] by this function.
     */
    private fun tryGvn(n: Node, valueInputs: List<NodeId> = emptyList()): NodeId {
        val rator = n.operator
        require(rator.op.isPure)
        val key = ValueNodeEqWrapper(rator.op, rator.extra, valueInputs)
        val cached = gvnCache[key]
        return if (cached == null) {
            // Save to cache.
            gvnCache[key] = assignId(n).id
            // Populate edges
            valueInputs.forEach {
                n.addInput(get(it), EdgeKind.Value, populating = true)
            }
            n.id
        } else {
            cached
        }
    }

    /**
     * Remove free vars that are not lexically referred to.
     */
    fun compactFreeVars(): List<String> {
        val (used, unused) = get(start).valueOutputs.map(::get).filter {
            // For each free vars...
            it.operator.op == OpCode.FreeVar
        }.partition {
            // Find out the ones that are not used.
            it.valueOutputs.isNotEmpty()
        }

        unused.forEach {
            // Two ways to remove an edge from a graph.
            // We can either remove the input entirely.
            // But that can result in a partial node -- What's the meaning of an Add node with only 1 input?
            // I see v8 uses "dead" node as a placeholder input. This way the changed node still gets to keep the
            // correct number of input counts.
            it.replaceInput(get(it.singleControlInput), get(dead), EdgeKind.Control)
        }

        used.forEachIndexed { index, n ->
            // Compact
            n.updateOperator {
                val extra = it.extra as FreeVarOpExtra
                it.copy(extra = extra.withIndex(index))
            }
        }

        return used.map {
            val extra = it.operator.extra as FreeVarOpExtra
            extra.name
        }
    }
}

private val Boolean.b2i: Int
    get() = if (this) 1 else 0