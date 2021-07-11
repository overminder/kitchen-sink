package com.gh.om.iueoc.son

import com.gh.om.iueoc.AnnExpr
import com.gh.om.iueoc.AnnS
import com.gh.om.iueoc.EocError
import com.gh.om.iueoc.ExprImp
import com.gh.om.iueoc.ExprLam
import com.gh.om.iueoc.ExprOp
import com.gh.om.iueoc.ExprVar
import com.gh.om.iueoc.LetKind
import com.gh.om.iueoc.PrimOp
import com.gh.om.iueoc.SourceLoc
import com.gh.om.iueoc.wrap
import kotlinx.collections.immutable.PersistentMap
import kotlinx.collections.immutable.persistentMapOf
import kotlinx.collections.immutable.putAll
import kotlinx.collections.immutable.toPersistentMap

// Data class for hashcode and equals
private data class ValueNodeEqWrapper(
    val opCode: OpCode,
    val parameter: Any?,
    // Looks really inefficient lol
    // Ordering is important -- `a - b` is not the same as `b - a`.
    val inputs: List<NodeId>
)

typealias NodeEnv = PersistentMap<String, NodeId>

// Freshly created nodes are not inserted into the graph yet:
// - No valid id
// - Inputs / outputs not yet populated.
// Steps to insert a node:
// 1. For value nodes: populate the inputs, and do GVN. If GVN returns an existing one, use that.
//    Otherwise assign an Id to this fresh node, put into GVN cache, and use it.
// 2. For control nodes: (partially) populate its inputs and outputs, and we are good.

class EnvChain(
    private val bindings: NodeEnv = persistentMapOf(),
    private val parent: EnvChain? = null
) {

    fun extend(newBindings: NodeEnv): EnvChain {
        return EnvChain(newBindings, this)
    }

    // Useful for determining the available free vars when making closures
    fun flatten(): NodeEnv {
        var out: NodeEnv = persistentMapOf()
        tailrec fun go(e: EnvChain) {
            e.bindings.forEach { (key, value) ->
                if (key !in out) {
                    out = out.put(key, value)
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

    fun deepCopy(graphId: GraphId): Graph
    fun remove(id: GraphId)
}

operator fun MultiGraph.get(graphId: GraphId): Graph {
    return requireNotNull(graphs[graphId]) {
        "$graphId not found. All ids: ${graphs.keys}"
    }.unwrap
}

/**
 * Do closure conversion by collecting nested lambdas.
 */
class MultiGraphBuilder : MultiGraph {
    override val graphs = mutableMapOf<GraphId, AnnS<Graph>>()

    private var idGen = FIRST_ID
    fun nextId(): GraphId {
        val ret = idGen
        idGen = GraphId(idGen.v + 1)
        return ret
    }

    /*
    operator fun get(graphId: GraphId): GraphBuilder {
        return requireNotNull(graphs[graphId]) {
            "$graphId not found. All ids: ${graphs.keys}"
        }.unwrap
    }

     */

    override fun deepCopy(graphId: GraphId): Graph {
        val (ann, from) = requireNotNull(graphs[graphId])
        val nodes: MutNodeMap = mutableMapOf()
        for (n0 in NodeTraversal(from).liveNodes) {
            val n = n0.deepCopy()
            nodes[n.id] = n
        }
        val cg = CopiedGraph(this, from.name, nodes, from.start, from.end, nextId())
        GraphVerifier(cg).verifyFullyBuilt()
        graphs[cg.id] = ann.wrap(cg)
        return cg
    }

    override fun remove(id: GraphId) {
        requireNotNull(graphs.remove(id))
        if (id.v == idGen.v - 1) {
            idGen = id
        }
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
        graphs[gid] = rootAnn.wrap(gb)

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
        val FRESH_ID = GraphId(-2)
        val FIRST_ID = GraphId(1)
        fun isValidId(graphId: GraphId): Boolean {
            return graphId.v >= FIRST_ID.v
        }
    }
}

class CopiedGraph(
    override val multiGraph: MultiGraph,
    override val name: String?,
    override val nodes: NodeMap,
    override val start: NodeId,
    override val end: NodeId,
    override val id: GraphId
) : Graph

// @JvmInline value class GraphId(val v: Int)
data class GraphId(val v: Int)

class GraphBuilder(private val multiGraphBuilder: MultiGraphBuilder, override val name: String?) : Graph {
    private var idGen = NodeIds.FIRST_ID_IN_GRAPH
    private fun nextId(): NodeId {
        val ret = idGen
        idGen = NodeId(idGen.v + 1)
        return ret
    }

    override val multiGraph: MultiGraph
        get() = multiGraphBuilder

    override val nodes: MutNodeMap = mutableMapOf()

    override val start: NodeId
    override val end: NodeId
    private val dead: NodeId

    override var id: GraphId = MultiGraphBuilder.FRESH_ID
        private set

    // Although nodes are mutable, we don't mutate value nodes during graph building.
    private val pureValueCache = mutableMapOf<ValueNodeEqWrapper, NodeId>()

    // A region or a fixed node (e.g. call)
    private var currentControlDep: NodeId? = null
    private var currentEffect: NodeId

    init {
        start = assignId(Nodes.start()).id
        end = assignId(Nodes.end()).id
        dead = assignId(Nodes.dead()).id
        currentEffect = assignId(Nodes.effect()).id

        get(currentEffect).populateInput(get(start), EdgeKind.Value)
    }

    private fun startRegion(nPreds: Int = 1, nPhis: Int = 0, kind: RegionKind = RegionKind.Basic): Node {
        // require(currentRegion == null)
        val region = Nodes.region(nPreds = nPreds, nPhis = nPhis, kind = kind)
        currentControlDep = assignId(region).id
        return region
    }

    private fun assertCurrentControlDep(): NodeId {
        return requireNotNull(currentControlDep)
    }

    private fun projectEffectFrom(node: Node): Node {
        val updatedEffect = assignId(Nodes.effect())
        updatedEffect.populateInput(node, EdgeKind.Value)
        currentEffect = updatedEffect.id
        return node
    }

    private fun threadControlFrom(node: Node): Node {
        require(node.opCode.isFixedWithNext)
        node.populateInput(get(assertCurrentControlDep()), EdgeKind.Control)
        currentControlDep = node.id
        return node
    }

    fun populateArgs(args: Collection<AnnS<String>>, freeVars: Collection<String>): EnvChain {
        var env: NodeEnv = persistentMapOf()

        val freeVarNodes = freeVars.mapIndexed { index, freeVar ->
            val extra = FreeVarOpExtra(freeVar, index)
            freeVar to Nodes.freeVar(extra)
        }

        val argNodes = args.mapIndexed { index, arg ->
            val extra = ArgumentOpExtra(arg.unwrap, index)
            arg.unwrap to Nodes.argument(extra)
        }

        env = env.putAll((freeVarNodes + argNodes).map { (name, node) ->
            assignId(node)
            node.populateInput(get(start), EdgeKind.Value)
            name to node.id
        })

        return EnvChain(env)
    }

    private fun doSeq(es: List<AnnExpr>, env: EnvChain): Node {
        // Evaluate and throw away result values for body[:-1]
        es.take(es.size - 1).forEach {
            doExpr(it, env)
        }
        return get(doExpr(es.last(), env))
    }

    fun doFunctionBody(graphId: GraphId, body: List<AnnExpr>, env: EnvChain) {
        require(id == MultiGraphBuilder.FRESH_ID)
        id = graphId

        startRegion().populateInput(get(start), EdgeKind.Control)

        val returnValue = doSeq(body, env)
        val exitRegion = get(assertCurrentControlDep())

        val returnNode = assignId(Nodes.ret())
        returnNode.populateInput(get(currentEffect), EdgeKind.Value)
        returnNode.populateInput(returnValue, EdgeKind.Value)
        returnNode.populateInput(exitRegion, EdgeKind.Control)

        get(end).populateInput(returnNode, EdgeKind.Control)
    }

    fun doExpr(annE: AnnExpr, env: EnvChain): NodeId {
        return when (val e = annE.unwrap) {
            is ExprVar.B -> {
                makeUniqueValueNode(Nodes.boolLit(e.value))
            }
            is ExprVar.I -> {
                makeUniqueValueNode(Nodes.intLit(e.value))
            }
            is ExprVar.Sym -> {
                makeSymbolLit(e.name)
            }
            is ExprVar.V -> env[e.name, annE.ann]
            is ExprOp.If -> {
                doIf(e, env)
            }
            is ExprOp.Let -> {
                doLet(e, annE.ann, env)
            }
            is ExprOp.Op -> {
                doOp(e, env)
            }
            is ExprLam.Ap -> {
                doAp(e, env)
            }
            is ExprLam.Lam -> {
                val (gid, freeVarNames) = multiGraphBuilder.buildLam(env, e, annE.ann)
                val freeVars = freeVarNames.map {
                    // This should never fail, as the checking was done earlier in buildLam.
                    env[it, annE.ann]
                }
                makeEffectfulValueNode(Nodes.lambdaLit(freeVars.size, gid), freeVars).id
            }
            is ExprImp.While -> {
                doWhile(e, env)
            }
            is ExprImp.Set -> {
                EocError.todo(annE.ann, "Not implemented: $e")
            }
        }
    }

    private fun doOp(e: ExprOp.Op, env: EnvChain): NodeId {
        val values = e.args.map { doExpr(it, env) }
        return when (e.op.unwrap) {
            PrimOp.FxAdd -> {
                makeUniqueValueNode(Nodes.fxAdd(), values)
            }
            PrimOp.FxSub -> {
                makeUniqueValueNode(Nodes.fxSub(), values)
            }
            PrimOp.FxLessThan -> {
                makeUniqueValueNode(Nodes.fxLessThan(), values)
            }
            PrimOp.BoxMk -> {
                val valueToBox = values.first()
                makeEffectfulValueNode(Nodes.boxLit(), listOf(valueToBox)).id
            }
            PrimOp.BoxGet -> {
                val boxValue = values.first()
                makeEffectfulValueNode(Nodes.boxGet(), listOf(boxValue)).id
            }
            PrimOp.BoxSet -> {
                val (boxValue, newValue) = values
                makeEffectfulValueNode(Nodes.boxSet(), listOf(boxValue, newValue)).id
            }
        }
    }

    private fun doAp(e: ExprLam.Ap, env: EnvChain): NodeId {
        val f = doExpr(e.f, env)
        val args = e.args.map { doExpr(it, env) }
        val callNode = makeEffectfulValueNode(Nodes.call(args.size), listOf(f) + args)
        return threadControlFrom(callNode).id
    }

    private fun doLet(
        e: ExprOp.Let,
        ann: SourceLoc,
        env: EnvChain,
    ): NodeId {
        val newEnv = when (e.kind) {
            LetKind.Basic -> {
                val newBindings = e.vs.zip(e.es).associateTo(mutableMapOf()) { (name, rhs) ->
                    val value = doExpr(rhs, env)
                    name.unwrap to value
                }.toPersistentMap()
                env.extend(newBindings)
            }
            LetKind.Seq -> {
                var newBindings: NodeEnv = persistentMapOf()
                // "Mutate" the current env on the go.
                e.vs.zip(e.es).forEach { (name, rhs) ->
                    val newEnv = env.extend(newBindings)
                    val value = doExpr(rhs, newEnv)
                    newBindings = newBindings.put(name.unwrap, value)
                }
                env.extend(newBindings)
            }
            LetKind.Rec -> {
                EocError.todo(ann, "letrec not yet implemented")
                /*
                        val newBindings = e.vs.associate {
                            val boxNode = makeBoxLit(makeSymbolLit("#letrec-hole"))
                            it.unwrap to boxNode
                        }.toPersistentMap()
                        val newEnv = env.extend(newBindings)
                        // Mutate the current env on the go.
                        e.vs.zip(e.es).forEach { (name, rhs) ->
                            val value = doExpr(rhs, newEnv)
                            name.unwrap to value
                        }
                         */
            }
        }
        return doSeq(e.body, newEnv).id
    }

    private fun makeCondJump(e: AnnExpr, env: EnvChain): Pair<Node, Node> {
        // Close out current region by condJump
        val condValue = doExpr(e, env)
        val condJump = assignId(Nodes.condJump())
        condJump.populateInput(get(condValue), EdgeKind.Value)
        condJump.populateInput(get(assertCurrentControlDep()), EdgeKind.Control)

        // Make projections
        val ifT = assignId(Nodes.ifT())
        val ifF = assignId(Nodes.ifF())
        ifT.populateInput(condJump, EdgeKind.Control)
        ifF.populateInput(condJump, EdgeKind.Control)

        return ifT to ifF
    }

    private fun doIf(e: ExprOp.If, env: EnvChain): NodeId {
        // Evaluate condValue, set up condJump
        val (ifT, ifF) = makeCondJump(e.cond, env)

        // Save the effect state before branching.
        val originalEffect = currentEffect

        // True branch
        startRegion().populateInput(ifT, EdgeKind.Control)
        val tValue = doExpr(e.ifT, env)
        val tValueRegion = assertCurrentControlDep()
        val tEffect = currentEffect
        val tJump = assignId(Nodes.jump())
        tJump.populateInput(get(tValueRegion), EdgeKind.Control)

        // Restore the effect state before branching.
        currentEffect = originalEffect

        // False branch
        startRegion().populateInput(ifF, EdgeKind.Control)
        val fValue = doExpr(e.ifF, env)
        val fValueRegion = assertCurrentControlDep()
        val fEffect = currentEffect
        val fJump = assignId(Nodes.jump())
        fJump.populateInput(get(fValueRegion), EdgeKind.Control)

        return joinControlFlow(tValue, tEffect, fValue, fEffect, tJump, fJump)
    }

    private fun doWhile(e: ExprImp.While, env: EnvChain): NodeId {
        // ... beforeLoop -> Jump -(effect phi)> condRegion
        // condRegion -> (...) -> CondJump -ifT> loopRegion -ifF> endRegion
        // loopRegion -> Jump -(effect phi)> condRegion
        // endRegion ...
        val effectFromBeforeLoop = currentEffect
        val jumpFromBeforeLoop = assignId(Nodes.jump())
        jumpFromBeforeLoop.populateInput(get(assertCurrentControlDep()), EdgeKind.Control)

        val condRegion = startRegion(nPreds = 2, nPhis = 1, kind = RegionKind.LoopHeader)
        condRegion.populateInput(jumpFromBeforeLoop, EdgeKind.Control)

        // Pessimistically make an effect phi -- we can try to eliminate it later.
        val effectPhi = assignId(Nodes.effectPhi(2))
        effectPhi.populateInput(condRegion, EdgeKind.Control)
        // Value inputs added later.
        currentEffect = effectPhi.id

        // Evaluating e.cond may involve additional regions.
        val (ifT, ifF) = makeCondJump(e.cond, env)
        var effectAfterCondJump = currentEffect

        val loopRegion = startRegion()
        loopRegion.populateInput(ifT, EdgeKind.Control)
        // Result of while is ignored
        doSeq(e.body, env)
        val effectFromLoopEnd = currentEffect
        val jumpFromLoopEnd = assignId(Nodes.jump())
        jumpFromLoopEnd.populateInput(get(assertCurrentControlDep()), EdgeKind.Control)
        condRegion.populateInput(jumpFromLoopEnd, EdgeKind.Control)

        // Try to eliminate redundant effect phis.
        // Hmm this is kind of complicated...
        if (effectPhi.id != effectFromLoopEnd) {
            // ^ effectPhi merges effectFromLoopEnd and effectFromBeforeLoop,
            // and effectFromLoopEnd comes from effectPhi. So if there's no effect in the loop,
            // effectFromLoopEnd will stay the same as effectPhi.
            effectPhi.populateInput(get(effectFromBeforeLoop), EdgeKind.Value)
            effectPhi.populateInput(get(effectFromLoopEnd), EdgeKind.Value)
        } else {
            effectPhi.becomeValueNode(get(effectFromBeforeLoop), this)
            // This implies that the cond node evaluation is also not effectful.
            require(effectAfterCondJump == effectPhi.id)
            effectAfterCondJump = effectFromBeforeLoop
            effectPhi.removeInput(get(effectPhi.singleControlInput), EdgeKind.Control)
        }

        val endRegion = startRegion()
        endRegion.populateInput(ifF, EdgeKind.Control)
        currentEffect = effectAfterCondJump
        return makeUniqueValueNode(Nodes.symbolLit("#undefined"))
    }

    private fun makeSymbolLit(name: String): NodeId {
        return makeUniqueValueNode(Nodes.symbolLit(name))
    }

    private fun joinControlFlow(
        tValue: NodeId,
        tEffect: NodeId,
        fValue: NodeId,
        fEffect: NodeId,
        tJump: Node,
        fJump: Node
    ): NodeId {
        val needPhi = tValue != fValue
        val needEffectPhi = tEffect != fEffect
        // Make a region as a join point
        // Both branches may be returning the same thing. In that case we don't need a phi.
        val joinRegion = startRegion(nPreds = 2, nPhis = needPhi.b2i + needEffectPhi.b2i, kind = RegionKind.Merge)
        joinRegion.populateInput(tJump, EdgeKind.Control)
        joinRegion.populateInput(fJump, EdgeKind.Control)
        if (needEffectPhi) {
            val effectPhi = assignId(Nodes.effectPhi(2))
            effectPhi.populateInput(joinRegion, EdgeKind.Control)
            effectPhi.populateInput(get(tEffect), EdgeKind.Value)
            effectPhi.populateInput(get(fEffect), EdgeKind.Value)
            currentEffect = effectPhi.id
        }
        return if (needPhi) {
            val phi = assignId(Nodes.phi(2))
            phi.populateInput(joinRegion, EdgeKind.Control)
            phi.populateInput(get(tValue), EdgeKind.Value)
            phi.populateInput(get(fValue), EdgeKind.Value)
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
    private fun makeUniqueValueNode(n: Node, valueInputs: List<NodeId> = emptyList()): NodeId {
        val rator = n.operator
        require(rator.op.isPure)
        val key = ValueNodeEqWrapper(rator.op, rator.extra, valueInputs)
        val cached = pureValueCache[key]
        return if (cached == null) {
            // Save to cache.
            pureValueCache[key] = assignId(n).id
            // Populate edges
            valueInputs.forEach {
                n.populateInput(get(it), EdgeKind.Value)
            }
            n.id
        } else {
            cached
        }
    }

    private fun makeEffectfulValueNode(n: Node, valueInputs: List<NodeId> = emptyList()): Node {
        assignId(n)
        n.populateInput(get(currentEffect), EdgeKind.Value)
        valueInputs.forEach {
            n.populateInput(get(it), EdgeKind.Value)
        }
        projectEffectFrom(n)
        return n
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

    // Use a map to keep track of copied node. This is usually used for merging two graphs.
    fun makeCopy(n: Node, idMap: MutableMap<NodeId, NodeId>, insert: Boolean = true): Node {
        val copy = n.deepCopyMapped {
            idMap.getOrPut(it, ::nextId)
        }
        if (insert) {
            nodes[copy.id] = copy
        }
        return copy
    }
}

private val Boolean.b2i: Int
    get() = if (this) 1 else 0