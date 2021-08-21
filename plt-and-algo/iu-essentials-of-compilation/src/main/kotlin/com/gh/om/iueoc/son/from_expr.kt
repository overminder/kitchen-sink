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
import kotlinx.collections.immutable.PersistentMap
import kotlinx.collections.immutable.persistentMapOf
import kotlinx.collections.immutable.putAll
import kotlinx.collections.immutable.toPersistentMap

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

class ExprToGraphCollection(private val graphs: MutGraphCollection) {
    /**
     * @param outerEnv Flattened free vars from the outer lexical scope.
     * @param name The function name
     */
    fun build(
        outerEnv: EnvChain?,
        name: String?,
        args: List<AnnS<String>>,
        body: List<AnnExpr>,
        rootAnn: SourceLoc,
        verify: Boolean = true
    ): ExprToGraph {
        val outerFlatEnv = outerEnv?.let {
            outerEnv.flatten() - args.map { it.unwrap }
        }.orEmpty()

        val g = graphs.add { MutGraph.make(it, name, rootAnn, graphs) }
        val gb = ExprToGraph(g)

        val env = gb.populateArgs(args, outerFlatEnv.keys)
        gb.doFunctionBody(body, env)

        // XXX sounds hacky to set signature here. But freeVarCount is not known until the uses are all analyzed.
        g.populateSignature(argCount = args.size, freeVarCount = gb.usedFreeVars!!.size)

        if (verify) {
            GraphVerifier(g).verifyFullyBuilt()
        }
        return gb
    }

    /**
     * @param outerEnv The env to be enclosed by the lambda
     */
    fun buildLam(outerEnv: EnvChain, lam: ExprLam.Lam, ann: SourceLoc): Pair<GraphId, List<String>> {
        val gb = build(outerEnv, lam.name, lam.args, lam.body, ann)
        return gb.graph.id to requireNotNull(gb.usedFreeVars)
    }
}

class ExprToGraph(val graph: MutGraph) {
    var usedFreeVars: List<String>? = null
        private set
    private val state = GraphBuilderState(graph)

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
            graph.assignId(node)
            node.populateInput(graph[graph.start], EdgeKind.Value)
            name to node.id
        })

        return EnvChain(env)
    }

    private fun doSeq(es: List<AnnExpr>, env: EnvChain): Node {
        // Evaluate and throw away result values for body[:-1]
        es.take(es.size - 1).forEach {
            doExpr(it, env)
        }
        return graph[doExpr(es.last(), env)]
    }

    fun doFunctionBody(body: List<AnnExpr>, env: EnvChain) {
        val returnValue = doSeq(body, env)
        val exitRegion = state.assertCurrentControlDep()

        val returnNode = graph.assignId(Nodes.ret())
        returnNode.populateInput(returnValue, EdgeKind.Value)
        returnNode.populateInput(exitRegion, EdgeKind.Control)

        graph[graph.end].populateInput(returnNode, EdgeKind.Control)

        usedFreeVars = compactFreeVars()
    }

    fun doExpr(annE: AnnExpr, env: EnvChain): NodeId {
        return when (val e = annE.unwrap) {
            is ExprVar.B -> {
                state.makeUniqueValueNode(Nodes.boolLit(e.value))
            }
            is ExprVar.I -> {
                state.makeUniqueValueNode(Nodes.fxLit(e.value))
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
                // TODO
                val (gid, freeVarNames) = ExprToGraphCollection(graph.owner).buildLam(env, e, annE.ann)
                val freeVars = freeVarNames.map {
                    // This should never fail, as the checking was done earlier in buildLam.
                    env[it, annE.ann]
                }
                state.makeEffectfulValueNode(Nodes.lambdaLit(freeVars.size, gid), freeVars).id
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
                state.makeUniqueValueNode(Nodes.fxAdd(), values)
            }
            PrimOp.FxSub -> {
                state.makeUniqueValueNode(Nodes.fxSub(), values)
            }
            PrimOp.FxLessThan -> {
                state.makeUniqueValueNode(Nodes.fxLessThan(), values)
            }
            PrimOp.BoxMk -> {
                val valueToBox = values.first()
                state.makeEffectfulValueNode(Nodes.boxLit(), listOf(valueToBox)).id
            }
            PrimOp.BoxGet -> {
                val boxValue = values.first()
                state.makeEffectfulValueNode(Nodes.boxGet(), listOf(boxValue)).id
            }
            PrimOp.BoxSet -> {
                val (boxValue, newValue) = values
                state.makeEffectfulValueNode(Nodes.boxSet(), listOf(boxValue, newValue)).id
            }
            PrimOp.Opaque -> {
                val r = graph.assignId(Nodes.opaqueValue())
                val value = graph[values.first()]
                r.populateInput(value, EdgeKind.Value)
                r.id
            }
        }
    }

    private fun doAp(e: ExprLam.Ap, env: EnvChain): NodeId {
        val f = doExpr(e.f, env)
        val args = e.args.map { doExpr(it, env) }
        val callNode = state.makeEffectfulValueNode(Nodes.call(args.size), listOf(f) + args)
        return callNode.id
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
        val condJump = graph.assignId(Nodes.condJump())
        condJump.populateInput(graph[condValue], EdgeKind.Value)
        condJump.populateInput(state.assertCurrentControlDep(), EdgeKind.Control)

        // Make projections
        val ifT = graph.assignId(Nodes.ifT())
        val ifF = graph.assignId(Nodes.ifF())
        ifT.populateInput(condJump, EdgeKind.Control)
        ifF.populateInput(condJump, EdgeKind.Control)

        return ifT to ifF
    }

    private fun doIf(e: ExprOp.If, env: EnvChain): NodeId {
        // Evaluate condValue, set up condJump
        val (ifT, ifF) = makeCondJump(e.cond, env)

        // True branch
        state.currentControlDep = ifT.id
        val tValue = doExpr(e.ifT, env)
        val tLastControl = state.assertCurrentControlDep()

        // False branch
        state.currentControlDep = ifF.id
        val fValue = doExpr(e.ifF, env)
        val fLastControl = state.assertCurrentControlDep()

        return state.joinControlFlow(tValue, fValue, tLastControl, fLastControl)
    }

    private fun doWhile(e: ExprImp.While, env: EnvChain): NodeId {
        // ... beforeLoop -> loopHeader
        // loopHeader -> (...) -> CondJump -ifT> loopBody -ifF> loopExit
        // loopBody -> (...) -backEdge> loopHeader
        // loopExit ...
        val jumpFromBeforeLoop = state.assertCurrentControlDep()

        val loopHeader = state.makeMergeNode(nPreds = 2, nPhis = 0, kind = RegionKind.LoopHeader)
        loopHeader.populateInput(jumpFromBeforeLoop, EdgeKind.Control)

        // Evaluating e.cond may involve additional regions.
        val (loopBody, loopExit) = makeCondJump(e.cond, env)

        state.currentControlDep = loopBody.id
        // Result of while is ignored
        doSeq(e.body, env)
        // Jump back to header
        loopHeader.populateInput(state.assertCurrentControlDep(), EdgeKind.Control)

        state.currentControlDep = loopExit.id
        return state.makeUniqueValueNode(Nodes.symbolLit("#undefined"))
    }

    private fun makeSymbolLit(name: String): NodeId {
        return state.makeUniqueValueNode(Nodes.symbolLit(name))
    }

    /**
     * Remove free vars that are not lexically referred to.
     */
    private fun compactFreeVars(): List<String> {
        val start = graph[graph.start]
        val (used, unused) = start.valueOutputs.map(graph::get).filter {
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
            it.removeInput(start, EdgeKind.Value)
            // it.replaceInput(start, graph[graph.dead], EdgeKind.Control)
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