package com.gh.om.iueoc.son

// Inline trivial calls: MkLambdaLit -> Call

class InlinePhase(private val reps: Int) : Phase {
    init {
        require(reps >= 1)
    }

    override fun run(g: MutGraph): Boolean {
        val runner = InlinePhaseRunner(g)
        var changed = false
        repeat(reps) {
            val changedThisTime = runner.once()
            if (!changedThisTime) {
                return@repeat
            }
            changed = true
        }
        return changed
    }
}

private class InlinePhaseRunner(private val cg: MutGraph) {
    private val gs = cg.owner

    // Returns true if there are changes.
    fun once(): Boolean {
        // 1. Traverse the graph to find MkLambdaLit -> Call
        val t = NodeTraversal.full(cg)
        val candidates = t.reachableNodes.mapNotNull { call ->
            asCallWithLambdaLitTarget(call)?.let { lambdaLit ->
                call to lambdaLit
            }
        }
        val first = candidates.firstOrNull() ?: return false

        val (call, lambdaLitEdge) = first
        // 2. Do inlining
        inline(call, lambdaLitEdge)
        return true
    }

    private fun inline(call: Node, lambdaLitEdge: Pair<Node, Int>) {
        val (lambdaLit, _) = lambdaLitEdge
        val graphId = GetOperatorExtra(lambdaLit).asLambdaLit

        // Transform:
        // - @g:
        //   + (e?, freeVars) -> <lambdaLit callee> -> e?
        //   + (e0, c0, <lambdaLit>, args) -> <call> -> (e1, c1)
        //   + <call> -> ...uses
        // - @callee: Start -> (e0, c0, args, freeVars) -> <callee-body...> -> (e_n, c_n, retVal) -> Return -> End
        //
        // Into:
        // - @g:
        //   + keep <lambdaLit>, but remove value out.
        //   + merge <callee-body> into <call>, replacing:
        //     1 e0@callee with e0@g
        //     2 args@callee with args@g
        //     3 freeVars@callee with freeVars@g
        //     4 c0@callee with c0@g
        //     5 call@g with retVal@callee
        //     6 e1@g with e_n@callee
        //     7 c1@g with c_n@callee
        // NOTE (graph rewrite order): Likely need to go from output to input, since output may refer to input but
        // not vice versa. If inputs are rewritten first, output may refer to stale refs.

        val g = collectCallSiteNodes(call, lambdaLit)
        val callee = collectAndInsertTargetNodes(graphId)

        val calleeHasEffect = callee.e0 != callee.en
        if (calleeHasEffect) {
            get(callee.e0).becomeValueNode(get(g.e0), cg) // 1
        } else {
            get(g.e1).replaceInput(call, get(g.e0), EdgeKind.Value)
        }
        // It's not trivial to replace Call: call's effect need to be killed, and var uses need to be replaced.
        // This needs to happen before replacing callee args/freeVars, as the retVal may be one of the args/freeVars.
        call.valueOutputs.filter {
            get(it).opCode != OpCode.Effect
        }.map(::get).forEach {
            it.replaceInput(call, get(callee.retVal), EdgeKind.Value)
        } // 5
        callee.args.forEach {
            val calleeArg = get(it)
            val extra = GetOperatorExtra(calleeArg).asArgument
            calleeArg.becomeValueNode(get(g.args[extra.index]), cg)
        } // 2
        callee.freeVars.forEach {
            val fv = get(it)
            val extra = GetOperatorExtra(fv).asFreeVar
            fv.becomeValueNode(get(g.freeVars[extra.index]), cg)
        } // 3
        val calleeHasControl = callee.c0 != callee.cn
        if (calleeHasControl) {
            get(callee.c0).becomeControlNode(get(g.c0), cg) // 4
        } else {
            get(g.c1).replaceInput(call, get(g.c0), EdgeKind.Control)
        }
        if (calleeHasEffect) {
            get(g.e1).replaceInput(call, get(callee.en), EdgeKind.Value) // 6
            // This is to prevent two effects chained together. Doing it here is fragile, and we should instead add
            // a trim/simplify pass to remove that.
            // val e1 = get(g.e1)
            // get(e1.singleValueOutput).replaceInput(e1, get(callee.en), EdgeKind.Value) // 6
        }
        if (calleeHasControl) {
            get(g.c1).replaceInput(call, get(callee.cn), EdgeKind.Control) // 7
        }

        // Clean up: remove call's inputs
        call.removeEdges(cg, EdgeDirection.Input)
    }

    private fun get(nodeId: NodeId, g: Graph = cg) = g[nodeId]

    private fun getOp(nodeId: NodeId, g: Graph = cg): OpCode {
        return g[nodeId].opCode
    }

    private fun collectCallSiteNodes(call: Node, lambdaLit: Node): CallSiteNodes {
        return CallSiteNodes(
            freeVars = lambdaLit.valueInputs.drop(1),
            e0 = call.valueInputs.first(),
            c0 = call.singleControlInput,
            args = call.valueInputs.drop(2),
            e1 = call.valueOutputs.first(),
            c1 = call.singleControlOutput,
        )
    }

    private fun collectAndInsertTargetNodes(graphId: GraphId): TargetNodes {
        val tg = gs[graphId]

        // Map nid@tg to nid@g
        // Copy all the nodes from target to call site
        val idMap = cg.copyFrom(NodeTraversal.full(tg).reachableNodes)

        val start = cg[idMap[tg.start]!!]
        val startVout = start.valueOutputs
        val end = cg[idMap[tg.end]!!]
        // XXX There might be more than one return.
        val retNode = cg[end.singleControlInput]
        val (en, retVal) = retNode.valueInputs

        val c0 = start.singleControlOutput
        val cn = retNode.singleControlInput
        val collected = TargetNodes(
            e0 = startVout.first { getOp(it, cg) == OpCode.Effect },
            c0 = c0,
            args = startVout.filter { getOp(it, cg) == OpCode.Argument },
            freeVars = startVout.filter { getOp(it, cg) == OpCode.FreeVar },
            en = en,
            cn = cn,
            retVal = retVal,
        )

        // Disconnect start and return.
        start.removeEdges(cg, EdgeDirection.Output)
        retNode.removeEdges(cg, EdgeDirection.Input)
        return collected
    }

    private class CallSiteNodes(
        val freeVars: List<NodeId>,
        val e0: NodeId,
        val c0: NodeId,
        val args: List<NodeId>,
        val e1: NodeId,
        val c1: NodeId,
    )

    private class TargetNodes(
        val e0: NodeId,
        val c0: NodeId,
        val args: List<NodeId>,
        val freeVars: List<NodeId>,
        val en: NodeId,
        val cn: NodeId,
        val retVal: NodeId,
    )

    private fun asCallWithLambdaLitTarget(n: Node): Pair<Node, Int>? {
        if (n.opCode != OpCode.Call) {
            return null
        }
        val ix = 1
        val target = cg[n.valueInputs[ix]]
        if (target.opCode != OpCode.ScmLambdaLit) {
            return null
        }
        return target to ix
    }
}
