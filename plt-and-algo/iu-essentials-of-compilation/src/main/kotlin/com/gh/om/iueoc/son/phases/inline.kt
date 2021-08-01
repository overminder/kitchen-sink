package com.gh.om.iueoc.son.phases

import com.gh.om.iueoc.son.EdgeDirection
import com.gh.om.iueoc.son.EdgeKind
import com.gh.om.iueoc.son.GetOperatorExtra
import com.gh.om.iueoc.son.Graph
import com.gh.om.iueoc.son.GraphId
import com.gh.om.iueoc.son.MutGraph
import com.gh.om.iueoc.son.MutGraphRef
import com.gh.om.iueoc.son.Node
import com.gh.om.iueoc.son.NodeId
import com.gh.om.iueoc.son.NodeTraversal
import com.gh.om.iueoc.son.OpCode
import com.gh.om.iueoc.son.get
import com.gh.om.iueoc.son.removeEdges
import com.gh.om.iueoc.son.singleControlInput
import com.gh.om.iueoc.son.singleControlOutput
import java.lang.RuntimeException

// Inline trivial calls: MkLambdaLit -> Call

object InlinePhase : Phase {
    override fun run(g: MutGraphRef): Boolean {
        return InlinePhaseRunner(g.g).once()
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
        //   + freeVars -> <lambdaLit callee>
        //   + (<lambdaLit>, args, c0) -> <call> -> (uses..., c1)
        // - @callee: Start -> (args, freeVars, c0) -> <callee-body...> -> (retVal, c_n) -> Return -> End
        //
        // Into:
        // - @g:
        //   + keep <lambdaLit>, but remove value out.
        //   + merge <callee-body> into <call>, replacing:
        //     1 args@callee with args@g
        //     2 freeVars@callee with freeVars@g
        //     3 c0@callee with c0@g
        //     4 call@g with retVal@callee
        //     5 c1@g with c_n@callee
        // NOTE (graph rewrite order): Likely need to go from output to input, since output may refer to input but
        // not vice versa. If inputs are rewritten first, output may refer to stale refs.

        val g = collectCallSiteNodes(call, lambdaLit)
        val callee = collectAndInsertTargetNodes(graphId)

        // It's not trivial to replace Call: call's effect need to be killed, and var uses need to be replaced.
        // This needs to happen before replacing callee args/freeVars, as the retVal may be one of the args/freeVars.
        call.valueOutputs.map(::get).forEach {
            it.replaceInput(call, get(callee.retVal), EdgeKind.Value)
        } // 4
        callee.args.forEach {
            val calleeArg = get(it)
            val extra = GetOperatorExtra(calleeArg).asArgument
            calleeArg.becomeValueNode(get(g.args[extra.index]), cg)
        } // 1
        callee.freeVars.forEach {
            val fv = get(it)
            val extra = GetOperatorExtra(fv).asFreeVar
            fv.becomeValueNode(get(g.freeVars[extra.index]), cg)
        } // 2
        val calleeHasControl = callee.c0 != callee.cn
        if (calleeHasControl) {
            val c0 = get(callee.c0)
            val c0Next = get(c0.singleControlOutput)
            c0Next.replaceInput(c0, get(g.c0), EdgeKind.Control)
            // get(callee.c0).becomeControlNode(get(g.c0), cg) // 3
        } else {
            get(g.c1).replaceInput(call, get(g.c0), EdgeKind.Control)
        }
        if (calleeHasControl) {
            get(g.c1).replaceInput(call, get(callee.cn), EdgeKind.Control) // 5
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
            freeVars = lambdaLit.valueInputs,
            c0 = call.singleControlInput,
            args = call.valueInputs.drop(1),
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
        val (retVal) = retNode.valueInputs

        val c0 = start.id
        val cn = retNode.singleControlInput
        val collected = TargetNodes(
            c0 = c0,
            args = startVout.filter { getOp(it, cg) == OpCode.Argument },
            freeVars = startVout.filter { getOp(it, cg) == OpCode.FreeVar },
            cn = cn,
            retVal = retVal,
        )

        // Disconnect start and return.
        // Still need start's controlOutput to properly rewrite control flow
        start.removeEdges(cg, EdgeDirection.Output, edgeKinds = EdgeKind.VALUE)
        retNode.removeEdges(cg, EdgeDirection.Input)
        return collected
    }

    private class CallSiteNodes(
        val freeVars: List<NodeId>,
        val c0: NodeId,
        val args: List<NodeId>,
        val c1: NodeId,
    )

    private class TargetNodes(
        val c0: NodeId,
        val args: List<NodeId>,
        val freeVars: List<NodeId>,
        val cn: NodeId,
        val retVal: NodeId,
    )

    private fun asCallWithLambdaLitTarget(n: Node): Pair<Node, Int>? {
        if (n.opCode != OpCode.Call) {
            return null
        }
        val ix = 0
        val target = cg[n.valueInputs[ix]]
        if (target.opCode != OpCode.ScmLambdaLit) {
            return null
        }
        return target to ix
    }
}
