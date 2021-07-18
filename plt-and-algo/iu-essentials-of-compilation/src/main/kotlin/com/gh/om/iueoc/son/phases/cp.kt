package com.gh.om.iueoc.son.phases

import com.gh.om.iueoc.son.EdgeDirection
import com.gh.om.iueoc.son.EdgeKind
import com.gh.om.iueoc.son.GetOperatorExtra
import com.gh.om.iueoc.son.MutGraph
import com.gh.om.iueoc.son.MutGraphRef
import com.gh.om.iueoc.son.Node
import com.gh.om.iueoc.son.NodeId
import com.gh.om.iueoc.son.NodeTraversal
import com.gh.om.iueoc.son.Nodes
import com.gh.om.iueoc.son.OpCode
import com.gh.om.iueoc.son.get
import com.gh.om.iueoc.son.removeEdges
import com.gh.om.iueoc.son.singleControlOutput
import com.gh.om.iueoc.son.singleValueInput

object ConstantPropagationPhase : Phase {
    override fun run(g: MutGraphRef): Boolean {
        return CpRunner(g.g).once()
    }
}

private class CpRunner(private val g: MutGraph) {
    private val workList = mutableSetOf<NodeId>()

    fun once(): Boolean {
        var changed = false

        workList += NodeTraversal.live(g).reachableNodeIds

        while (workList.isNotEmpty()) {
            val nid = workList.first()
            workList.remove(nid)

            changed = trySimplify(g[nid]) || changed
        }

        return changed
    }

    fun trySimplify(n: Node): Boolean {
        return when (n.opCode) {
            OpCode.ScmFxAdd -> simpifyBinaryIntOp(n) { lhs, rhs -> Nodes.intLit(lhs + rhs) }
            OpCode.ScmFxSub -> simpifyBinaryIntOp(n) { lhs, rhs -> Nodes.intLit(lhs - rhs) }
            OpCode.ScmFxLessThan -> simpifyBinaryIntOp(n) { lhs, rhs -> Nodes.boolLit(lhs < rhs) }
            // OpCode.CondJump -> simplifyCondJump(n)
            else -> false
        }
    }

    private fun simpifyBinaryIntOp(n: Node, binOp: (Int, Int) -> Node): Boolean {
        val vins = n.valueInputs.map(g::get)
        if (!vins.all { it.opCode == OpCode.ScmFxLit }) {
            return false
        }
        val (lhs, rhs) = vins.map { GetOperatorExtra(it).asFxLit }
        val replacement = g.assignId(binOp(lhs, rhs))
        n.becomeValueNode(replacement, g)
        // Note that n's inputs are not yet cut away -- we have to manually do that.
        // n has no edges now, and becomes invalid. Hopefully it won't be seen again...
        n.removeEdges(g, EdgeDirection.Input, EdgeKind.VALUE)
        // However n may still be in the worklist. Remove it so that we never see invalid nodes.
        workList -= n.id
        workList += replacement.valueOutputs
        return true
    }

    private fun simplifyCondJump(n: Node): Boolean {
        val condValueNode = g[n.singleValueInput]
        if (condValueNode.opCode != OpCode.ScmBoolLit) {
            return false
        }

        val cond = GetOperatorExtra(condValueNode).asBoolLit
        val projectionToKill = if (cond) {
            OpCode.ScmIfT
        } else {
            OpCode.ScmIfF
        }
        val branch = n.controlOutputs.map(g::get).first {
            it.opCode == projectionToKill
        }
        // TODO: find the merge point, then kill everything between the condJump and the merge point.
        // Maybe first find the post dominator?
        val region = branch.singleControlOutput

        return true
    }
}