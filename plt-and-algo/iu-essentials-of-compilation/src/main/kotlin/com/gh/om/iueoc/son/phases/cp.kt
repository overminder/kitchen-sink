package com.gh.om.iueoc.son.phases

import com.gh.om.iueoc.indexOfSafe
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
import com.gh.om.iueoc.son.isPure
import com.gh.om.iueoc.son.isValueFixedWithNext
import com.gh.om.iueoc.son.removeEdges
import com.gh.om.iueoc.son.singleControlInput
import com.gh.om.iueoc.son.singleControlOutput
import com.gh.om.iueoc.son.singleValueInput

object ConstantPropagationPhase : Phase {
    override fun run(g: MutGraphRef): Boolean {
        return CpRunner(g.g).once()
    }
}

// Simple CP (value + control) + DCE (control). Pure value DCE in done in trim.
private class CpRunner(private val g: MutGraph) {
    // Dead nodes take precedence over other nodes
    private val deadNodes = mutableSetOf<NodeId>()
    private val workList = mutableSetOf<NodeId>()

    fun once(): Boolean {
        var changed = false

        workList += NodeTraversal.live(g).reachableNodeIds

        while (deadNodes.isNotEmpty() || workList.isNotEmpty()) {
            val nid = if (deadNodes.isNotEmpty()) {
                val nid = deadNodes.first()
                deadNodes.remove(nid)
                nid
            } else {
                val nid = workList.first()
                workList.remove(nid)
                nid
            }

            changed = trySimplify(g[nid]) || changed
        }

        return changed
    }

    fun trySimplify(n: Node): Boolean {
        if (n.opCode.isPure && n.opCode.isValueFixedWithNext && n.valueOutputs.isEmpty()) {
            simplifyPureValueWithControl(n)
            return true
        }

        return when (n.opCode) {
            OpCode.ScmFxAdd -> simpifyBinaryIntOp(n) { lhs, rhs ->
                Nodes.fxLit(lhs + rhs)
            } || simplifyAddReassoc(n)
            OpCode.ScmFxSub -> simpifyBinaryIntOp(n) { lhs, rhs ->
                Nodes.fxLit(lhs - rhs)
            }
            OpCode.ScmFxLessThan -> simpifyBinaryIntOp(n) { lhs, rhs ->
                Nodes.boolLit(lhs < rhs)
            }
            OpCode.CondJump -> simplifyCondJump(n)
            OpCode.Dead -> simplifyDead(n)
            else -> false
        }
    }

    /**
     * Globally reassociate the arith ops.
     * This is more efficient if it's applied to the whole arith tree... Otherwise it sounds really inefficient.
     * (Need to find a way to remove visited arith nodes from workList... Or shall we?)
     */
    private fun simplifyAddReassoc(n: Node): Boolean {
        // Need to also deal with other operators. Hmm.
        var constSum = 0
        var nConsts = 0
        val poss = mutableListOf<Node>()
        val negs = mutableListOf<Node>()
        fun go(n: Node, isNeg: Boolean) {
            when (val op = n.opCode) {
                OpCode.ScmFxAdd -> {
                    for (rand in n.valueInputs.map(g::get)) {
                        go(rand, isNeg)
                    }
                }
                OpCode.ScmFxSub -> {
                    val (lhs, rhs) = n.valueInputs.map(g::get)
                    go(lhs, isNeg)
                    go(rhs, !isNeg)
                }
                OpCode.ScmFxLit -> {
                    var value = GetOperatorExtra(n).asFxLit
                    if (isNeg) {
                        value = -value
                    }
                    constSum += value
                    nConsts += 1
                }
                else -> {
                    val out = if (isNeg) negs else poss
                    out += n
                }
            }
        }

        go(n, false)
        if (nConsts == 0) {
            // No changes.
            return false
        }

        var lhs = if (constSum != 0) {
            g.assignId(Nodes.fxLit(constSum))
        } else {
            null
        }
        lhs = poss.fold(lhs) { acc, rhs ->
            if (acc == null) {
                rhs
            } else {
                val add = g.assignId(Nodes.fxAdd())
                add.populateInput(acc, EdgeKind.Value)
                add.populateInput(rhs, EdgeKind.Value)
                add
            }
        }
        val posSum = lhs ?: g.assignId(Nodes.fxLit(0))
        val negSum = negs.fold(null) { acc: Node?, rhs ->
            if (acc == null) {
                rhs
            } else {
                val add = g.assignId(Nodes.fxAdd())
                add.populateInput(acc, EdgeKind.Value)
                add.populateInput(rhs, EdgeKind.Value)
                add
            }
        }
        val replacement = if (negSum == null) {
            posSum
        } else {
            val sub = g.assignId(Nodes.fxSub())
            sub.populateInput(posSum, EdgeKind.Value)
            sub.populateInput(negSum, EdgeKind.Value)
            sub
        }
        replaceWith(n, replacement)
        return true
    }

    /** If a control-threaded value node [n] has no value uses, kill it. */
    private fun simplifyPureValueWithControl(n: Node) {
        val next = g[n.singleControlOutput]
        val prev = g[n.singleControlInput]
        next.replaceInput(n, prev, EdgeKind.Control)
        n.removeInput(prev, EdgeKind.Control)
    }

    private fun simpifyBinaryIntOp(n: Node, binOp: (Int, Int) -> Node): Boolean {
        val vins = n.valueInputs.map(g::get)
        if (!vins.all { it.opCode == OpCode.ScmFxLit }) {
            return false
        }
        val (lhs, rhs) = vins.map { GetOperatorExtra(it).asFxLit }
        val replacement = g.assignId(binOp(lhs, rhs))
        replaceWith(n, replacement)
        return true
    }

    private fun replaceWith(orig: Node, replacement: Node) {
        orig.becomeValueNode(replacement, g)
        // Note that n's inputs are not yet cut away -- we have to manually do that.
        // n has no edges now, and becomes invalid. Hopefully it won't be seen again...
        orig.removeEdges(g, EdgeDirection.Input, EdgeKind.VALUE)
        // However n may still be in the worklist. Remove it so that we never see invalid nodes.
        workList -= orig.id
        workList += replacement.valueOutputs
    }

    private fun tryEvaluateAsBool(value: Node): Boolean? {
        return when (value.opCode) {
            OpCode.ScmBoolLit -> GetOperatorExtra(value).asBoolLit
            OpCode.ScmBoxLit,
            OpCode.ScmLambdaLit,
            OpCode.ScmFxLit,
            OpCode.ScmSymbolLit,
            OpCode.ScmFxAdd,
            OpCode.ScmFxSub,
            OpCode.ScmBoxSet,
            -> true
            else -> null
        }
    }

    // Transform:
    //   (boolLit, c0) -> CondJump -> ifT -> c1, ifF -> c2
    // Into
    //   c0 -> c1, dead -> c2
    // Removing CondJump, ifT, ifF entirely. The dead node can be trimmed away later.
    private fun simplifyCondJump(condJump: Node): Boolean {
        val cond = tryEvaluateAsBool(g[condJump.singleValueInput]) ?: return false
        val opCodeToKill = if (cond) {
            OpCode.ScmIfF
        } else {
            OpCode.ScmIfT
        }
        val branches = condJump.controlOutputs.map(g::get)
        for (b in branches) {
            if (b.opCode == opCodeToKill) {
                val dead = g.assignId(Nodes.dead())
                b.becomeControlNode(dead, g)
                deadNodes += dead.id
            } else {
                b.becomeControlNode(g[condJump.singleControlInput], g)
            }
        }
        condJump.removeEdges(g, EdgeDirection.Input)
        return true
    }

    private fun simplifyDead(dead: Node): Boolean {
        var changed = false
        require(dead.opCode == OpCode.Dead)
        for (co in dead.controlOutputs.map(g::get)) {
            changed = when {
                co.opCode == OpCode.Merge -> {
                    simplifyPartiallyDeadMerge(co, dead)
                    true
                }
                co.opCode == OpCode.CondJump -> {
                    simplifyDeadCondJump(co, dead)
                    true
                }
                co.opCode == OpCode.ScmIfT || co.opCode == OpCode.ScmIfF -> {
                    simplifySingleControlThreadedDeadNode(co, dead)
                    true
                }
                co.opCode.isValueFixedWithNext -> {
                    simplifySingleControlThreadedDeadNode(co, dead)
                    true
                }
                else -> {
                    error("Unhandled node with dead input: $co")
                }
            }
        }
        require(dead.valueOutputs.isEmpty())
        return changed
    }

    // Transform:
    //   (c0_dead, value) -> condJump -> (ifT, ifF)
    // Into:
    //   c0_dead -> (ifT, ifF)
    private fun simplifyDeadCondJump(condJump: Node, dead: Node) {
        for (co in condJump.controlOutputs.map(g::get)) {
            co.replaceInput(condJump, dead, EdgeKind.Control)
        }
        condJump.removeEdges(g, EdgeDirection.Input)
        workList -= condJump.id
        deadNodes += dead.id
    }

    // Transform:
    //   c0_dead -> node -> c1
    // Into:
    //   c0_dead -> c1
    private fun simplifySingleControlThreadedDeadNode(node: Node, dead: Node) {
        val nextNode = g[node.singleControlOutput]
        nextNode.replaceInput(node, dead, EdgeKind.Control)
        node.removeInput(dead, EdgeKind.Control)
        deadNodes += dead.id
    }

    // Transform:
    //   (c0, c1_dead) -> Merge -> (phis, c2)
    //   (v0, v1) -> phi -> (phi uses...)
    // Into:
    //   c0 -> c2
    //   v0 -> (phi uses...)
    private fun simplifyPartiallyDeadMerge(merge: Node, deadIncomingBranch: Node) {
        // Not necessarily true though
        require(merge.controlInputs.size == 2)

        val deadBranchIx = merge.controlInputs.indexOfSafe(deadIncomingBranch.id)!!
        val liveBranchIx = 1 - deadBranchIx
        val cins = merge.controlInputs.map(g::get)
        val cos = merge.controlOutputs.map(g::get)
        val phis = cos.filter { it.opCode == OpCode.Phi }
        val c2 = cos.first { it.opCode != OpCode.Phi }

        for (phi in phis) {
            val liveValue = phi.valueInputs[liveBranchIx]
            // Sanity check. Can a loop header have such dead incoming branch? Possible if it's an infinite loop?
            require(liveValue != phi.id)
            phi.becomeValueNode(g[liveValue], g)
            // XXX Phi's values inputs still have transitive dead uses. How should we deal with them?
            phi.removeEdges(g, EdgeDirection.Input)
            workList -= phi.id
        }

        c2.replaceInput(merge, cins[liveBranchIx], EdgeKind.Control)
        merge.removeEdges(g, EdgeDirection.Input)
        workList -= merge.id
    }
}