package com.gh.om.iueoc.son

import com.gh.om.iueoc.EocError
import com.gh.om.iueoc.Value
import com.gh.om.iueoc.asBoolean

typealias Env = MutableMap<NodeId, Value>

fun interp(nid: NodeId, nodes: NodeMap, env: Env = mutableMapOf()): Value {
    fun get(id: NodeId): Node {
        return requireNotNull(nodes[id]) {
            "NodeId $id not found"
        }
    }

    fun goValue(nid: NodeId): Value {
        val n = get(nid)
        return when (val op = n.operator.op) {
            OpCode.Memory -> {
                TODO()
            }
            OpCode.Phi,
            OpCode.MemoryPhi -> {
                requireNotNull(env[nid])
            }
            OpCode.ScmBoolLit -> {
                val value = n.operator.extra as Boolean
                Value.B(value)
            }
            OpCode.ScmSymbolLit -> {
                val value = n.operator.extra as String
                Value.Sym(value)
            }
            OpCode.ScmFxLit -> {
                // Hmm ideally we want type safety on operator
                val value = n.operator.extra as Int
                Value.I(value)
            }
            OpCode.ScmFxAdd -> {
                binaryIntOp(op, n.valueInputs.map(::goValue)) { x, y ->
                    Value.I(x + y)
                }
            }
            OpCode.ScmFxLessThan -> {
                binaryIntOp(op, n.valueInputs.map(::goValue)) { x, y ->
                    Value.B(x < y)
                }
            }
            else -> error("Not a value node: $n")
        }
    }

    /**
     * Before jumping a target region, resolve phis that come from the current region.
     */
    fun populatePhis(jump: Node, targetRegion: Node) {
        // The phis have control input from thisRegion.
        val thisRegion = jump.singleControlInput

        val phisInTarget = targetRegion.controlOutputs.map(::get).filter {
            it.operator.op == OpCode.Phi
        }
        if (phisInTarget.isNotEmpty()) {
            // When there are phis:
            // Find the {control,value}inputIx to choose the correct input value in the phis
            val inputIx = targetRegion.controlInputs.indexOfFirst { jumpToTarget ->
                get(jumpToTarget).singleControlInput == thisRegion
            }
            require(inputIx != -1)
            // Evaluate in parallel
            val evaluated = phisInTarget.map { phi ->
                val vi = phi.valueInputs[inputIx]
                phi.id to goValue(vi)
            }
            env += evaluated
        }
    }

    tailrec fun goControl(nid: NodeId): Value {
        val n = get(nid)
        return when (n.operator.op) {
            OpCode.Start -> {
                goControl(n.singleControlOutput)
            }
            OpCode.Region -> {
                val jumpNode = n.controlOutputs.find { co ->
                    get(co).operator.op != OpCode.Phi
                }
                goControl(requireNotNull(jumpNode))
            }
            OpCode.End -> {
                error("Not reachable")
            }
            OpCode.Return -> {
                val (memory, value) = n.valueInputs
                goValue(memory)
                goValue(value)
            }
            OpCode.CondJump -> {
                val couts = n.controlOutputs.map(::get)
                val coutOps = couts.map { it.operator }
                EocError.ensure(Operators.isSchemeIfProjections(coutOps)) { "Unimplemented condJump projections: $coutOps" }
                val nextNode = if (goValue(n.singleValueInput).asBoolean) {
                    couts.find { it.operator.op == OpCode.ScmIfT }
                } else {
                    couts.find { it.operator.op == OpCode.ScmIfF }
                }
                requireNotNull(nextNode)

                val targetRegion = nextNode.singleControlOutput
                populatePhis(n, get(targetRegion))

                // Jump
                goControl(targetRegion)
            }
            OpCode.Jump -> {
                val targetRegion = n.singleControlOutput
                populatePhis(n, get(targetRegion))
                goControl(targetRegion)
            }
            OpCode.ScmIfT,
            OpCode.ScmIfF -> {
                error("${n.operator}: should be handled by CondJump ")
            }
            else -> {
                error("${n.operator}: valueNode to be handled by goValue ")
            }
        }
    }

    return goControl(nid)
}

private fun populatePhis() {

}

private fun <R> binaryIntOp(e: OpCode, argValues: List<Value>, func: (Int, Int) -> R): R {
    val (lhsV, rhsV) = argValues
    EocError.ensure(lhsV is Value.I) {
        "$e takes int value, not $lhsV"
    }
    EocError.ensure(rhsV is Value.I) {
        "$e takes int value, not $rhsV"
    }
    return func(lhsV.value, rhsV.value)
}