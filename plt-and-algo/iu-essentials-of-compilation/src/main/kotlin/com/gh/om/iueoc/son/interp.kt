package com.gh.om.iueoc.son

import com.gh.om.iueoc.EocError
import com.gh.om.iueoc.ExprOp
import com.gh.om.iueoc.PrimOp
import com.gh.om.iueoc.Tr
import com.gh.om.iueoc.Trampoline
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
            OpCode.Phi -> {
                requireNotNull(env[nid])
            }
            OpCode.IntLit -> {
                // Hmm ideally we want type safety on operator
                val value = n.operator.parameter as Int
                Value.I(value)
            }
            OpCode.IntAdd -> {
                binaryIntOp(op, n.valueInputs.map(::goValue)) { x, y ->
                    Value.I(x + y)
                }
            }
            OpCode.IntLessThan -> {
                binaryIntOp(op, n.valueInputs.map(::goValue)) { x, y ->
                    Value.B(x < y)
                }
            }
            else -> error("Not a value node: $n")
        }
    }

    tailrec fun goControl(nid: NodeId): Value {
        val n = get(nid)
        return when (n.operator.op) {
            OpCode.Start -> {
                goControl(n.singleControlOutput)
            }
            OpCode.Region -> {
                goControl(n.singleControlOutput)
            }
            OpCode.End -> {
                error("Not reachable")
            }
            OpCode.Return -> {
                goValue(n.singleValueInput)
            }
            OpCode.CondJump -> {
                val couts = n.controlOutputs.map(::get)
                val nextNode = if (goValue(n.singleValueInput).asBoolean) {
                    couts.find { it.operator.op == OpCode.IfT }
                } else {
                    couts.find { it.operator.op == OpCode.IfF }
                }
                requireNotNull(nextNode)

                // Before the jump, resolve phi in jump target.
                // The phis have control input from thisRegion.
                val thisRegion = n.singleControlInput

                val targetRegion = get(nextNode.singleControlOutput)
                val phisInTarget = targetRegion.controlOutputs.map(::get).filter {
                    it.operator.op == OpCode.Phi
                }
                // Find the {control,value}inputIx to choose the correct input value in the phis
                val inputIx = targetRegion.controlInputs.indexOf(thisRegion).also {
                    require(it != -1)
                }
                // Evaluate in parallel
                val evaluated = phisInTarget.map {
                    val vi = it.valueInputs[inputIx]
                    vi to goValue(vi)
                }
                env += evaluated

                // Jump
                goControl(nextNode.singleControlOutput)
            }
            OpCode.Phi,
            OpCode.IntLit,
            OpCode.IntAdd,
            OpCode.IntLessThan -> {
                error("Not a control node: $n")
            }
            OpCode.IfT,
            OpCode.IfF -> {
                error("Should be handled by CondJump ")
            }
        }
    }

    return goControl(nid)
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