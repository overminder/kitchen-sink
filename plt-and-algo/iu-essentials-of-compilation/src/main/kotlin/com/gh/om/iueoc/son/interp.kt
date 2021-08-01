package com.gh.om.iueoc.son

import com.gh.om.iueoc.EocError
import com.gh.om.iueoc.Value
import com.gh.om.iueoc.asBoolean

/*
sealed class Value {
    data class I(val value: Int) : Value()
    data class B(val value: Boolean) : Value()
    data class Sym(val name: String) : Value()
    data class Clo(val code: GraphId, val freeVars: List<Value>) : Value()
    data class Box(val ptr: HeapPtr) : Value()
}
@JvmInline
value class HeapPtr(val value: Int) {
    fun bump() = HeapPtr(value + 1)
}

class Heap(
    val store: PersistentMap<HeapPtr, Value> = persistentMapOf(),
    private val allocPtr: HeapPtr = HeapPtr(1)
) {

    private fun allocate(v: Value): Pair<HeapPtr, Heap> {
        val newPtr = allocPtr.bump()
        val newStore = store.put(newPtr, v)
        return newPtr to Heap(newStore, newPtr)
    }

    fun box(v: Value): Value.Box {
    }
}

 */

typealias Env = MutableMap<NodeId, Value>

fun interp(gs: GraphCollection, entry: GraphId, env: Env = mutableMapOf()): Value {
    return Interp(gs, entry, env, emptyList(), emptyList()).start()
}

private class Interp(
    private val gs: GraphCollection,
    gid: GraphId,
    // Maps phi nodes to values
    private val env: Env,
    private val args: List<Value>,
    private val freeVars: List<Value>,
) {
    private val graph = gs[gid]

    private val evaluatedEffectfulNodes = mutableMapOf<NodeId, Value>()

    fun start(): Value {
        return goControl(graph.start, null)
    }

    fun get(id: NodeId) = graph[id]

    fun goEffectfulValue(n: Node) {
        require(n.opCode.isValueFixedWithNext)

        val values = n.valueInputs.map(::goValue)
        val result = when (n.opCode) {
            OpCode.Call -> {
                val f = values.first() as Value.LamG
                val args = values.drop(1)
                interpCall(f.graphId, args, f.freeVars)
            }
            OpCode.ScmLambdaLit -> {
                val gid = n.operator.extra as GraphId
                Value.LamG(gid, values)
            }
            OpCode.ScmBoxLit -> {
                val toBox = values.first()
                Value.Box(toBox)
            }
            OpCode.ScmBoxGet -> {
                val box = values.first() as Value.Box
                box.value
            }
            OpCode.ScmBoxSet -> {
                val (box0, newValue) = values
                val box = box0 as Value.Box
                val oldValue = box.value
                box.value = newValue
                oldValue
            }
            else -> {
                error("${n.operator}: Not an effectful value node")
            }
        }
        evaluatedEffectfulNodes[n.id] = result
    }

    fun goValue(nid: NodeId): Value {
        val n = get(nid)
        if (n.opCode.isValueFixedWithNext) {
            return requireNotNull(evaluatedEffectfulNodes[nid]) {
                "$n is not yet evaluated?"
            }
        }
        return when (val op = n.operator.op) {
            OpCode.Argument -> {
                val extra = GetOperatorExtra(n).asArgument
                return args[extra.index]
            }
            OpCode.FreeVar -> {
                val extra = GetOperatorExtra(n).asFreeVar
                return freeVars[extra.index]
            }
            OpCode.Phi -> {
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
            OpCode.ScmFxSub -> {
                binaryIntOp(op, n.valueInputs.map(::goValue)) { x, y ->
                    Value.I(x - y)
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
     * Right when jumping, resolve phis that come from the current "basic block".
     * - V8 has two kinds of phis: value and effect, and the effectPhi needs to be done in a call-by-need way.
     * - Hotspot/Graal uses just the value phi, which is pure (all value nodes can be evaluated for multiple times)
     *   and can be done in a call-by-value way. Just need to evaluate all phis, and put such mapping {phi: value}
     *   back into the env.
     */
    fun tryPopulatePhi(jump: Node, targetRegion: Node) {
        // Only merge nodes have phis.
        if (targetRegion.opCode != OpCode.Merge) {
            return
        }
        // The phis have control input from jump.
        val phisInTarget = targetRegion.controlOutputs.map(::get).filter {
            it.opCode == OpCode.Phi
        }
        if (phisInTarget.isEmpty()) {
            return
        }
        // When there are phis:
        // Find the {control,value}inputIx to choose the correct input value in the phis
        val inputIx = targetRegion.controlInputs.indexOfFirst { it == jump.id }
        require(inputIx != -1)

        // Evaluate in parallel
        val phiValues = phisInTarget.map { phi ->
            val vi = phi.valueInputs[inputIx]
            phi.id to goValue(vi)
        }
        // XXX How should we invalidate the effectful nodes? Are they not visible?
        // And write back value phis
        env += phiValues
    }

    tailrec fun goControl(nid: NodeId, comingFrom: Node?): Value {
        val n = get(nid)
        if (comingFrom != null) {
            tryPopulatePhi(comingFrom, n)
        }

        if (n.opCode.isValueFixedWithNext) {
            goEffectfulValue(n)
            return goControl(n.singleControlOutput, comingFrom = n)
        }
        return when (n.operator.op) {
            OpCode.Start -> {
                goControl(n.singleControlOutput, comingFrom = n)
            }
            OpCode.Merge -> {
                val nextNode = n.controlOutputs.find { co ->
                    val op = get(co).opCode
                    op != OpCode.Phi
                }
                goControl(requireNotNull(nextNode), comingFrom = n)
            }
            OpCode.End -> {
                error("Not reachable")
            }
            OpCode.Return -> {
                val (value) = n.valueInputs
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

                // Jump
                goControl(nextNode.singleControlOutput, comingFrom = nextNode)
            }
            OpCode.ScmIfT,
            OpCode.ScmIfF -> {
                error("${n.operator}: should be handled by CondJump ")
            }
            OpCode.Call -> {
                goValue(nid)
                goControl(n.singleControlOutput, comingFrom = n)
            }
            else -> {
                error("${n.operator}: not a control")
            }
        }
    }

    private fun interpCall(target: GraphId, args: List<Value>, freeVars: List<Value>): Value {
        val tg = gs[target]
        // Sanity check
        val startVouts = tg[tg.start].valueOutputs
        val expectedArgCount = startVouts.count {
            val n = tg[it]
            n.opCode == OpCode.Argument
        }
        val expectedFreeVarCounts = startVouts.count {
            val n = tg[it]
            n.opCode == OpCode.FreeVar
        }
        EocError.ensure(args.size == expectedArgCount, tg.sourceLoc) {
            "Arg count mismatch: expecting $expectedArgCount, got ${args.size}"
        }
        EocError.ensure(freeVars.size == expectedFreeVarCounts, tg.sourceLoc) {
            "freeVar count mismatch: expecting $expectedFreeVarCounts, got ${freeVars.size}"
        }
        return Interp(gs, target, mutableMapOf(), args, freeVars).start()
    }
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