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

fun interp(g: Graph, env: Env = mutableMapOf()): Value {
    return Interp(g, env).start()
}

private class Interp(
    private val graph: Graph,
    // Maps phi nodes to values
    private val env: Env
) {
    private var evaluatedEffects = mutableSetOf<NodeId>()
    private var evaluatedEffectfulNodes = mutableMapOf<NodeId, Value>()

    fun start(): Value {
        val startingEffect = get(graph.start).valueOutputs.first {
            get(it).operator.op == OpCode.Effect
        }
        evaluatedEffects += startingEffect
        return goControl(graph.start)
    }

    fun get(id: NodeId) = graph[id]

    fun goEffect(n: Node) {
        val nid = n.id
        when (n.opCode) {
            OpCode.Effect -> {
                if (nid !in evaluatedEffects) {
                    goEffectfulValue(get(n.singleValueInput))
                }
            }
            OpCode.EffectPhi -> {
                // Assigned when entering a join region
                require(nid in evaluatedEffects)
            }
            else -> {
                error("${n.opCode}")
            }
        }
    }

    fun goEffectfulValue(n: Node): Value {
        val nid = n.id
        // Start is a special effectful value that only has effect output.
        require(n.opCode == OpCode.Start || n.opCode.isEffectfulValue)

        // If already evaluated: return that.
        evaluatedEffectfulNodes[nid]?.let {
            return it
        }

        // Invariant: effectful values all have first input as the effect.
        goEffect(get(n.valueInputs.first()))

        val values = n.valueInputs.drop(1).map(::goValue)
        val result = when (n.opCode) {
            OpCode.ScmLambdaLit -> {
                TODO()
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
                error("${n.operator}: Not an effectful node")
            }
        }
        val effectOut = n.valueOutputs.first()
        require(get(effectOut).opCode == OpCode.Effect)
        // Make sure it's only added once.
        require(evaluatedEffects.add(effectOut))
        require(evaluatedEffectfulNodes.put(n.id, result) == null)
        return result
    }

    fun goValue(nid: NodeId): Value {
        val n = get(nid)
        if (n.opCode.isEffectfulValue) {
            return goEffectfulValue(n)
        }
        return when (val op = n.operator.op) {
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
     * This does different things given the graph semantics:
     * - When everything is pure (no memory/io etc), everything is call-by-value: only need to evaluate
     * each phi, and put such mapping {phi: value} into env.
     * - When there are effectful nodes (memory write etc): Since the effectul operations aren't idempotent,
     * they need to be done in a call-by-need way. A change in phi and memory phi values need to
     * invalidate all dependent effectful values.
     */
    fun populatePhis(jump: Node, targetRegion: Node) {
        // The phis have control input from thisRegion.
        val thisRegion = jump.singleControlInput

        val phisInTarget = targetRegion.controlOutputs.map(::get).filter {
            it.opCode == OpCode.Phi
        }
        val effectPhi = targetRegion.controlOutputs.map(::get).firstOrNull {
            it.opCode == OpCode.EffectPhi
        }
        if (phisInTarget.isEmpty() && effectPhi == null) {
            return
        }
        // When there are phis:
        // Find the {control,value}inputIx to choose the correct input value in the phis
        val inputIx = targetRegion.controlInputs.indexOfFirst { jumpToTarget ->
            get(jumpToTarget).singleControlInput == thisRegion
        }
        require(inputIx != -1)

        // Evaluate in parallel
        val phiValues = phisInTarget.map { phi ->
            val vi = phi.valueInputs[inputIx]
            phi.id to goValue(vi)
        }
        effectPhi?.let { phi ->
            val vi = phi.valueInputs[inputIx]

            // Force the effect input.
            goEffect(get(vi))

            // 2. Invalidate things dominated by it.
            invalidateEffects(get(phi.singleValueOutput))
            evaluatedEffects += phi.id
        }
        // And write back value phis (effect is already written back)
        env += phiValues
    }

    private tailrec fun invalidateEffects(from: Node) {
        if (from.opCode.isEffectfulValue) {
            evaluatedEffectfulNodes.remove(from.id)
            invalidateEffects(get(from.valueOutputs.first()))
        } else if (from.opCode.isEffect) {
            when (from.opCode) {
                OpCode.EffectPhi -> {
                    // Done -- Don't invalidate across another phi, as the original phi doesn't strictly dominate that.
                }
                OpCode.Effect -> {
                    evaluatedEffects.remove(from.id)
                    val lastOutput = from.valueOutputs.last()
                    from.valueOutputs.take(from.valueOutputs.size - 1).forEach {
                        @Suppress("NON_TAIL_RECURSIVE_CALL")
                        invalidateEffects(get(it))
                    }
                    invalidateEffects(get(lastOutput))
                }
                else -> error("Not an effect: ${from.opCode}")
            }
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
                    get(co).opCode.isJump
                }
                goControl(requireNotNull(jumpNode))
            }
            OpCode.End -> {
                error("Not reachable")
            }
            OpCode.Return -> {
                val (effect, value) = n.valueInputs
                goEffect(get(effect))
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
                error("${n.operator}: not a control")
            }
        }
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