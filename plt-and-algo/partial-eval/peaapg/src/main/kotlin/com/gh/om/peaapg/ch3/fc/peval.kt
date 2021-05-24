package com.gh.om.peaapg.ch3.fc

// Let's write a partial evaluator (specializer, or "mix" in PEaAPG) in the host langauge first.

abstract class Division {
    abstract fun isStatic(v: String): Boolean
}

fun Division.isStatic(v: Expr): Boolean {
    // Could also const fold before this, to turn (x * 0) into 0
    return when (v) {
        is Expr.BOp -> isStatic(v.lhs) && isStatic(v.rhs)
        is Expr.I -> true
        is Expr.MkList -> v.args.all(::isStatic)
        is Expr.Symbol -> true
        is Expr.UOp -> isStatic(v.arg)
        is Expr.Var -> isStatic(v.name)
    }
}

// Invariant: Value is immutable
typealias ProgramState = Pair<Label, Store>

fun mix(program: Program, division: Division, initialStore: Store, maxSteps: Int? = null): Program {
    // Map to a unique such that Label-unique is unique.
    val pending = mutableMapOf<ProgramState, Int>()
    val marked = mutableMapOf<ProgramState, Int>()
    val uniqueGen = UniqueGen<Label>()

    val initialState = program.bbs.first().label to initialStore
    maybeAddNewProgramState(uniqueGen, pending, marked, initialState)

    // Note that in the original mix program, both pending and marked are vars containing persistent data structures.
    // This way they can be partial evaluated.
    val residualBBs = mutableListOf<BB>()

    var remainingSteps = maxSteps
    while (pending.isNotEmpty() && (remainingSteps == null || remainingSteps > 0)) {
        val (task, labelId) = pending.takeAndRemoveFirst()
        marked[task] = labelId
        val (pp, vs) = task
        val bb = lookup(program, pp)

        // Might be updated by the block body
        val mvs = vs.toMutableMap()

        // This is also a var in the original mix
        val generatedCode = mutableListOf<Assign>()
        val jump = mixBB(bb, program, division, pending, marked, uniqueGen, mvs, generatedCode)

        residualBBs += BB(pp.specialize(labelId), generatedCode, jump)
        if (remainingSteps != null) {
            remainingSteps -= 1
        }
    }

    if (remainingSteps == 0) {
        println("WARNING: too many steps, early return from mix")
    }

    // Remove the given args.
    val residualArgs = program.args.toSet() - initialStore.keys
    return Program(residualArgs.toList(), residualBBs)
}

private tailrec fun mixBB(
    bb: BB,
    program: Program,
    division: Division,
    pending: MutableMap<ProgramState, Int>,
    marked: MutableMap<ProgramState, Int>,
    uniqueGen: UniqueGen<Label>,
    mvs: MutableStore,
    generatedCode: MutableList<Assign>
): Jump {
    for (assign in bb.body) {
        if (division.isStatic(assign.name)) {
            // When X is a static var, X := expr implies that expr only depends on static vars
            mvs[assign.name] = assign.expr.eval(mvs)
        } else {
            val rexpr = reduce(assign.expr, mvs)
            // Otherwise generate residual program
            generatedCode += assign.copy(expr = rexpr)
        }
    }

    val nextLabel = when (val jump = bb.last) {
        // Compression happens
        is Jump.Goto -> jump.label
        is Jump.If -> {
            if (division.isStatic(jump.cond)) {
                // Compression happens
                if (jump.cond.eval(mvs).isTrue) {
                    jump.ifTrue
                } else {
                    jump.ifFalse
                }
            } else {
                // Dynamic branch: create new program states.
                // Safe to insert mvs into sets as it will no longer be updated.
                val ifTrueState = jump.ifTrue to mvs
                val ifFalseState = jump.ifFalse to mvs
                val trueLabel = maybeAddNewProgramState(uniqueGen, pending, marked, ifTrueState)
                val falseLabel = maybeAddNewProgramState(uniqueGen, pending, marked, ifFalseState)
                return Jump.If(reduce(jump.cond, mvs), trueLabel, falseLabel)
            }
        }
        // Reduce can do as much as eval
        is Jump.Return -> return Jump.Return(reduce(jump.expr, mvs))
    }
    return mixBB(lookup(program, nextLabel), program, division, pending, marked, uniqueGen, mvs, generatedCode)
}

private fun Label.specialize(id: Int): Label {
    return Label("${name}_s$id")
}

private fun maybeAddNewProgramState(
    uniqueGen: UniqueGen<Label>,
    pending: MutableMap<ProgramState, Int>,
    marked: MutableMap<ProgramState, Int>,
    state: ProgramState,
): Label {
    val known = marked[state] ?: pending[state]
    if (known != null) {
        return state.first.specialize(known)
    }

    // Not in either
    val labelId = uniqueGen.next(state.first)
    pending[state] = labelId
    return state.first.specialize(labelId)
}

private class UniqueGen<K> {
    private val map = mutableMapOf<K, Int>()

    fun next(key: K): Int {
        val res = map.getOrDefault(key, 0) + 1
        map[key] = res
        return res
    }
}

// Partially evaluate given the known store
// Can be done in the same way as NbE
private fun reduce(expr: Expr, store: Store): Expr {
    return when (expr) {
        // Not doing any optimization here
        // Note: Such traversal can be simplified by SYB
        is Expr.BOp -> expr.copy(lhs = reduce(expr.lhs, store), rhs = reduce(expr.rhs, store))
        is Expr.I -> expr
        is Expr.MkList -> Expr.MkList(expr.args.map { reduce(it, store) })
        is Expr.Symbol -> expr
        is Expr.UOp -> expr.copy(arg = reduce(expr.arg, store))
        is Expr.Var -> {
            val value = store[expr.name]
            value?.readBack() ?: expr
        }
    }
}

// Convert a value back to code.
private fun Value.readBack(): Expr = when (this) {
    is Value.Cons -> Expr.BOp(BinaryRator.Cons, head.readBack(), tail.readBack())
    is Value.I -> Expr.I(value)
    Value.Nil -> Expr.MkList(emptyList())
    is Value.Symbol -> Expr.Symbol(name)
}

private fun lookup(program: Program, label: Label): BB {
    return requireNotNull(program.bbs.find { it.label == label }) {
        "Label $label not found"
    }
}

private fun <K, V> MutableMap<K, V>.takeAndRemoveFirst(): Pair<K, V> {
    val (key, value) = entries.first()
    remove(key)
    return key to value
}
