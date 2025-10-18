package com.gh.om.pl.cwai

/**
 * Represents a value in the interpreter runtime.
 */
sealed interface IValue : IValueOrCell {
    /**
     * An int value
     */
    data class IVInt(val value: Int) : IValue

    /**
     * A boolean value
     */
    data class IVBool(val value: Boolean) : IValue

    /**
     * A lambda with captured lexical [env].
     */
    data class IVClosure(
        val abs: Exp.EAbs,
        val env: IEnv,
    ) : IValue
}

class ICell(var value: IValue? = null) : IValueOrCell

sealed interface IValueOrCell

typealias IEnv = Map<String, IValueOrCell>

private fun errorAt(
    loc: SourceLoc,
    msg: String,
): Nothing {
    throw IllegalArgumentException("$msg at ${loc.fileName}:${loc.line}:${loc.column}")
}

private fun expectInt(
    v: IValue,
    loc: SourceLoc,
): Int =
    when (v) {
        is IValue.IVInt -> v.value
        else -> errorAt(
            loc,
            "expected integer value",
        )
    }

private fun expectBool(
    v: IValue,
    loc: SourceLoc,
): Boolean =
    when (v) {
        is IValue.IVBool -> v.value
        else -> errorAt(
            loc,
            "expected boolean value",
        )
    }

private fun applyPrim(
    op: PrimOp,
    args: List<IValue>,
    loc: SourceLoc,
): IValue {
    // Arity is enforced by Exp.fromSExp, but we guard anyway
    if (args.size != op.arity) errorAt(
        loc,
        "primitive '$op' expects ${op.arity} args, got ${args.size}",
    )
    return when (op) {
        PrimOp.INT_ADD -> {
            val a = expectInt(
                args[0],
                loc,
            )
            val b = expectInt(
                args[1],
                loc,
            )
            IValue.IVInt(a + b)
        }

        PrimOp.INT_SUB -> {
            val a = expectInt(
                args[0],
                loc,
            )
            val b = expectInt(
                args[1],
                loc,
            )
            IValue.IVInt(a - b)
        }

        PrimOp.INT_LT -> {
            val a = expectInt(
                args[0],
                loc,
            )
            val b = expectInt(
                args[1],
                loc,
            )
            IValue.IVBool(a < b)
        }
    }
}

tailrec fun eval(
    exp: Exp,
    env: IEnv,
): IValue {
    fun deref(
        v: IValueOrCell,
        loc: SourceLoc,
    ): IValue =
        when (v) {
            is ICell -> v.value ?: errorAt(
                loc,
                "uninitialized recursive binding",
            )

            is IValue -> v
        }
    return when (exp) {
        is Exp.EInt -> IValue.IVInt(exp.value)
        is Exp.EBool -> IValue.IVBool(exp.value)
        is Exp.ESym -> {
            val b = env[exp.name]
                ?: errorAt(
                    exp.sourceLoc,
                    "unbound variable '${exp.name}'",
                )
            deref(
                b,
                exp.sourceLoc,
            )
        }

        is Exp.EAbs -> IValue.IVClosure(
            exp,
            env,
        )

        is Exp.EApp -> {
            @Suppress("NON_TAIL_RECURSIVE_CALL")
            val fnV = eval(
                exp.callee,
                env,
            )

            @Suppress("NON_TAIL_RECURSIVE_CALL")
            val argVs = exp.args.map {
                eval(
                    it,
                    env,
                )
            }
            val clos = when (fnV) {
                is IValue.IVClosure -> fnV
                else -> errorAt(
                    exp.callee.sourceLoc,
                    "attempted to call a non-function value",
                )
            }
            val params = clos.abs.args
            if (params.size != argVs.size) {
                errorAt(
                    exp.sourceLoc,
                    "arity mismatch: expected ${params.size} args, got ${argVs.size}",
                )
            }
            val argEnv: IEnv = params.zip(argVs).associate { it.first to it.second }
            val newEnv: IEnv = clos.env + argEnv
            eval(
                clos.abs.body,
                newEnv,
            )
        }

        is Exp.EIf -> {
            @Suppress("NON_TAIL_RECURSIVE_CALL")
            val condV = eval(
                exp.condition,
                env,
            )
            val cond = expectBool(
                condV,
                exp.condition.sourceLoc,
            )
            if (cond) eval(
                exp.trueBranch,
                env,
            ) else eval(
                exp.falseBranch,
                env,
            )
        }

        is Exp.ELet -> {
            if (!exp.isRec) {
                // Non-recursive let: evaluate RHS in original env, then extend
                @Suppress("NON_TAIL_RECURSIVE_CALL")
                val evaluated = exp.bindings.map { (name, rhs) ->
                    name to eval(
                        rhs,
                        env,
                    ) as IValueOrCell
                }
                val newEnv = env + evaluated.toMap()
                eval(
                    exp.body,
                    newEnv,
                )
            } else {
                // letrec: allocate cells first, extend env, evaluate RHS under extended env, assign cells, then eval body
                val cellEnvEntries = exp.bindings.map { (name, _) -> name to ICell() }
                val recEnv: IEnv = env + cellEnvEntries.toMap()
                // evaluate each rhs under recEnv and assign into corresponding cell
                for ((bindingEntry, cellEntry) in exp.bindings.zip(cellEnvEntries)) {
                    @Suppress("NON_TAIL_RECURSIVE_CALL")
                    val v = eval(
                        bindingEntry.second,
                        recEnv,
                    )
                    val cell = cellEntry.second
                    cell.value = v
                }
                eval(
                    exp.body,
                    recEnv,
                )
            }
        }

        is Exp.EPrimOp -> {
            @Suppress("NON_TAIL_RECURSIVE_CALL")
            val argVs = exp.args.map {
                eval(
                    it,
                    env,
                )
            }
            applyPrim(
                exp.op,
                argVs,
                exp.sourceLoc,
            )
        }
    }
}
