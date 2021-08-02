package com.gh.om.iueoc.son

enum class OpCode(val klass: OpCodeClass) {
    // Start node is the start of the graph
    // o(C:entryRegion, V:Argument ** |args|, V:FreeVar ** |upvals|)
    Start(OpCodeClass.Anchor),

    // End node is the end of the graph
    // i(C): One (or more) control input (from return)
    End(OpCodeClass.Anchor),

    // A join point for multiple incoming blocks (merge node in v8/graal)
    // i(C:jumpOrStart ** |preds|): n predecessors, can be jump or start
    // o(C:jump; C:phi ** |preds|): 1 jump node + n phis.
    // Each phi's value input corresponds to the control input on the same index in this region.
    Merge(OpCodeClass.Anchor),

    // Jump nodes mark the end of a block
    // i(V:retVal, C:prev), o(C:end)
    Return(OpCodeClass.Jump),

    // i(V:cond, C:currentRegion), o(C:ifT, C:ifF): 2 projection outputs
    CondJump(OpCodeClass.Jump),

    // io(C): Jump from region to region
    // We don't need a specific node for jump. Any node with next can do. Though having a jump makes the interpreter's
    // job easier -- there's always an end-of-block node so that phis can be detected and populated before the jump.
    // Jump(OpCodeClass.Jump),

    // Projection nodes
    // Control projections
    // i(C:condJump), o(C:nextRegion)
    // Scm-prefixed to check for not #f and #f.
    ScmIfT(OpCodeClass.Projection),
    ScmIfF(OpCodeClass.Projection),

    // Value projections
    // Function argument. i(V): start (should actually be control); p(ArgumentOpExtra): name and nth argument
    Argument(OpCodeClass.Projection),

    // Closure lifted free var (upvalue). i(V): start; p(FreeVarOpExtra): name and nth free var
    FreeVar(OpCodeClass.Projection),

    // Value nodes
    // Phi takes a single control input: a Merge node (just like phis appearing in a basic block's header).
    // i(C:merge; V ** n:values to choose from). Each value input corresponds to the merge's control input on the
    // same index.
    Phi(OpCodeClass.Phi),

    // i(V:target, V:args, C:prev) o(V:result, C:next)
    // In v8, call nodes are associated with lot of complicated information in v8.
    // And they may need control in/out as well.
    Call(OpCodeClass.FixedValue),

    // Literals
    ScmBoolLit(OpCodeClass.Value),

    // All the memory-related nodes have C in (previous control) and C out (next control)
    // i(V:toBox, C:prev), o(C:next)
    ScmBoxLit(OpCodeClass.FixedValue),
    ScmFxLit(OpCodeClass.Value),

    // i(V:freeVar ** |freeVars|, C:prev), o(C:next)
    ScmLambdaLit(OpCodeClass.FixedValue),
    ScmSymbolLit(OpCodeClass.Value),

    // Box operations
    // i(V:box, C:prev), o(C:next)
    ScmBoxGet(OpCodeClass.FixedValue),

    // i(V:box, V:newValue, C:prev), o(C:next)
    ScmBoxSet(OpCodeClass.FixedValue),

    // Int operations
    ScmFxAdd(OpCodeClass.Value),
    ScmFxSub(OpCodeClass.Value),
    ScmFxLessThan(OpCodeClass.Value),

    // i(V) -- Mark a value as opaque so that optimizations won't go through.
    OpaqueValue(OpCodeClass.Value),

    // A special marker operator, provides a dead value that should be removed from the graph.
    Dead(OpCodeClass.Misc),
}

// Need to figure out a better way to classify opcodes.
enum class OpCodeClass {
    // Start/End/Region
    Anchor,

    // End of basic blocks
    Jump,
    Projection,
    Phi,
    Value,

    // Fixed as in fixed in the control chain.
    FixedValue,

    // Dead etc
    Misc,
}

val OpCode.isPure: Boolean
    get() = when (this) {
        OpCode.ScmBoolLit,
        OpCode.ScmFxLit,
        OpCode.ScmSymbolLit,
        OpCode.ScmLambdaLit,
        OpCode.ScmBoxLit,

        OpCode.ScmFxAdd,
        OpCode.ScmFxSub,
        OpCode.ScmFxLessThan -> true
        else -> false
    }

val OpCode.isControlStructure: Boolean
    get() = when (this) {
        OpCode.Start,
        OpCode.Merge,
        OpCode.ScmIfT,
        OpCode.ScmIfF,
        OpCode.CondJump,
        OpCode.Return -> true
        else -> false
    }

val OpCode.hasControlInput: Boolean
    get() = (this != OpCode.Start && isControlStructure) || isValueFixedWithNext ||
        this == OpCode.Phi || this == OpCode.End

val OpCode.hasControlOutput: Boolean
    get() = isControlStructure || isValueFixedWithNext

// FixedWithNext value nodes <-> effectful.
val OpCode.isValueFixedWithNext: Boolean
    get() = when (this) {
        OpCode.Call,

        OpCode.ScmBoxLit,
        OpCode.ScmBoxSet,
        OpCode.ScmBoxGet,

        OpCode.ScmLambdaLit -> true
        else -> false
    }

val OpCode.isValue: Boolean
    get() = when (this) {
        OpCode.Argument,
        OpCode.FreeVar,
        OpCode.Phi,
        OpCode.Call,
        OpCode.ScmBoolLit,
        OpCode.ScmFxLit,
        OpCode.ScmLambdaLit,
        OpCode.ScmSymbolLit,
        OpCode.ScmFxAdd,
        OpCode.ScmFxSub,
        OpCode.ScmFxLessThan,
        OpCode.ScmBoxLit,
        OpCode.ScmBoxGet,
        OpCode.ScmBoxSet,
        OpCode.OpaqueValue -> true
        else -> false
    }

data class Operator(
    val op: OpCode,
    val nValueIn: Int,
    val nControlIn: Int,
    val nValueOut: Int,
    val nControlOut: Int,
    val extra: Any?
)

enum class RegionKind {
    Merge,
    LoopHeader,
}

// Hmm this is really hard to refactor.
class ArgumentOpExtra(val name: String, val index: Int) {
    override fun equals(other: Any?): Boolean = index == other
    override fun hashCode(): Int = index.hashCode()
    override fun toString() = name
}

class FreeVarOpExtra(val name: String, val index: Int) {
    override fun equals(other: Any?) = index == other
    override fun hashCode(): Int = index.hashCode()
    override fun toString() = name

    fun withIndex(newIndex: Int) = FreeVarOpExtra(name, newIndex)
}

class GetOperatorExtra(private val operator: Operator) {
    // Keep the mapping in sync with [Operators] below.
    val asArgument get() = cast<ArgumentOpExtra>(OpCode.Argument)
    val asFreeVar get() = cast<FreeVarOpExtra>(OpCode.FreeVar)
    val asLambdaLit get() = cast<GraphId>(OpCode.ScmLambdaLit)
    val asFxLit get() = cast<Int>(OpCode.ScmFxLit)
    val asBoolLit get() = cast<Boolean>(OpCode.ScmBoolLit)

    companion object {
        operator fun invoke(node: Node) = GetOperatorExtra(node.operator)
    }

    private inline fun <reified A> cast(op: OpCode): A {
        require(operator.op == op)
        return operator.extra as A
    }
}

object Operators {
    // Re number of inputs and outputs: The idea is that these are the "expected" number of inputs and outputs.
    // We shouldn't really limit the number of valueOutputs as that's determined by the number of uses.
    // OTOH valueIn / controlIn / controlOut are usually more strict.

    fun start() = make(OpCode.Start, nControlOut = 1)
    fun end(nRetNodes: Int = 1) = make(OpCode.End, nControlIn = nRetNodes)

    fun merge(nPreds: Int, nPhis: Int, kind: RegionKind) =
        make1(OpCode.Merge, nControlIn = nPreds, nControlOut = 1 + nPhis, extra = kind)

    fun ret() = make(OpCode.Return, nValueIn = 1, nControlIn = 1, nControlOut = 1)
    fun condJump() = make(OpCode.CondJump, nValueIn = 1, nControlIn = 1, nControlOut = 2)

    fun ifT() = make(OpCode.ScmIfT, nControlIn = 1, nControlOut = 1)
    fun ifF() = make(OpCode.ScmIfF, nControlIn = 1, nControlOut = 1)
    fun argument(extra: ArgumentOpExtra) = make1(OpCode.Argument, nValueIn = 1, extra = extra)
    fun freeVar(extra: FreeVarOpExtra) = make1(OpCode.FreeVar, nValueIn = 1, extra = extra)

    fun phi(nRegions: Int) = make(OpCode.Phi, nValueIn = nRegions, nControlIn = 1)

    fun call(nArgs: Int) = make(OpCode.Call, nValueIn = nArgs + 1, nControlIn = 1, nControlOut = 1)

    // Many of the literal nodes allocate, but are still pure from schemes' semantics.
    fun boolLit(value: Boolean) = make1(OpCode.ScmBoolLit, extra = value)
    fun boxLit() = make(OpCode.ScmBoxLit, nValueIn = 1, nControlIn = 1, nControlOut = 1)
    fun fxLit(value: Int) = make1(OpCode.ScmFxLit, extra = value)
    fun lambdaLit(nFreeVars: Int, graphId: GraphId) =
        make1(OpCode.ScmLambdaLit, nValueIn = nFreeVars, nControlIn = 1, nControlOut = 1, extra = graphId)

    fun symbolLit(value: String) = make1(OpCode.ScmSymbolLit, extra = value)

    fun boxGet() = make(OpCode.ScmBoxGet, nValueIn = 1, nControlIn = 1, nControlOut = 1)
    fun boxSet() = make(OpCode.ScmBoxSet, nValueIn = 2, nControlIn = 1, nControlOut = 1)

    fun fxAdd() = make(OpCode.ScmFxAdd, nValueIn = 2)
    fun fxSub() = make(OpCode.ScmFxSub, nValueIn = 2)
    fun fxLessThan() = make(OpCode.ScmFxLessThan, nValueIn = 2)

    fun opaqueValue() = make(OpCode.OpaqueValue, nValueIn = 1)

    fun dead() = make(OpCode.Dead)

    private fun make1(
        op: OpCode,
        nValueIn: Int = 0,
        nControlIn: Int = 0,
        nValueOut: Int = 0,
        nControlOut: Int = 0,
        extra: Any
    ): Operator {
        return Operator(
            op,
            nValueIn = nValueIn,
            nControlIn = nControlIn,
            nValueOut = nValueOut,
            nControlOut = nControlOut,
            extra = extra
        )
    }

    private fun make(
        op: OpCode,
        nValueIn: Int = 0,
        nControlIn: Int = 0,
        nValueOut: Int = 0,
        nControlOut: Int = 0
    ) = make1(
        op,
        nValueIn = nValueIn,
        nControlIn = nControlIn,
        nValueOut = nValueOut,
        nControlOut = nControlOut,
        extra = Unit
    )

    fun isSchemeIfProjections(operators: Collection<Operator>): Boolean {
        return operators.count() == 2 &&
            operators.count { it.op == OpCode.ScmIfT } == 1 &&
            operators.count { it.op == OpCode.ScmIfF } == 1
    }
}

