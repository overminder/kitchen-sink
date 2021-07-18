package com.gh.om.iueoc.son

enum class OpCode(val klass: OpCodeClass) {
    // Start node is the start of the graph
    // o(C:entryRegion, V:effect, V:Argument ** |args|, V:FreeVar ** |upvals|)
    Start(OpCodeClass.Anchor),

    // End node is the end of the graph
    // i(C): One (or more) control input (from return)
    End(OpCodeClass.Anchor),

    // Region nodes mark the start of a block.
    // This can also be a join point for multiple incoming blocks (merge node in v8)
    // i(C:jumpOrStart ** |preds|): n predecessors, can be jump or start
    // o(C:jump; C:phi ** |preds|): 1 jump node + n phis.
    // Each phi's value input corresponds to the control input on the same index in this region.
    Region(OpCodeClass.Anchor),

    // Jump nodes mark the end of a block
    // i(V:effect, V:retVal, C:region), o(C:end)
    Return(OpCodeClass.Jump),

    // i(V:cond, C:currentRegion), o(C:ifT, C:ifF): 2 projection outputs
    CondJump(OpCodeClass.Jump),

    // io(C): Jump from region to region
    Jump(OpCodeClass.Jump),

    // Projection nodes
    // Control projections
    // i(C:condJump), o(C:nextRegion)
    // Scm-prefixed to check for not #f and #f.
    ScmIfT(OpCodeClass.Projection),
    ScmIfF(OpCodeClass.Projection),

    // Value projections
    // Function argument. i(V): start; p(ArgumentOpExtra): name and nth argument
    Argument(OpCodeClass.Projection),

    // Closure lifted free var (upvalue). i(V): start; p(FreeVarOpExtra): name and nth free var
    FreeVar(OpCodeClass.Projection),

    // i(V:effectfulNode): The effect of an operation. This is created by Start and threaded by effectful nodes
    // (e.g. alloc and memory read/write). Note that this can be consumed by multiple nodes, when the control
    // is split (e.g. (if _ (write-1) (write-2))).
    Effect(OpCodeClass.Projection),

    // Value nodes
    // Phi in v8 takes a single control input (Merge). A Region is roughly a Merge.
    // i(C; V ** n): The region that contains the phi (just like phis appearing in a basic block's header),
    // and the value nodes to choose from. Each value input corresponds to the region's control input on the
    // same index.
    Phi(OpCodeClass.Phi),
    EffectPhi(OpCodeClass.Phi),

    // i(V:memory, V:target, V:args, C:regionOrFixed) o(V:memory, V:result, C:jumpOrFixed)
    // In v8, call nodes are associated with lot of complicated information in v8.
    // And they may need control in/out as well.
    Call(OpCodeClass.Value),

    // Literals
    ScmBoolLit(OpCodeClass.Value),

    // i(V:effect, V:toBox)
    ScmBoxLit(OpCodeClass.Value),
    ScmFxLit(OpCodeClass.Value),

    // i(V:effect, V:freeVar ** |freeVars|)
    ScmLambdaLit(OpCodeClass.Value),
    ScmSymbolLit(OpCodeClass.Value),

    // Box operations
    // i(V:effect V:box)
    ScmBoxGet(OpCodeClass.Value),

    // i(V:effect, V:box, V:newValue)
    ScmBoxSet(OpCodeClass.Value),

    // Int operations
    ScmFxAdd(OpCodeClass.Value),
    ScmFxSub(OpCodeClass.Value),
    ScmFxLessThan(OpCodeClass.Value),

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

    // Dead etc
    Misc,
}

val OpCode.isPure: Boolean
    get() = when (this) {
        OpCode.ScmBoolLit,
        OpCode.ScmFxLit,
        OpCode.ScmSymbolLit,

        OpCode.ScmFxAdd,
        OpCode.ScmFxSub,
        OpCode.ScmFxLessThan -> true
        else -> false
    }

val OpCode.isEffectfulValue: Boolean
    get() = when (this) {
        OpCode.Call,

        OpCode.ScmBoxLit,
        OpCode.ScmBoxSet,
        OpCode.ScmBoxGet,

        OpCode.ScmLambdaLit -> true
        else -> false
    }

val OpCode.isEffect: Boolean
    get() = when (this) {
        OpCode.Effect,
        OpCode.EffectPhi -> true
        else -> false
    }

val OpCode.isJump: Boolean
    get() = when (this) {
        OpCode.Jump,
        OpCode.CondJump,
        OpCode.Return -> true
        else -> false
    }

val OpCode.isRegionOrFixedWithNext: Boolean
    get() = this == OpCode.Region || isFixedWithNext

val OpCode.isFixedWithNext: Boolean
    get() = when (this) {
        OpCode.Call -> true
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
        OpCode.ScmBoxSet -> true
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
    Basic,
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

    fun region(nPreds: Int, nPhis: Int, kind: RegionKind) = make1(OpCode.Region, nControlIn = nPreds, nControlOut = 1 + nPhis, extra = kind)

    fun ret() = make(OpCode.Return, nValueIn = 2, nControlIn = 1, nControlOut = 1)
    fun condJump() = make(OpCode.CondJump, nValueIn = 1, nControlIn = 1, nControlOut = 2)
    fun jump() = make(OpCode.Jump, nControlIn = 1, nControlOut = 1)

    fun ifT() = make(OpCode.ScmIfT, nControlIn = 1, nControlOut = 1)
    fun ifF() = make(OpCode.ScmIfF, nControlIn = 1, nControlOut = 1)
    fun argument(extra: ArgumentOpExtra) = make1(OpCode.Argument, nValueIn = 1, extra = extra)
    fun freeVar(extra: FreeVarOpExtra) = make1(OpCode.FreeVar, nValueIn = 1, extra = extra)
    fun effect() = make(OpCode.Effect, nValueIn = 1)

    fun phi(nRegions: Int) = make(OpCode.Phi, nValueIn = nRegions, nControlIn = 1)
    fun effectPhi(nRegions: Int) = make(OpCode.EffectPhi, nValueIn = nRegions, nControlIn = 1)

    fun call(nArgs: Int) = make(OpCode.Call, nValueIn = 2 + nArgs, nControlIn = 1, nControlOut = 1)

    // Many of the literal nodes allocate, but are still pure from schemes' semantics.
    fun boolLit(value: Boolean) = make1(OpCode.ScmBoolLit, extra = value)
    fun boxLit() = make(OpCode.ScmBoxLit, nValueIn = 2)
    fun fxLit(value: Int) = make1(OpCode.ScmFxLit, extra = value)
    fun lambdaLit(nFreeVars: Int, graphId: GraphId) =
        make1(OpCode.ScmLambdaLit, nValueIn = 1 + nFreeVars, extra = graphId)

    fun symbolLit(value: String) = make1(OpCode.ScmSymbolLit, extra = value)

    fun boxGet() = make(OpCode.ScmBoxGet, nValueIn = 2)
    fun boxSet() = make(OpCode.ScmBoxSet, nValueIn = 3)

    fun fxAdd() = make(OpCode.ScmFxAdd, nValueIn = 2)
    fun fxSub() = make(OpCode.ScmFxSub, nValueIn = 2)
    fun fxLessThan() = make(OpCode.ScmFxLessThan, nValueIn = 2)

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

