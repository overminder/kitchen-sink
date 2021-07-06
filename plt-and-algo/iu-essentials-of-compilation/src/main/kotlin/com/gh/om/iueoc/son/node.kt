package com.gh.om.iueoc.son

// Version 1.

enum class OpCode(val klass: OpCodeClass) {
    // Start node is the start of the graph
    // o(C; V; V ** |args|; V ** |upvals|): One control output to the entry region, one memory output,
    // and a bunch of upvals and parameters.
    Start(OpCodeClass.Anchor),

    // End node is the end of the graph
    // i(C): One (or more) control input (from return)
    End(OpCodeClass.Anchor),

    // Region nodes mark the start of a block
    // i(C ** n): n predecessors, can be jump or start
    // o(C; C ** n): 1 jump node + n phis.
    // Each phi's value input corresponds to the control input on the same index in this region.
    Region(OpCodeClass.Anchor),

    // Jump nodes mark the end of a block
    // i(V:memory, V:retVal, C:region), o(C:end)
    Return(OpCodeClass.Jump),

    // i(V:cond C:currentRegion), o(C:ifT, C:ifF): 2 projection outputs
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
    // io(V): The memory effect of an operation. This is created by Start and threaded by memory writes (e.g. box-set!).
    // Memory reads (box-get) also need an input of this.
    Memory(OpCodeClass.Projection),

    // Value nodes
    // Phi in v8 takes a single control input (Merge). A Region is roughly a Merge.
    // i(C; V ** n): The region that contains the phi (just like phis appearing in a basic block's header),
    // and the value nodes to choose from. Each value input corresponds to the region's control input on the
    // same index.
    Phi(OpCodeClass.Phi),
    MemoryPhi(OpCodeClass.Phi),

    // Literals
    ScmBoolLit(OpCodeClass.Value),
    // i(V:box)
    ScmBoxLit(OpCodeClass.Value),
    ScmFxLit(OpCodeClass.Value),
    ScmLambdaLit(OpCodeClass.Value),
    ScmSymbolLit(OpCodeClass.Value),

    // Box operations
    // i(V:memory V:box)
    ScmBoxGet(OpCodeClass.Value),
    // i(V:memory, V:box, V:newValue)
    ScmBoxSet(OpCodeClass.Value),

    // Int operations
    ScmFxAdd(OpCodeClass.Value),
    ScmFxLessThan(OpCodeClass.Value),

    Dead(OpCodeClass.Misc),
}

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
        OpCode.ScmBoxLit,
        OpCode.ScmFxLit,
        OpCode.ScmLambdaLit,
        OpCode.ScmSymbolLit,

        OpCode.ScmBoxGet,

        OpCode.ScmFxAdd,
        OpCode.ScmFxLessThan -> true
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

object Operators {
    // Re number of inputs and outputs: The idea is that these are the "expected" number of inputs and outputs.
    // We shouldn't really limit the number of valueOutputs as that's determined by the number of uses.
    // OTOH valueIn / controlIn / controlOut are usually more strict.

    fun start() = make(OpCode.Start, nControlOut = 1)
    fun end(nRetNodes: Int = 1) = make(OpCode.End, nControlIn = nRetNodes)

    fun region(nPreds: Int, nPhis: Int) = make(OpCode.Region, nControlIn = nPreds, nControlOut = 1 + nPhis)

    fun ret() = make(OpCode.Return, nValueIn = 2, nControlIn = 1, nControlOut = 1)
    fun condJump() = make(OpCode.CondJump, nValueIn = 1, nControlIn = 1, nControlOut = 2)
    fun jump() = make(OpCode.Jump, nControlIn = 1, nControlOut = 1)

    fun ifT() = make(OpCode.ScmIfT, nControlIn = 1, nControlOut = 1)
    fun ifF() = make(OpCode.ScmIfF, nControlIn = 1, nControlOut = 1)
    fun argument(extra: ArgumentOpExtra) = make1(OpCode.Argument, nValueIn = 1, parameter = extra)
    fun freeVar(extra: FreeVarOpExtra) = make1(OpCode.FreeVar, nValueIn = 1, parameter = extra)
    fun memory() = make(OpCode.Memory, nValueIn = 1)

    fun phi(nRegions: Int) = make(OpCode.Phi, nValueIn = nRegions, nControlIn = 1)
    fun memoryPhi(nRegions: Int) = make(OpCode.MemoryPhi, nValueIn = nRegions, nControlIn = 1)

    // Many of the literal nodes allocate, but are still pure from schemes' semantics.
    fun boolLit(value: Boolean) = make1(OpCode.ScmBoolLit, parameter = value)
    fun boxLit() = make(OpCode.ScmBoxLit, nValueIn = 1)
    fun fxLit(value: Int) = make1(OpCode.ScmFxLit, parameter = value)
    fun lambdaLit(graphId: GraphId) = make1(OpCode.ScmLambdaLit, parameter = graphId)
    fun symbolLit(value: String) = make1(OpCode.ScmSymbolLit, parameter = value)

    fun boxGet() = make(OpCode.ScmBoxGet, nValueIn = 2)
    fun boxSet() = make(OpCode.ScmBoxSet, nValueIn = 3)

    fun fxAdd() = make(OpCode.ScmFxAdd, nValueIn = 2)
    fun fxLessThan() = make(OpCode.ScmFxLessThan, nValueIn = 2)

    fun dead() = make(OpCode.Dead)

    private fun make1(
        op: OpCode,
        nValueIn: Int = 0,
        nControlIn: Int = 0,
        nValueOut: Int = 0,
        nControlOut: Int = 0,
        parameter: Any
    ): Operator {
        return Operator(
            op,
            nValueIn = nValueIn,
            nControlIn = nControlIn,
            nValueOut = nValueOut,
            nControlOut = nControlOut,
            extra = parameter
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
        parameter = Unit
    )

    fun isSchemeIfProjections(operators: Collection<Operator>): Boolean {
        return operators.count() == 2 &&
            operators.count { it.op == OpCode.ScmIfT } == 1 &&
            operators.count { it.op == OpCode.ScmIfF } == 1
    }
}

typealias NodeId = Int
typealias NodeIdList = List<NodeId>
typealias MutNodeIdList = MutableList<NodeId>
typealias MutNodeMap = MutableMap<NodeId, Node>
typealias NodeMap = Map<NodeId, Node>

class Node(operator: Operator) {
    var operator = operator
        private set

    val valueInputs: NodeIdList get() = _valueInputs
    val controlInputs: NodeIdList get() = _controlInputs
    val valueOutputs: NodeIdList get() = _valueOutputs
    val controlOutputs: NodeIdList get() = _controlOutputs

    private val _valueInputs: MutNodeIdList = mutableListOf()
    private val _controlInputs: MutNodeIdList = mutableListOf()
    private val _valueOutputs: MutNodeIdList = mutableListOf()
    private val _controlOutputs: MutNodeIdList = mutableListOf()

    override fun toString(): String {
        val hex = System.identityHashCode(this).and(0xffff).toString(16)
        return "<Node ${operator.op} ${operator.extra} $hex>"
    }

    // Only assigned after GVN.
    var id: NodeId = NodeIds.FRESH_ID
        private set

    fun assignId(id: NodeId) {
        require(this.id == NodeIds.FRESH_ID)
        this.id = id
    }

    /**
     * @param populating True to override an UNPOPULATED_ID edge. This means that the total number of
     *  inputs is not changed. Asserts if none is found.
     *  False to insert an additional edge, and update operator to change the edge count.
     */
    fun addInput(input: Node, edgeKind: EdgeKind, populating: Boolean = false) {
        require(NodeIds.isValid(id))
        require(NodeIds.isValid(input.id))

        val inputsToUpdate = mutableInputsByKind(edgeKind)
        // Add input to self.inputs
        if (populating) {
            val index = inputsToUpdate.indexOf(NodeIds.UNPOPULATED_ID)
            require(index != -1) { "All populated in $this" }
            inputsToUpdate[index] = input.id
        } else {
            inputsToUpdate.add(input.id)
            operator = when (edgeKind) {
                EdgeKind.Value -> operator.copy(nValueIn = operator.nValueIn + 1)
                EdgeKind.Control -> operator.copy(nControlIn = operator.nControlIn + 1)
            }
        }
        // Add self to input.uses
        input.addUse(this, edgeKind, populating = populating)
    }

    fun replaceInput(oldInput: Node, newInput: Node, edgeKind: EdgeKind) {
        require(NodeIds.isValid(id))
        require(NodeIds.isValid(oldInput.id))
        require(NodeIds.isValid(newInput.id))

        val inputsToUpdate = mutableInputsByKind(edgeKind)
        val index = inputsToUpdate.indexOf(oldInput.id)
        require(index != -1)
        inputsToUpdate[index] = newInput.id
        oldInput.removeUse(this, edgeKind)
        newInput.addUse(this, edgeKind, populating = false)
    }

    private fun addUse(use: Node, edgeKind: EdgeKind, populating: Boolean) {
        val outputsToUpdate = mutableOutputsByKind(edgeKind)
        if (populating && edgeKind == EdgeKind.Control) {
            // Usually only control edges need explicit population
            val index = outputsToUpdate.indexOf(NodeIds.UNPOPULATED_ID)
            require(index != -1) { "All populated in $this" }
            outputsToUpdate[index] = use.id
        } else {
            outputsToUpdate.add(use.id)
            operator = when (edgeKind) {
                EdgeKind.Value -> operator.copy(nValueOut = operator.nValueOut + 1)
                EdgeKind.Control -> operator.copy(nControlOut = operator.nControlOut + 1)
            }
        }
    }

    private fun removeUse(use: Node, edgeKind: EdgeKind) {
        val outputsToUpdate = mutableOutputsByKind(edgeKind)
        val index = outputsToUpdate.indexOf(use.id)
        require(index != -1)
        outputsToUpdate.removeAt(index)
        operator = when (edgeKind) {
            EdgeKind.Value -> operator.copy(nValueOut = operator.nValueOut - 1)
            EdgeKind.Control -> operator.copy(nControlOut = operator.nControlOut - 1)
        }
    }

    fun updateOperator(f: (Operator) -> Operator) {
        operator = f(operator)
    }

    private fun mutableInputsByKind(kind: EdgeKind): MutNodeIdList = when (kind) {
        EdgeKind.Value -> _valueInputs
        EdgeKind.Control -> _controlInputs
    }

    private fun mutableOutputsByKind(kind: EdgeKind): MutNodeIdList = when (kind) {
        EdgeKind.Value -> _valueOutputs
        EdgeKind.Control -> _controlOutputs
    }

    fun inputsByKind(kind: EdgeKind): NodeIdList = mutableInputsByKind(kind)

    fun outputsByKind(kind: EdgeKind): NodeIdList = mutableOutputsByKind(kind)

    companion object {
        // A freshly created node has no assigned Id, and all its edges are uninitialized (but allocated).
        fun fresh(operator: Operator): Node {
            val n = Node(operator)
            n._valueInputs += List(operator.nValueIn) { NodeIds.UNPOPULATED_ID }
            n._controlInputs += List(operator.nControlIn) { NodeIds.UNPOPULATED_ID }
            n._valueOutputs += List(operator.nValueOut) { NodeIds.UNPOPULATED_ID }
            n._controlOutputs += List(operator.nControlOut) { NodeIds.UNPOPULATED_ID }
            return n
        }
    }
}

// Asserts that the node has only 1 value input
val Node.singleValueInput: NodeId
    get() {
        require(valueInputs.size == 1)
        return valueInputs.first()
    }

// Asserts that the node has only 1 control input
val Node.singleControlInput: NodeId
    get() {
        require(controlInputs.size == 1)
        return controlInputs.first()
    }

// Asserts that the node has only 1 control output
val Node.singleControlOutput: NodeId
    get() {
        require(controlOutputs.size == 1)
        return controlOutputs.first()
    }

object Nodes {
    fun start() = Node.fresh(Operators.start())
    fun end() = Node.fresh(Operators.end())

    fun region(nPreds: Int, nPhis: Int) = Node.fresh(Operators.region(nPreds = nPreds, nPhis = nPhis))

    fun ret() = Node.fresh(Operators.ret())
    fun condJump() = Node.fresh(Operators.condJump())
    fun jump() = Node.fresh(Operators.jump())

    fun ifT() = Node.fresh(Operators.ifT())
    fun ifF() = Node.fresh(Operators.ifF())
    fun argument(extra: ArgumentOpExtra) = Node.fresh(Operators.argument(extra))
    fun freeVar(extra: FreeVarOpExtra) = Node.fresh(Operators.freeVar(extra))
    fun memory() = Node.fresh(Operators.memory())

    fun phi(nRegions: Int) = Node.fresh(Operators.phi(nRegions))
    fun memoryPhi(nRegions: Int) = Node.fresh(Operators.memoryPhi(nRegions))

    fun boolLit(value: Boolean) = Node.fresh(Operators.boolLit(value))
    fun boxLit() = Node.fresh(Operators.boxLit())
    fun intLit(value: Int) = Node.fresh(Operators.fxLit(value))
    fun lambdaLit(graphId: Int) = Node.fresh(Operators.lambdaLit(graphId))
    fun symbolLit(value: String) = Node.fresh(Operators.symbolLit(value))

    fun fxAdd() = Node.fresh(Operators.fxAdd())
    fun fxLessThan() = Node.fresh(Operators.fxLessThan())
    fun boxGet() = Node.fresh(Operators.boxGet())
    fun boxSet() = Node.fresh(Operators.boxSet())

    fun dead() = Node.fresh(Operators.dead())
}

object NodeIds {
    // Inputs / outputs
    const val UNPOPULATED_ID = -2

    // Fresh node
    const val FRESH_ID = -1
    const val FIRST_ID_IN_GRAPH = 1

    fun isValid(id: NodeId): Boolean {
        return id >= FIRST_ID_IN_GRAPH
    }
}

enum class EdgeKind {
    Value,
    Control,
}

/**
 * @param nthInput The input index wrt to, i.e. to[kind, nthInput] == from
 */
data class Edge(val from: NodeId, val to: NodeId, val kind: EdgeKind, val nthInput: Int)

interface Graph {
    val nodes: NodeMap
    val start: NodeId
    val end: NodeId
    val id: GraphId
    val name: String?
}

operator fun Graph.get(id: NodeId): Node {
    return requireNotNull(nodes[id]) {
        "$id doesn't exist. All nodes: ${nodes.keys}"
    }
}

// It's hard to implement a general purpose mutable graph -- We may need various bookkeeping processes
// between mutations. E.g to reconstruct SSA.
/*
interface MutGraph: Graph {
    override val nodes: MutNodeMap

    fun gvn(n: Node): NodeId?
}
 */