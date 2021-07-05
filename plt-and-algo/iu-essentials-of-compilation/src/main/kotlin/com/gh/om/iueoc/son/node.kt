package com.gh.om.iueoc.son

// Version 1.

enum class OpCode(val klass: OpCodeClass) {
    // Start node is the start of the graph
    // TODO: Start has argc output values (parameters).
    // o(C)
    Start(OpCodeClass.Anchor),

    // End node is the end of the graph
    // i(C)
    End(OpCodeClass.Anchor),

    // Region nodes mark the start of a block
    // i(C ** n): n predecessors, can be jump or start
    // o(C; C ** n): 1 jump node + n phis.
    // Each phi's value input corresponds to the control input on the same index in this region.
    Region(OpCodeClass.Anchor),

    // Jump nodes mark the end of a block
    // i(VC): 1 return value, 1 region input. o(C): 1 end node output.
    Return(OpCodeClass.Jump),
    // i(VC): 1 return value, 1 region input. o(CC): 2 projection outputs
    CondJump(OpCodeClass.Jump),
    // io(C): Jump from region to region
    Jump(OpCodeClass.Jump),

    // Projection nodes
    // io(C): 1 CondJump input, 1 region output
    // Scm-prefixed to check for not #f and #f.
    ScmIfT(OpCodeClass.Projection),
    ScmIfF(OpCodeClass.Projection),

    // Value nodes
    // Phi in v8 takes a single control input (Merge). A Region is roughly a Merge.
    // i(C; V ** n): The region that contains the phi (just like phis appearing in a basic block's header),
    // and the value nodes to choose from. Each value input corresponds to the region's control input on the
    // same index.
    Phi(OpCodeClass.Phi),

    // Literals
    ScmBoolLit(OpCodeClass.Value),
    ScmSymbolLit(OpCodeClass.Value),
    ScmFxLit(OpCodeClass.Value),

    // Int operations
    ScmFxAdd(OpCodeClass.Value),
    ScmFxLessThan(OpCodeClass.Value),
}

enum class OpCodeClass {
    // Start/End/Region
    Anchor,
    // End of basic blocks
    Jump,
    Projection,
    Phi,
    Value,
}

val OpCode.isPure: Boolean
    get() = when (this) {
        OpCode.ScmFxLit, OpCode.ScmFxAdd, OpCode.ScmFxLessThan -> true
        else -> false
    }

data class Operator(
    val op: OpCode,
    val nValueIn: Int,
    val nControlIn: Int,
    val nValueOut: Int,
    val nControlOut: Int,
    val parameter: Any?
)

object Operators {
    // Re number of inputs and outputs: The idea is that these are the "expected" number of inputs and outputs.
    // We shouldn't really limit the number of valueOutputs as that's determined by the number of uses.
    // OTOH valueIn / controlIn / controlOut are usually more strict.
    // Nodes are responsible

    fun start() = make(OpCode.Start, nControlOut = 1)
    fun end(nRetNodes: Int = 1) = make(OpCode.End, nControlIn = nRetNodes)

    fun region(nPreds: Int, nPhis: Int) = make(OpCode.Region, nControlIn = nPreds, nControlOut = 1 + nPhis)

    fun ret() = make(OpCode.Return, nValueIn = 1, nControlIn = 1, nControlOut = 1)
    fun condJump() = make(OpCode.CondJump, nValueIn = 1, nControlIn = 1, nControlOut = 2)
    fun jump() = make(OpCode.Jump, nControlIn = 1, nControlOut = 1)

    fun ifT() = make(OpCode.ScmIfT, nControlIn = 1, nControlOut = 1)
    fun ifF() = make(OpCode.ScmIfF, nControlIn = 1, nControlOut = 1)

    fun phi(nRegions: Int) = make(OpCode.Phi, nValueIn = nRegions, nControlIn = 1)
    fun boolLit(value: Boolean) = make1(OpCode.ScmBoolLit, parameter = value)
    fun symbolLit(value: String) = make1(OpCode.ScmSymbolLit, parameter = value)
    fun intLit(value: Int) = make1(OpCode.ScmFxLit, parameter = value)
    fun intAdd() = make(OpCode.ScmFxAdd, nValueIn = 2)
    fun intLessThan() = make(OpCode.ScmFxLessThan, nValueIn = 2)

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
            parameter = parameter
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

        val inputsToUpdate = when (edgeKind) {
            EdgeKind.Value -> _valueInputs
            EdgeKind.Control -> _controlInputs
        }
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

    private fun addUse(use: Node, edgeKind: EdgeKind, populating: Boolean) {
        val outputsToUpdate = when (edgeKind) {
            EdgeKind.Value -> _valueOutputs
            EdgeKind.Control -> _controlOutputs
        }
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

    companion object {
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

interface Graph {
    val nodes: NodeMap
    val start: NodeId
    val end: NodeId
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

object Nodes {
    fun start() = Node.fresh(Operators.start())
    fun end() = Node.fresh(Operators.end())

    fun region(nPreds: Int, nPhis: Int) = Node.fresh(Operators.region(nPreds = nPreds, nPhis = nPhis))

    fun ret() = Node.fresh(Operators.ret())
    fun condJump() = Node.fresh(Operators.condJump())
    fun jump() = Node.fresh(Operators.jump())

    fun ifT() = Node.fresh(Operators.ifT())
    fun ifF() = Node.fresh(Operators.ifF())

    fun phi(nRegions: Int) = Node.fresh(Operators.phi(nRegions))
    fun symbolLit(value: String) = Node.fresh(Operators.symbolLit(value))
    fun boolLit(value: Boolean) = Node.fresh(Operators.boolLit(value))
    fun intLit(value: Int) = Node.fresh(Operators.intLit(value))
    fun intAdd() = Node.fresh(Operators.intAdd())
    fun intLessThan() = Node.fresh(Operators.intLessThan())
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