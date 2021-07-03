package com.gh.om.iueoc.son

// Version 1.

enum class OpCode {
    // Start node is the start of the graph
    // TODO: Start has argc output values (parameters).
    Start,

    // End node is the end of the graph
    End,

    // Region nodes mark the start of a block
    Region,

    // Jump nodes mark the end of a block
    Return,
    CondJump,

    // Value nodes
    IntLit,
}

interface Operator {
    val op: OpCode
    val nValueIn: Int
    val nControlIn: Int
    val nValueOut: Int
    val nControlOut: Int
}

data class Operator1<out A>(
    override val op: OpCode,
    override val nValueIn: Int,
    override val nControlIn: Int,
    override val nValueOut: Int,
    override val nControlOut: Int,
    val parameter: A,
) : Operator

object Operators {
    fun start() = make(OpCode.Start, nControlOut = 1)
    fun end(nRetNodes: Int = 1) = make(OpCode.End, nControlIn = nRetNodes)

    fun region() = make(OpCode.Region, nControlIn = 1, nControlOut = 1)

    fun ret() = make(OpCode.Return, nValueIn = 1, nControlIn = 1, nControlOut = 1)
    fun condJump() = make(OpCode.CondJump, nValueIn = 1, nControlIn = 1, nControlOut = 2)

    fun int(value: Int) = make1(OpCode.IntLit, parameter = value)

    private fun <A> make1(
        op: OpCode,
        nValueIn: Int = 0,
        nControlIn: Int = 0,
        nValueOut: Int = 0,
        nControlOut: Int = 0,
        parameter: A
    ): Operator1<A> {
        return Operator1(
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
}

typealias NodeId = Int
typealias MutNodeIds = MutableList<NodeId>

// Nodes are hash-cons-ed.
data class Node(
    val operator: Operator,
    val valueInputs: MutNodeIds,
    val controlInputs: MutNodeIds,
) {
    val valueOutputs: MutNodeIds = mutableListOf()
    val controlOutputs: MutNodeIds = mutableListOf()

    // Only assigned after GVN.
    var id: NodeId = NodeIds.FRESH_ID
        private set

    fun assignId(id: NodeId) {
        require(this.id == NodeIds.FRESH_ID)
        this.id = id
    }

    companion object {
        fun fresh(operator: Operator): Node {
            val vins = MutableList(operator.nValueIn) { NodeIds.UNPOPULATED_ID }
            val cins = MutableList(operator.nControlIn) { NodeIds.UNPOPULATED_ID }
            val n = Node(operator, vins, cins)
            n.valueOutputs += List(operator.nValueOut) { NodeIds.UNPOPULATED_ID }
            n.controlOutputs += List(operator.nControlOut) { NodeIds.UNPOPULATED_ID }
            return n
        }
    }
}

// Asserts that the node has only 1 value input
val Node.valueInput: NodeId
    get() {
        require(valueInputs.size == 1)
        return valueInputs.first()
    }

// Asserts that the node has only 1 control output
val Node.controlOutput: NodeId
    get() {
        require(controlOutputs.size == 1)
        return controlOutputs.first()
    }

class GraphBuilder {
    private var idGen: Int = NodeIds.FIRST_ID_IN_GRAPH
    private fun nextId(): Int {
        return idGen++
    }

    val nodes: MutableMap<NodeId, Node> = mutableMapOf()

    val start: NodeId
    val end: NodeId

    init {
        start = assignId(Nodes.start())
        end = assignId(Nodes.end())
        // Connect them
        get(start).controlOutputs[0] = end
        get(end).controlInputs[0] = start
    }

    private fun assignId(node: Node): NodeId {
        node.assignId(nextId())
        nodes[node.id] = node
        return node.id
    }

    private operator fun get(nid: NodeId): Node {
        return requireNotNull(nodes[nid]) {
            "$nid doesn't exist. All nodes: ${nodes.keys}"
        }
    }

    inner class Verifier {
        fun verify() {
            val visited = mutableSetOf<NodeId>()
            goNode(start, ExecutionState.StartGraph, visited)
            require(end in visited)
        }

        fun verifyEdgeExists(from: NodeId, to: NodeId, kind: EdgeKind) {
            val (getIn, getOut) = when (kind) {
                EdgeKind.Value -> Node::valueInputs to Node::valueOutputs
                EdgeKind.Control -> Node::controlInputs to Node::controlOutputs
            }
            val fromN = get(from)
            val toN = get(to)
            require(getOut(fromN).count { it == to } == 1)
            require(getIn(toN).count { it == from } == 1)
        }

        fun verifyEdges(nid: NodeId) {
            val n = get(nid)

            require(n.valueInputs.all(NodeIds::isValid))
            require(n.controlInputs.all(NodeIds::isValid))
            require(n.valueOutputs.all(NodeIds::isValid))
            require(n.controlInputs.all(NodeIds::isValid))

            require(n.valueInputs.size == n.operator.nValueIn)
            require(n.valueOutputs.size == n.operator.nValueOut)
            require(n.controlInputs.size == n.operator.nControlIn)
            require(n.controlOutputs.size == n.operator.nControlOut)

            n.valueOutputs.forEach {
                verifyEdgeExists(nid, it, EdgeKind.Value)
            }
            n.controlOutputs.forEach {
                verifyEdgeExists(nid, it, EdgeKind.Control)
            }
        }

        tailrec fun goNode(nid: NodeId, nk: ExecutionState, visited: MutableSet<NodeId>) {
            if (nid in visited) {
                return
            }
            visited += nid
            verifyEdges(nid)
            val n = get(nid)
            when (n.operator.op) {
                OpCode.Start -> {
                    require(nk == ExecutionState.StartGraph)

                    require(get(n.controlOutput).operator.op != OpCode.Start)
                    goNode(n.controlOutput, ExecutionState.StartBlock, visited)
                }
                OpCode.Region -> {
                    require(nk == ExecutionState.StartBlock)

                    goNode(n.controlOutput, ExecutionState.EndBlock, visited)
                }
                OpCode.End -> {
                    require(nk == ExecutionState.StartBlock)
                    // Done
                }
                OpCode.Return -> {
                    require(nk == ExecutionState.EndBlock)

                    @Suppress("NON_TAIL_RECURSIVE_CALL")
                    goNode(n.valueInput, ExecutionState.Value, visited)

                    val end = get(n.controlOutput)
                    require(end.operator.op == OpCode.End)
                    goNode(n.controlOutput, ExecutionState.StartBlock, visited)
                }
                OpCode.CondJump -> {
                    require(nk == ExecutionState.EndBlock)

                    n.controlOutputs.forEach {
                        @Suppress("NON_TAIL_RECURSIVE_CALL")
                        goNode(it, ExecutionState.StartBlock, visited)
                    }
                }
                OpCode.IntLit -> {
                    require(nk == ExecutionState.Value)
                }
            }
        }
    }

    // Visit nodes from start and verify that all the reachable nodes are fully built
    fun verifyFullyBuilt() {
        val visited = mutableSetOf<NodeId>()

    }
}

object Nodes {
    fun start() = Node.fresh(Operators.start())
    fun end() = Node.fresh(Operators.end())
    fun int(value: Int) = Node.fresh(Operators.int(value))
    fun ret() = Node.fresh(Operators.ret())
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

enum class ExecutionState {
    StartGraph,
    StartBlock,
    EndBlock,
    Value,
}

enum class EdgeKind {
    Value,
    Control,
}

private fun main() {
    val gb = GraphBuilder()
    gb.Verifier().verify()
}