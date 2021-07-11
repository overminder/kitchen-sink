package com.gh.om.iueoc.son

@JvmInline
value class NodeId(val v: Int)
typealias NodeIdList = List<NodeId>
typealias MutNodeIdList = MutableList<NodeId>
typealias MutNodeMap = MutableMap<NodeId, Node>
typealias NodeMap = Map<NodeId, Node>

class Node(operator: Operator) {
    var operator = operator
        private set

    val opCode: OpCode
        get() = operator.op

    // Must be assigned before adding edges.
    var id: NodeId = NodeIds.FRESH_ID
        private set

    val valueInputs: NodeIdList get() = _valueInputs
    val controlInputs: NodeIdList get() = _controlInputs
    val valueOutputs: NodeIdList get() = _valueOutputs
    val controlOutputs: NodeIdList get() = _controlOutputs

    private val _valueInputs: MutNodeIdList = mutableListOf()
    private val _controlInputs: MutNodeIdList = mutableListOf()
    private val _valueOutputs: MutNodeIdList = mutableListOf()
    private val _controlOutputs: MutNodeIdList = mutableListOf()

    fun deepCopy() = deepCopyMapped { it }

    fun deepCopyMapped(convertId: (NodeId) -> NodeId): Node {
        val n = Node(operator)
        n._valueInputs += _valueInputs.map(convertId)
        n._controlInputs += _controlInputs.map(convertId)
        n._valueOutputs += _valueOutputs.map(convertId)
        n._controlOutputs += _controlOutputs.map(convertId)
        n.id = convertId(id)
        return n
    }

    override fun toString(): String {
        val extraPart = if (operator.extra == null || operator.extra == Unit) {
            ""
        } else {
            " ${operator.extra}"
        }
        val hex = System.identityHashCode(this).and(0xffff).toString(16)
        return "<Node ${id.v} ${operator.op}$extraPart 0x$hex>"
    }

    fun assignId(id: NodeId) {
        require(this.id == NodeIds.FRESH_ID)
        this.id = id
    }

    fun populateInput(input: Node, edgeKind: EdgeKind) {
        addInput(input, edgeKind, EdgeDirection.Both)
    }

    fun becomeValueNode(newValue: Node, graph: Graph) {
        // Node replacement is actually tricky.
        // For a pure value node (e.g. a + b), this can be as simple as replace any use of this with [by].
        // Could also be useful to remove input to this node.
        // XXX: Doing this on the fly will also invalidate the unique value node cache...
        require(controlOutputs.isEmpty())
        val vouts = valueOutputs.map { graph[it] }
        vouts.forEach {
            it.replaceInput(this, newValue, EdgeKind.Value)
        }
    }

    fun becomeControlNode(newValue: Node, graph: Graph) {
        require(valueOutputs.isEmpty())
        graph[singleControlOutput].replaceInput(this, newValue, EdgeKind.Control)
    }

    /**
     * @param populating True to override an UNPOPULATED_ID edge. This means that the total number of
     *  inputs is not changed. Asserts if none is found.
     *  False to insert an additional edge, and update operator to change the edge count.
     */
    fun addInput(input: Node, edgeKind: EdgeKind, populating: EdgeDirection) {
        require(NodeIds.isValid(id))
        require(NodeIds.isValid(input.id))

        val inputsToUpdate = mutableInputsByKind(edgeKind)
        // Add input to self.inputs
        if (populating.input) {
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
        input.addUse(this, edgeKind, populating)
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
        newInput.addUse(this, edgeKind, EdgeDirection.None)
    }

    fun removeInput(input: Node, edgeKind: EdgeKind) {
        require(NodeIds.isValid(id))
        require(NodeIds.isValid(input.id))

        val inputsToUpdate = mutableInputsByKind(edgeKind)
        val index = inputsToUpdate.indexOf(input.id)
        require(index != -1)
        inputsToUpdate.removeAt(index)
        input.removeUse(this, edgeKind)
    }

    private fun addUse(use: Node, edgeKind: EdgeKind, populating: EdgeDirection) {
        val outputsToUpdate = mutableOutputsByKind(edgeKind)
        if (populating.output && edgeKind == EdgeKind.Control) {
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

// Asserts that the node has only 1 value input
val Node.singleValueOutput: NodeId
    get() {
        require(valueOutputs.size == 1)
        return valueOutputs.first()
    }

// Asserts that the node has only 1 control output
val Node.singleControlOutput: NodeId
    get() {
        require(controlOutputs.size == 1)
        return controlOutputs.first()
    }

fun Node.removeEdges(
    g: Graph,
    direction: EdgeDirection = EdgeDirection.Both,
    edgeKinds: Array<EdgeKind> = EdgeKind.ALL
) {
    for (edgeKind in edgeKinds) {
        if (direction.input) {
            inputsByKind(edgeKind).map(g::get).forEach {
                removeInput(it, edgeKind)
            }
        }
        if (direction.output) {
            outputsByKind(edgeKind).map(g::get).forEach {
                it.removeInput(this, edgeKind)
            }
        }
    }
}

object Nodes {
    fun start() = Node.fresh(Operators.start())
    fun end() = Node.fresh(Operators.end())

    fun region(nPreds: Int, nPhis: Int, kind: RegionKind) =
        Node.fresh(Operators.region(nPreds = nPreds, nPhis = nPhis, kind = kind))

    fun ret() = Node.fresh(Operators.ret())
    fun condJump() = Node.fresh(Operators.condJump())
    fun jump() = Node.fresh(Operators.jump())

    fun ifT() = Node.fresh(Operators.ifT())
    fun ifF() = Node.fresh(Operators.ifF())
    fun argument(extra: ArgumentOpExtra) = Node.fresh(Operators.argument(extra))
    fun freeVar(extra: FreeVarOpExtra) = Node.fresh(Operators.freeVar(extra))
    fun effect() = Node.fresh(Operators.effect())

    fun phi(nRegions: Int) = Node.fresh(Operators.phi(nRegions))
    fun effectPhi(nRegions: Int) = Node.fresh(Operators.effectPhi(nRegions))

    fun call(nArgs: Int) = Node.fresh(Operators.call(nArgs))

    fun boolLit(value: Boolean) = Node.fresh(Operators.boolLit(value))
    fun boxLit() = Node.fresh(Operators.boxLit())
    fun intLit(value: Int) = Node.fresh(Operators.fxLit(value))
    fun lambdaLit(nFreeVars: Int, graphId: GraphId) = Node.fresh(Operators.lambdaLit(nFreeVars, graphId))
    fun symbolLit(value: String) = Node.fresh(Operators.symbolLit(value))

    fun fxAdd() = Node.fresh(Operators.fxAdd())
    fun fxSub() = Node.fresh(Operators.fxSub())
    fun fxLessThan() = Node.fresh(Operators.fxLessThan())
    fun boxGet() = Node.fresh(Operators.boxGet())
    fun boxSet() = Node.fresh(Operators.boxSet())

    fun dead() = Node.fresh(Operators.dead())
}

object NodeIds {
    // Inputs / outputs
    val UNPOPULATED_ID = NodeId(-2)

    // Fresh node
    val FRESH_ID = NodeId(-1)
    val FIRST_ID_IN_GRAPH = NodeId(1)

    fun isValid(id: NodeId): Boolean {
        return id.v >= FIRST_ID_IN_GRAPH.v
    }
}

enum class EdgeKind {
    Value,
    Control;

    companion object {
        val ALL = values()
        val VALUE = arrayOf(Value)
        val CONTROL = arrayOf(Control)
    }
}

enum class EdgeDirection(val bitset: Int) {
    None(0),
    Input(1 shl 0),
    Output(1 shl 1),
    Both(Input.bitset or Output.bitset);

    val input: Boolean
        get() = bitset and Input.bitset == Input.bitset

    val output: Boolean
        get() = bitset and Output.bitset == Output.bitset
}


/**
 * @param nthInput The input index wrt to, i.e. to[kind, nthInput] == from
 */
data class Edge(val from: NodeId, val to: NodeId, val kind: EdgeKind, val nthInput: Int)

interface Graph {
    val multiGraph: MultiGraph
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