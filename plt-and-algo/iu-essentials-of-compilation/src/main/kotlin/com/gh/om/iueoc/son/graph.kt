package com.gh.om.iueoc.son

import com.gh.om.iueoc.SourceLoc
import com.gh.om.iueoc.algo.GraphCap

// Sea of nodes graph.
// Graph has a start and an end, and maintains a NodeId -> Node mapping.
// MutGraph provides a general purpose interface for editing nodes and edges.
// GraphCollection maintains a GraphId -> Graph mapping.
// MutGraphCollection allows editing the mapping.

@JvmInline value class GraphId(private val v: Int) {
    fun next() = GraphId(v + 1)
    fun diff(other: GraphId): Int = other.v - v
    override fun toString() = v.toString()

    companion object {
        val FIRST_ID = GraphId(1)
    }
}

interface Graph {
    // The ID in the multiGraph
    val id: GraphId

    // Debug information
    val name: String?
    val sourceLoc: SourceLoc?

    // args / freevars may be optimized away by DCE. Need to keep a record here.
    // In general we need to record the signature.
    val argCount: Int
    val freeVarCount: Int

    // The compilation unit
    val owner: GraphCollection

    // Known anchors
    val start: NodeId
    val end: NodeId
    val nodes: List<Node>

    companion object {
        operator fun get(nodes: List<Node>, id: NodeId): Node {
            return requireNotNull(nodes.getOrNull(id.asIx)) {
                "$id doesn't exist. All nodes: ${nodes.size}"
            }
        }
    }
}

operator fun Graph.get(id: NodeId): Node {
    return Graph[nodes, id]
}

class IdGenerator<A>(initial: A, private val next: (A) -> A) {
    private var state = initial

    operator fun invoke(): A {
        val returnValue = state
        state = next(state)
        return returnValue
    }
}

class GraphBuilderState(private val graph: MutGraph) {
    private val pureValueCache = mutableMapOf<ValueNodeEqWrapper, NodeId>()

    // An anchor or a fixed node (e.g. call)
    var currentControlDep: NodeId = graph.start

    fun makeMergeNode(nPreds: Int, nPhis: Int, kind: RegionKind): Node {
        val region = Nodes.merge(nPreds = nPreds, nPhis = nPhis, kind = kind)
        currentControlDep = graph.assignId(region).id
        return region
    }

    fun assertCurrentControlDep(): Node {
        return graph[currentControlDep]
    }

    fun threadControlFrom(node: Node): Node {
        require(node.opCode.isValueFixedWithNext)
        node.populateInput(assertCurrentControlDep(), EdgeKind.Control)
        currentControlDep = node.id
        return node
    }

    fun joinControlFlow(
        tValue: NodeId,
        fValue: NodeId,
        tJump: Node,
        fJump: Node
    ): NodeId {
        val needPhi = tValue != fValue
        // Make a region as a join point
        // Both branches may be returning the same thing. In that case we don't need a phi.
        val mergeNode = makeMergeNode(nPreds = 2, nPhis = needPhi.b2i, kind = RegionKind.Merge)
        mergeNode.populateInput(tJump, EdgeKind.Control)
        mergeNode.populateInput(fJump, EdgeKind.Control)
        return if (needPhi) {
            val phi = graph.assignId(Nodes.phi(2))
            phi.populateInput(mergeNode, EdgeKind.Control)
            phi.populateInput(graph[tValue], EdgeKind.Value)
            phi.populateInput(graph[fValue], EdgeKind.Value)
            phi.id
        } else {
            tValue
        }
    }

    fun makeUniqueValueNode(n: Node, valueInputs: List<NodeId> = emptyList()): NodeId {
        val rator = n.operator
        require(rator.op.isPure)
        val key = ValueNodeEqWrapper(rator.op, rator.extra, valueInputs)
        val cached = pureValueCache[key]
        return if (cached == null) {
            // Save to cache.
            pureValueCache[key] = graph.assignId(n).id
            // Populate edges
            valueInputs.forEach {
                n.populateInput(graph[it], EdgeKind.Value)
            }
            n.id
        } else {
            cached
        }
    }

    fun makeEffectfulValueNode(n: Node, valueInputs: List<NodeId> = emptyList()): Node {
        graph.assignId(n)
        valueInputs.forEach {
            n.populateInput(graph[it], EdgeKind.Value)
        }
        threadControlFrom(n)
        return n
    }
}

class MutGraph private constructor(
    override val id: GraphId,
    override val name: String?,
    override val sourceLoc: SourceLoc?,
    override val owner: MutGraphCollection,
) : Graph {
    override val start
        get() = requireNotNull(mutStart)
    override val end
        get() = requireNotNull(mutEnd)
    override val nodes get(): List<Node> = mutNodes

    private val nextId = IdGenerator(NodeIds.FIRST_ID_IN_GRAPH, NodeId::next)
    private var mutNodes = mutableListOf<Node>()
    private var mutStart: NodeId? = null
    private var mutEnd: NodeId? = null

    override var argCount: Int = -1
        private set

    override var freeVarCount: Int = -1
        private set

    companion object {
        fun make(
            id: GraphId,
            name: String?,
            sourceLoc: SourceLoc?,
            owner: MutGraphCollection,
        ): MutGraph {
            val out = MutGraph(id, name, sourceLoc, owner)
            out.initAnchors()
            return out
        }
    }

    private fun initAnchors() {
        mutStart = assignId(Nodes.start()).id
        mutEnd = assignId(Nodes.end()).id
    }

    fun assignId(node: Node): Node {
        node.assignId(nextId())
        return add(node)
    }

    fun copyFrom(ns: Sequence<Node>, idMap: MutableMap<NodeId, NodeId> = mutableMapOf()): MutableMap<NodeId, NodeId> {
        val toAdd = mutableListOf<Node>()
        for (n in ns) {
            val copy = n.deepCopyMapped {
                idMap.getOrPut(it, nextId::invoke)
            }
            toAdd += copy
        }
        // Every node assigned an ID is added. That is, there's no unreachable node.
        require(toAdd.size == idMap.size)
        // Sort and then add, so that each newly added node is assigned the correct ID.
        toAdd.sortBy { it.id.asIx }
        val sizeBefore = nodes.size
        mutNodes += toAdd
        verifyNodeIds(sizeBefore)
        return idMap
    }

    // Empty as in only copying the metadata.
    fun makeEmptyCopy(initAnchors: Boolean = false): MutGraph {
        val out = MutGraph(id, name, sourceLoc, owner)
        out.populateSignature(argCount, freeVarCount)
        if (initAnchors) {
            out.initAnchors()
        }
        return out
    }

    fun setAnchors(start: NodeId, end: NodeId) {
        mutStart = start
        mutEnd = end
    }

    fun populateSignature(argCount: Int, freeVarCount: Int) {
        this.argCount = argCount
        this.freeVarCount = freeVarCount
    }

    val ref get() = MutGraphRef(id, owner)

    private fun add(node: Node, checkSize: Boolean = true): Node {
        if (checkSize) {
            require(node.id.asIx == nodes.size)
        }
        mutNodes.add(node)
        return node
    }
}

val NodeId.asIx: Int
    get() = NodeIds.FIRST_ID_IN_GRAPH.diff(this)

val GraphId.asIx: Int
    get() = GraphId.FIRST_ID.diff(this)

interface GraphCollection {
    val graphs: List<Graph>
}

val GraphCollection.graphIds: List<GraphId>
    get() = graphs.map { it.id }

operator fun GraphCollection.get(graphId: GraphId): Graph {
    return requireNotNull(graphs.getOrNull(graphId.asIx)) {
        "$graphId not found. All ids: ${graphs.size}"
    }
}

class MutGraphCollection : GraphCollection {
    override val graphs get(): List<Graph> = mutGraphs

    private val mutGraphs = mutableListOf<MutGraph>()
    private val nextId = IdGenerator(GraphId.FIRST_ID, GraphId::next)

    fun add(build: (GraphId) -> MutGraph): MutGraph {
        val id = nextId()
        require(id.asIx == graphs.size)
        val graph = build(id)
        mutGraphs.add(graph)
        return graph
    }

    fun replace(from: MutGraph, to: MutGraph) {
        require(from.id == to.id)
        val ix = from.id.asIx
        require(mutGraphs[ix] === from)
        mutGraphs[ix] = to
    }

    operator fun get(graphId: GraphId): MutGraph {
        return requireNotNull(mutGraphs.getOrNull(graphId.asIx)) {
            "$graphId not found. All ids: ${graphs.size}"
        }
    }
}

// Is a data class for hashcode and equals
private data class ValueNodeEqWrapper(
    val opCode: OpCode,
    val parameter: Any?,
    // Looks really inefficient lol
    // Ordering is important -- `a - b` is not the same as `b - a`.
    val inputs: List<NodeId>
)

class MutGraphRef(val id: GraphId, val gs: MutGraphCollection) {
    val g: MutGraph
        get() = gs[id]
}

private val Boolean.b2i: Int
    get() = if (this) 1 else 0

object ControlFlowGraphCap : GraphCap<Graph, NodeId> {
    override fun predecessors(g: Graph, id: Int): List<Int> {
        return g.nodes[id].controlInputs.map { nodeToId(g, it) }
    }

    override fun successors(g: Graph, id: Int): List<Int> {
        return g.nodes[id].controlOutputs.map { nodeToId(g, it) }
    }

    override fun nodeToId(g: Graph, n: NodeId): Int {
        return n.asIx
    }

    override fun size(g: Graph): Int {
        return g.nodes.size
    }

    override fun idToNode(g: Graph, id: Int): NodeId {
        return g.nodes[id].id
    }

    override fun hasNodeId(g: Graph, id: Int): Boolean {
        return 0 <= id && id < size(g)
    }
}