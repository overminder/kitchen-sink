package com.gh.om.iueoc.son

import com.gh.om.iueoc.SourceLoc

// Sea of nodes graph.
// Graph has a start and an end, and maintains a NodeId -> Node mapping.
// MutableGraph provides a general purpose interface for editing nodes and edges.
// MultiGraph is a collection of graphs.
// MutableMultiGraph allows editing graphs.

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

    // The compilation unit
    val owner: GraphCollection

    // Known anchors
    val start: NodeId
    val end: NodeId
    val nodes: List<Node>
}

operator fun Graph.get(id: NodeId): Node {
    return requireNotNull(nodes.getOrNull(id.asIx)) {
        "$id doesn't exist. All nodes: ${nodes.size}"
    }
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

    // A region or a fixed node (e.g. call)
    private var currentControlDep: NodeId? = null
    var currentEffect: NodeId

    init {
        val eff = graph.assignId(Nodes.effect())
        eff.populateInput(graph[graph.start], EdgeKind.Value)
        currentEffect = eff.id
    }

    fun startRegion(nPreds: Int = 1, nPhis: Int = 0, kind: RegionKind = RegionKind.Basic): Node {
        // require(currentRegion == null)
        val region = Nodes.region(nPreds = nPreds, nPhis = nPhis, kind = kind)
        currentControlDep = graph.assignId(region).id
        return region
    }

    fun assertCurrentControlDep(): Node {
        return graph[requireNotNull(currentControlDep)]
    }

    fun assertCurrentEffect(): Node {
        return graph[currentEffect]
    }

    private fun projectEffectFrom(node: Node): Node {
        val updatedEffect = graph.assignId(Nodes.effect())
        updatedEffect.populateInput(node, EdgeKind.Value)
        currentEffect = updatedEffect.id
        return node
    }

    fun threadControlFrom(node: Node): Node {
        require(node.opCode.isFixedWithNext)
        node.populateInput(assertCurrentControlDep(), EdgeKind.Control)
        currentControlDep = node.id
        return node
    }

    fun joinControlFlow(
        tValue: NodeId,
        tEffect: NodeId,
        fValue: NodeId,
        fEffect: NodeId,
        tJump: Node,
        fJump: Node
    ): NodeId {
        val needPhi = tValue != fValue
        val needEffectPhi = tEffect != fEffect
        // Make a region as a join point
        // Both branches may be returning the same thing. In that case we don't need a phi.
        val joinRegion = startRegion(nPreds = 2, nPhis = needPhi.b2i + needEffectPhi.b2i, kind = RegionKind.Merge)
        joinRegion.populateInput(tJump, EdgeKind.Control)
        joinRegion.populateInput(fJump, EdgeKind.Control)
        if (needEffectPhi) {
            val effectPhi = graph.assignId(Nodes.effectPhi(2))
            effectPhi.populateInput(joinRegion, EdgeKind.Control)
            effectPhi.populateInput(graph[tEffect], EdgeKind.Value)
            effectPhi.populateInput(graph[fEffect], EdgeKind.Value)
            currentEffect = effectPhi.id
        }
        return if (needPhi) {
            val phi = graph.assignId(Nodes.phi(2))
            phi.populateInput(joinRegion, EdgeKind.Control)
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
        n.populateInput(assertCurrentEffect(), EdgeKind.Value)
        valueInputs.forEach {
            n.populateInput(graph[it], EdgeKind.Value)
        }
        projectEffectFrom(n)
        return n
    }
}

class MutGraph(
    override val id: GraphId,
    override val name: String?,
    override val sourceLoc: SourceLoc?,
    override val owner: MutGraphCollection,
) : Graph {
    override val start: NodeId
    override val end: NodeId
    override val nodes get(): List<Node> = mutNodes
    val dead: NodeId

    private val nextId = IdGenerator(NodeIds.FIRST_ID_IN_GRAPH, NodeId::next)
    private val mutNodes = mutableListOf<Node>()

    init {
        start = assignId(Nodes.start()).id
        end = assignId(Nodes.end()).id
        dead = assignId(Nodes.dead()).id
    }

    fun assignId(node: Node): Node {
        node.assignId(nextId())
        return add(node)
    }

    private fun add(node: Node, checkSize: Boolean = true): Node {
        if (checkSize) {
            require(node.id.asIx == nodes.size)
        }
        mutNodes.add(node)
        return node
    }

    fun makeCopies(ns: Sequence<Node>, idMap: MutableMap<NodeId, NodeId>) {
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
    }
}

val NodeId.asIx: Int
    get() = NodeIds.FIRST_ID_IN_GRAPH.diff(this)

val GraphId.asIx: Int
    get() = GraphId.FIRST_ID.diff(this)

interface GraphCollection {
    val graphs: List<Graph>
}

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
}

// Is a data class for hashcode and equals
private data class ValueNodeEqWrapper(
    val opCode: OpCode,
    val parameter: Any?,
    // Looks really inefficient lol
    // Ordering is important -- `a - b` is not the same as `b - a`.
    val inputs: List<NodeId>
)

private val Boolean.b2i: Int
    get() = if (this) 1 else 0
