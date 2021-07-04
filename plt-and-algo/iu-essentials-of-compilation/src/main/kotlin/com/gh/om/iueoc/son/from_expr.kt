package com.gh.om.iueoc.son

import com.gh.om.iueoc.AnnExpr
import com.gh.om.iueoc.ExprOp
import com.gh.om.iueoc.ExprVar

// Data class for hashcode and equals
private data class ValueNodeEqWrapper(
    val opCode: OpCode,
    val parameter: Any?,
    // Looks really inefficient lol
    val inputs: Set<NodeId>
)

// Freshly created nodes are not inserted into the graph yet:
// - No valid id
// - Inputs / outputs not yet populated.
// Steps to insert a node:
// 1. For value nodes: populate the inputs, and do GVN. If GVN returns an existing one, use that.
//    Otherwise assign an Id to this fresh node, put into GVN cache, and use it.
// 2. For control nodes: (partially) populate its inputs and outputs, and we are good.

class GraphBuilder: Graph {
    private var idGen: Int = NodeIds.FIRST_ID_IN_GRAPH
    private fun nextId(): Int {
        return idGen++
    }

    override val nodes: MutNodeMap = mutableMapOf()

    override val start: NodeId
    override val end: NodeId

    // Although nodes are mutable, we don't mutate value nodes during graph building.
    private val gvnCache = mutableMapOf<ValueNodeEqWrapper, NodeId>()

    private var currentRegion: NodeId? = null

    init {
        start = assignId(Nodes.start())
        end = assignId(Nodes.end())
    }

    private fun startRegion(nPhis: Int): Node {
        require(currentRegion == null)
        val region = Nodes.region(nPhis)
        currentRegion = assignId(region)
        return region
    }

    fun doFunctionBody(annE: AnnExpr) {
        startRegion(0).addInput(get(start), EdgeKind.Control, populating = true)

        val returnValue = get(doExpr(annE))
        val exitRegion = get(requireNotNull(currentRegion))

        val returnNode = Nodes.ret()
        assignId(returnNode)
        returnNode.addInput(returnValue, EdgeKind.Value, populating = true)
        returnNode.addInput(exitRegion, EdgeKind.Control, populating = true)

        get(end).addInput(returnNode, EdgeKind.Control, populating = true)
    }

    fun doExpr(annE: AnnExpr): NodeId {
        return when (val e = annE.unwrap) {
            is ExprOp.If -> TODO()
            is ExprOp.Let -> TODO()
            is ExprOp.Op -> TODO()
            is ExprVar.B -> TODO()
            is ExprVar.I -> {
                tryGvn(Nodes.int(e.value))
            }
            is ExprVar.Sym -> TODO()
            is ExprVar.V -> TODO()
        }
    }

    private fun assignId(node: Node): NodeId {
        node.assignId(nextId())
        nodes[node.id] = node
        return node.id
    }

    private fun tryGvn(n: Node): NodeId {
        val rator = n.operator
        require(rator.op.isPure)
        val key = ValueNodeEqWrapper(rator.op, rator.parameter, n.valueInputs.toSet())
        val cached = gvnCache[key]
        return if (cached == null) {
            // Save to cache.
            gvnCache[key] = assignId(n)
            n.id
        } else {
            cached
        }
    }
}

class GraphVerifier(private val g: Graph) {
    fun verifyFullyBuilt() {
        val visited = mutableSetOf<NodeId>()
        goNode(g.start, ExecutionState.StartGraph, visited)
        require(g.end in visited)
    }

    private fun verifyEdgeExists(from: NodeId, to: NodeId, kind: EdgeKind) {
        val (getIn, getOut) = when (kind) {
            EdgeKind.Value -> Node::valueInputs to Node::valueOutputs
            EdgeKind.Control -> Node::controlInputs to Node::controlOutputs
        }
        val fromN = g[from]
        val toN = g[to]
        require(getOut(fromN).count { it == to } == 1)
        require(getIn(toN).count { it == from } == 1)
    }

    private fun verifyEdges(nid: NodeId) {
        val n = g[nid]

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

    // Verify as in interpreting the nodes.
    private fun goNode(nid: NodeId, estate: ExecutionState, visited: MutableSet<NodeId>) {
        if (nid in visited) {
            return
        }
        visited += nid
        verifyEdges(nid)
        val n = g[nid]
        return when (n.operator.op) {
            OpCode.Start -> {
                require(estate == ExecutionState.StartGraph)

                goNode(n.singleControlOutput, ExecutionState.StartRegion, visited)
            }
            OpCode.Region -> {
                require(estate == ExecutionState.StartRegion)

                n.controlOutputs.forEach {
                    val co = g[it]
                    if (co.operator.op == OpCode.Phi) {
                        goNode(it, ExecutionState.Value, visited)
                    } else {
                        goNode(it, ExecutionState.EndRegion, visited)
                    }
                }
            }
            OpCode.End -> {
                require(estate == ExecutionState.StartRegion)
                // Done
            }
            OpCode.Return -> {
                require(estate == ExecutionState.EndRegion)

                goNode(n.singleValueInput, ExecutionState.Value, visited)

                val end = g[n.singleControlOutput]
                require(end.operator.op == OpCode.End)
                goNode(n.singleControlOutput, ExecutionState.StartRegion, visited)
            }
            OpCode.CondJump -> {
                require(estate == ExecutionState.EndRegion)

                n.controlOutputs.forEach {
                    goNode(it, ExecutionState.ProjCondJump, visited)
                }
            }
            OpCode.Phi -> {
                require(estate == ExecutionState.Value)

                val region = g[n.singleControlInput]
                require(n.valueInputs.size == region.controlInputs.size)
                n.valueInputs.forEach {
                    goNode(it, ExecutionState.Value, visited)
                }
            }
            OpCode.IntLit -> {
                require(estate == ExecutionState.Value)
            }
            OpCode.IntAdd, OpCode.IntLessThan -> {
                require(estate == ExecutionState.Value)
                n.valueInputs.forEach {
                    goNode(it, ExecutionState.Value, visited)
                }
            }
            OpCode.IfT, OpCode.IfF -> {
                require(estate == ExecutionState.ProjCondJump)
                goNode(n.singleControlOutput, ExecutionState.StartRegion, visited)
            }
        }
    }
}

private enum class ExecutionState {
    StartGraph,
    StartRegion,
    EndRegion,
    ProjCondJump,
    Value,
}

enum class EdgeKind {
    Value,
    Control,
}

private fun main() {
    val gb = GraphBuilder()
    GraphVerifier(gb).verifyFullyBuilt()
    println("Ok")
}
