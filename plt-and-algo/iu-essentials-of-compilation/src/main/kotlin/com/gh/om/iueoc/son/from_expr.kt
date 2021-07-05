package com.gh.om.iueoc.son

import com.gh.om.iueoc.AnnExpr
import com.gh.om.iueoc.EocError
import com.gh.om.iueoc.ExprLam
import com.gh.om.iueoc.ExprOp
import com.gh.om.iueoc.ExprVar
import com.gh.om.iueoc.PrimOp
import com.gh.om.iueoc.SourceLoc

// Data class for hashcode and equals
private data class ValueNodeEqWrapper(
    val opCode: OpCode,
    val parameter: Any?,
    // Looks really inefficient lol
    // Ordering is important -- `a - b` is not the same as `b - a`.
    val inputs: List<NodeId>
)

// Freshly created nodes are not inserted into the graph yet:
// - No valid id
// - Inputs / outputs not yet populated.
// Steps to insert a node:
// 1. For value nodes: populate the inputs, and do GVN. If GVN returns an existing one, use that.
//    Otherwise assign an Id to this fresh node, put into GVN cache, and use it.
// 2. For control nodes: (partially) populate its inputs and outputs, and we are good.

class EnvChain(
    private val bindings: MutableMap<String, NodeId> = mutableMapOf(),
    private val parent: EnvChain? = null
) {
    fun extend(newBindings: MutableMap<String, NodeId>): EnvChain {
        return EnvChain(newBindings, this)
    }

    operator fun get(name: String, loc: SourceLoc): NodeId {
        var here: EnvChain = this
        while (true) {
            val value = here.bindings[name]
            if (value == null) {
                val next = here.parent
                EocError.ensure(next != null, loc) { "Unbound var $name" }
                here = next
            } else {
                return value
            }
        }
    }
}

class GraphBuilder : Graph {
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

    private fun startRegion(nPreds: Int = 1, nPhis: Int = 0): Node {
        // require(currentRegion == null)
        val region = Nodes.region(nPreds = nPreds, nPhis = nPhis)
        currentRegion = assignId(region)
        return region
    }

    private fun assertCurrentRegion(): NodeId {
        return requireNotNull(currentRegion)
    }

    fun doFunctionBody(annE: AnnExpr) {
        startRegion().addInput(get(start), EdgeKind.Control, populating = true)

        val returnValue = get(doExpr(annE, EnvChain()))
        val exitRegion = get(assertCurrentRegion())

        val returnNode = Nodes.ret()
        assignId(returnNode)
        returnNode.addInput(returnValue, EdgeKind.Value, populating = true)
        returnNode.addInput(exitRegion, EdgeKind.Control, populating = true)

        get(end).addInput(returnNode, EdgeKind.Control, populating = true)
    }

    fun doExpr(annE: AnnExpr, env: EnvChain): NodeId {
        return when (val e = annE.unwrap) {
            is ExprOp.If -> {
                // Hmm is this correct?

                // Evaluate condValue, set up condJump
                val condValue = doExpr(e.cond, env)
                val condJump = Nodes.condJump().also(::assignId)
                condJump.addInput(get(condValue), EdgeKind.Value, populating = true)
                condJump.addInput(get(assertCurrentRegion()), EdgeKind.Control, populating = true)

                // Make projections
                val ifT = Nodes.ifT().also(::assignId)
                val ifF = Nodes.ifF().also(::assignId)
                ifT.addInput(condJump, EdgeKind.Control, populating = true)
                ifF.addInput(condJump, EdgeKind.Control, populating = true)

                // True branch
                startRegion().addInput(ifT, EdgeKind.Control, populating = true)
                val tValue = doExpr(e.ifT, env)
                val tValueRegion = assertCurrentRegion()
                val tJump = Nodes.jump().also(::assignId)
                tJump.addInput(get(tValueRegion), EdgeKind.Control, populating = true)

                // False branch
                startRegion().addInput(ifF, EdgeKind.Control, populating = true)
                val fValue = doExpr(e.ifF, env)
                val fValueRegion = assertCurrentRegion()
                val fJump = Nodes.jump().also(::assignId)
                fJump.addInput(get(fValueRegion), EdgeKind.Control, populating = true)

                // Join point
                // Merge node may be able to simplify the structure.
                // Both branches may be returning the same thing. In that case we don't need a phi.
                val needPhi = tValue != fValue
                val joinRegion = startRegion(nPreds = 2, nPhis = if (needPhi) 1 else 0)
                joinRegion.addInput(tJump, EdgeKind.Control, populating = true)
                joinRegion.addInput(fJump, EdgeKind.Control, populating = true)
                if (needPhi) {
                    val phi = Nodes.phi(2).also(::assignId)
                    phi.addInput(joinRegion, EdgeKind.Control, populating = true)
                    phi.addInput(get(tValue), EdgeKind.Value, populating = true)
                    phi.addInput(get(fValue), EdgeKind.Value, populating = true)
                    phi.id
                } else {
                    tValue
                }
            }
            is ExprOp.Let -> {
                val newBindings = e.vs.zip(e.es).associateTo(mutableMapOf()) { (name, rhs) ->
                    val value = doExpr(rhs, env)
                    name.unwrap to value
                }
                doExpr(e.body, env.extend(newBindings))
            }
            is ExprOp.Op -> {
                val values = e.args.map { doExpr(it, env) }
                when (e.op.unwrap) {
                    PrimOp.FxAdd -> {
                        tryGvn(Nodes.intAdd(), values)
                    }
                    PrimOp.FxLessThan -> {
                        tryGvn(Nodes.intLessThan(), values)
                    }
                }
            }
            is ExprVar.B -> {
                tryGvn(Nodes.boolLit(e.value))
            }
            is ExprVar.I -> {
                tryGvn(Nodes.intLit(e.value))
            }
            is ExprVar.Sym -> {
                tryGvn(Nodes.symbolLit(e.name))
            }
            is ExprVar.V -> env[e.name, annE.ann]
            is ExprLam.Ap, is ExprLam.Lam -> {
                EocError.todo(annE.ann, "Not implemented: $e")
            }
        }
    }

    private fun assignId(node: Node): NodeId {
        node.assignId(nextId())
        nodes[node.id] = node
        return node.id
    }

    /**
     * Try to use an existing value node from the graph. The value node should be pure.
     * [n] should be fresh, and its [valueInputs] are inserted to [n] by this function.
     */
    private fun tryGvn(n: Node, valueInputs: List<NodeId> = emptyList()): NodeId {
        val rator = n.operator
        require(rator.op.isPure)
        val key = ValueNodeEqWrapper(rator.op, rator.parameter, valueInputs)
        val cached = gvnCache[key]
        return if (cached == null) {
            // Save to cache.
            gvnCache[key] = assignId(n)
            // Populate edges
            valueInputs.forEach {
                n.addInput(get(it), EdgeKind.Value, populating = true)
            }
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
        // |from->to| == |to<-from|
        val f2t = getOut(fromN).count { it == to }
        val t2f = getIn(toN).count { it == from }
        require(f2t == t2f)
        if (kind == EdgeKind.Control) {
            // Control edges should be no more than one
            require(f2t == 1)
        }
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
                require(estate == ExecutionState.Returned)
                // Done
            }
            OpCode.Return -> {
                require(estate == ExecutionState.EndRegion)

                goNode(n.singleValueInput, ExecutionState.Value, visited)

                val end = g[n.singleControlOutput]
                require(end.operator.op == OpCode.End)
                goNode(n.singleControlOutput, ExecutionState.Returned, visited)
            }
            OpCode.CondJump -> {
                require(estate == ExecutionState.EndRegion)

                n.controlOutputs.forEach {
                    goNode(it, ExecutionState.ProjCondJump, visited)
                }
            }
            OpCode.Jump -> {
                require(estate == ExecutionState.EndRegion)

                goNode(n.singleControlOutput, ExecutionState.StartRegion, visited)
            }
            OpCode.Phi -> {
                require(estate == ExecutionState.Value)

                val region = g[n.singleControlInput]
                require(n.valueInputs.size == region.controlInputs.size)
                n.valueInputs.forEach {
                    goNode(it, ExecutionState.Value, visited)
                }
            }
            OpCode.ScmBoolLit,
            OpCode.ScmSymbolLit,
            OpCode.ScmFxLit -> {
                require(estate == ExecutionState.Value)
            }
            OpCode.ScmFxAdd, OpCode.ScmFxLessThan -> {
                require(estate == ExecutionState.Value)
                n.valueInputs.forEach {
                    goNode(it, ExecutionState.Value, visited)
                }
            }
            OpCode.ScmIfT, OpCode.ScmIfF -> {
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
    Returned,
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
