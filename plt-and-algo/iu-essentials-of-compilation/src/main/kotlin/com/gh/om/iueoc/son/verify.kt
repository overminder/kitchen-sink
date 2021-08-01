package com.gh.om.iueoc.son

class GraphVerifier(private val g: Graph) {
    private val visited = mutableSetOf<NodeId>()

    fun verifyFullyBuilt() {
        visited.clear()
        goNode(g.start)
        require(g.end in visited)
    }

    private fun verifyEdgeAndBackEdge(from: NodeId, to: NodeId, kind: EdgeKind) {
        val fromN = g[from]
        val toN = g[to]
        // |from->to| == |to<-from|
        val outputs = fromN.outputsByKind(kind)
        val f2t = outputs.count { it == to }
        val inputs = toN.inputsByKind(kind)
        val t2f = inputs.count { it == from }
        require(f2t == t2f)
        if (kind == EdgeKind.Control) {
            // Control edges should be no more than one
            require(f2t == 1)
        }
    }

    /**
     * Common invariants: all edges are valid, and the number of edges match the one stored in the operator.
     * Also verify that all the neighbours have correct back edges.
     */
    private fun verifyCommonInvariants(nid: NodeId) {
        val n = g[nid]
        require(n.id == nid)

        require(n.valueInputs.all { it.isValid })
        require(n.controlInputs.all { it.isValid })
        require(n.valueOutputs.all { it.isValid })
        require(n.controlInputs.all { it.isValid })

        require(n.valueInputs.size == n.operator.nValueIn)
        require(n.valueOutputs.size == n.operator.nValueOut)
        require(n.controlInputs.size == n.operator.nControlIn)
        require(n.controlOutputs.size == n.operator.nControlOut)

        n.valueOutputs.forEach {
            verifyEdgeAndBackEdge(nid, it, EdgeKind.Value)
        }
        n.controlOutputs.forEach {
            verifyEdgeAndBackEdge(nid, it, EdgeKind.Control)
        }

        if (n.opCode.isValueFixedWithNext) {
            require(n.controlInputs.size == 1)
            require(n.controlOutputs.size == 1)
        }
    }

    /**
     * @param [index] A null index means everything.
     */
    private fun checkInputBy(n: Node, index: Int?, kind: EdgeKind, predicate: (OpCode) -> Boolean) {
        val inputs = n.inputsByKind(kind)
        if (index != null) {
            val op = getOp(inputs[index])
            require(predicate(op))
        } else {
            inputs.forEach {
                val op = getOp(it)
                require(predicate(op))
            }
        }
    }

    private fun getOp(id: NodeId): OpCode = g[id].operator.op

    // Do operator-specific checks on the edges, but do not recursively visit the neighbour nodes.
    // The order is roughly interpretation order -- controls go down and values go up.
    // Hmm are we partially repeating what the operator definition is doing?
    private fun verifyEdgesByOpCode(n: Node) {
        when (val nodeOp = n.operator.op) {
            OpCode.Start -> {
                // Checks on value outputs are likely not needed...
                val valueOutputs = n.valueOutputs.map(::getOp)
                valueOutputs.forEach {
                    require(it == OpCode.Argument || it == OpCode.FreeVar)
                }
            }
            OpCode.End -> {
                // Done
            }
            OpCode.Merge -> {
                val cin = when (n.operator.extra as RegionKind) {
                    RegionKind.Merge -> 2
                    RegionKind.LoopHeader -> 2
                }
                require(n.controlInputs.size == cin)
                n.controlOutputs.map(::getOp).forEach {
                    require(it.hasControlInput)
                }
            }
            OpCode.Return -> {
                checkInputBy(n, 0, EdgeKind.Value) { it.isValue }
                checkInputBy(n, 0, EdgeKind.Control) { it.hasControlOutput }
                require(getOp(n.singleControlOutput) == OpCode.End)
            }
            OpCode.CondJump -> {
                checkInputBy(n, 0, EdgeKind.Value) { it.isValue }
                checkInputBy(n, 0, EdgeKind.Control) { it.hasControlOutput }
                require(n.controlOutputs.size == 2)
                n.controlOutputs.map(::getOp).forEach {
                    require(it == OpCode.ScmIfT || it == OpCode.ScmIfF)
                }
            }
            OpCode.ScmIfT,
            OpCode.ScmIfF -> {
                checkInputBy(n, 0, EdgeKind.Control) { it == OpCode.CondJump }
            }
            OpCode.Argument,
            OpCode.FreeVar -> {
                checkInputBy(n, 0, EdgeKind.Value) { it == OpCode.Start }
            }
            OpCode.Phi -> {
                checkInputBy(n, 0, EdgeKind.Control) { it == OpCode.Merge }
                val region = g[n.singleControlInput]
                require(n.valueInputs.size == region.controlInputs.size)
                n.valueInputs.forEach {
                    val inputOp = getOp(it)
                    require(inputOp.isValue)
                }
            }
            OpCode.Call -> {
                checkInputBy(n, 0, EdgeKind.Control) { it.hasControlOutput }
                require(n.valueOutputs.isNotEmpty())
            }
            OpCode.ScmBoolLit,
            OpCode.ScmFxLit,
            OpCode.ScmSymbolLit -> {
                require(n.valueInputs.isEmpty())
            }
            OpCode.ScmBoxLit,
            OpCode.ScmLambdaLit,
            OpCode.ScmBoxGet,
            OpCode.ScmBoxSet,
            OpCode.ScmFxAdd,
            OpCode.ScmFxSub,
            OpCode.ScmFxLessThan -> {
                checkInputBy(n, null, EdgeKind.Value) { it.isValue }
            }
            OpCode.Dead -> {
                error("Shouldn't be connected to the graph?")
            }
            else -> {
                error("Not implemented: $nodeOp")
            }
        }
    }

    // Verify by checking basic invariants and opcode specific edges
    private fun goNode(nid: NodeId) {
        if (nid in visited) {
            return
        }
        visited += nid
        verifyCommonInvariants(nid)
        val n = g[nid]
        verifyEdgesByOpCode(n)
        n.valueInputs.forEach(::goNode)
        n.controlInputs.forEach(::goNode)
        n.valueOutputs.forEach(::goNode)
        n.controlOutputs.forEach(::goNode)
    }
}

fun Graph.verifyNodeIds(startingFrom: Int = 0) {
    nodes.asSequence().withIndex().drop(startingFrom).forEach { (ix, node) ->
        require(ix == node.id.asIx)
    }
}
