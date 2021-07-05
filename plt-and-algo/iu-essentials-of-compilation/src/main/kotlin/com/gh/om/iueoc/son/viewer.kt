package com.gh.om.iueoc.son

import java.io.Writer

// Graph -> dot
// See: https://graphviz.org/doc/info/attrs.html
// https://renenyffenegger.ch/notes/tools/Graphviz/attributes/style
// http://magjac.com/graphviz-visual-editor/

private data class Edge(val from: NodeId, val to: NodeId, val kind: EdgeKind, val nthInput: Int)

fun graphToDot(g: Graph, out: Writer) {
    // Header
    out.appendLine("digraph {")

    val gtd = GraphToDot(g, out)
    gtd.visitNode(g.start)

    out.appendLine("}")
}

private class GraphToDot(val g: Graph, val out: Writer) {
    val visitedNodes = mutableSetOf<NodeId>()
    val visitedEdges = mutableSetOf<Edge>()

    fun visitEdge(edge: Edge, onlyOneEdge: Boolean) {
        if (edge in visitedEdges) {
            return
        }
        visitedEdges += edge
        visitNode(edge.from)
        visitNode(edge.to)

        // (edge label?)
        val edgeChar = when (edge.kind) {
            EdgeKind.Value -> "V"
            EdgeKind.Control -> "C"
        }
        val labelPart = if (onlyOneEdge) {
            ""
        } else {
            "label=\"$edgeChar:${edge.nthInput}\""
        }
        val args = when (edge.kind) {
            EdgeKind.Value -> "style=dotted $labelPart arrowhead=onormal"
            EdgeKind.Control -> "style=solid $labelPart"
        }
        out.appendLine("  ${edge.from} -> ${edge.to} [$args]")
    }

    fun visitNode(id: NodeId) {
        if (id in visitedNodes) {
            return
        }
        visitedNodes += id

        val n = g[id]
        val op = n.operator.op
        val param = n.operator.parameter
        val label = if (param != null && param != Unit) {
            "\"$op $param\""
        } else {
            "$op"
        }
        val shapePart = when (op.klass) {
            OpCodeClass.Anchor -> "shape=box"
            OpCodeClass.Jump -> "shape=hexagon"
            OpCodeClass.Projection -> "shape=cds"
            OpCodeClass.Phi -> "shape=oval"
            OpCodeClass.Value -> "shape=oval style=dotted"
        }
        out.appendLine("  $id [label=$label $shapePart]")

        // TODO: generalize this?
        n.valueInputs.forEachIndexed { index, input ->
            visitEdge(Edge(input, id, EdgeKind.Value, index), n.valueInputs.size == 1)
        }
        n.controlInputs.forEachIndexed { index, input ->
            visitEdge(Edge(input, id, EdgeKind.Control, index), n.controlInputs.size == 1)
        }
        // The edge will be visited as an input edge, so that we get the correct input index for free.
        n.valueOutputs.forEach(::visitNode)
        n.controlOutputs.forEach(::visitNode)
    }
}


