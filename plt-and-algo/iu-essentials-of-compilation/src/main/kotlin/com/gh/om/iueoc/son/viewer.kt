package com.gh.om.iueoc.son

import java.io.Writer

// Graph -> dot
// See: https://graphviz.org/doc/info/attrs.html
// https://renenyffenegger.ch/notes/tools/Graphviz/attributes/style (Lots of examples!)
// http://magjac.com/graphviz-visual-editor/

// xdot.py seems to hang for > 600 nodes...
fun graphsToDot(gs: GraphCollection, out: Writer) {
    out.appendLine("digraph {")
    gs.graphs.forEach { g ->
        val gid = g.id
        val locPart = g.sourceLoc?.let {
            "at line ${it.row}"
        } ?: "at ?"
        val name = listOfNotNull("G:${gid}", g.name, locPart).joinToString()
        graphToDot(g, out, "\"$name\"")
    }
    out.appendLine("}")
}

private fun graphToDot(g: Graph, out: Writer, name: String? = null) {
    // Header
    out.appendLine("subgraph cluster_${g.id} {")
    name?.let {
        out.appendLine("  label = $name")
        out.appendLine("  labelloc = top")
    }

    val gtd = GraphToDot(g, out)
    gtd.visitNode(g.start)
    out.appendLine("}")
}

private class GraphToDot(val g: Graph, val out: Writer) {
    val visitedNodes = mutableSetOf<NodeId>()
    val visitedEdges = mutableSetOf<Edge>()

    // Id as in the identifier in the dot language.
    private fun ident(id: NodeId): String {
        return "\"${g.id}_${id}\""
    }

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
        out.appendLine("  ${ident(edge.from)} -> ${ident(edge.to)} [$args]")
    }

    fun visitNode(id: NodeId) {
        if (id in visitedNodes) {
            return
        }
        visitedNodes += id

        if (!id.isValid) {
            // Still want to render it.
            out.appendLine("  ${ident(id)} [label=Invalid]")
            return
        }
        val n = g[id]
        val op = n.operator.op
        val param = n.operator.extra
        val label = if (param != null && param != Unit) {
            "\"$id $op $param\""
        } else {
            "\"$id $op\""
        }
        // TODO: Classify the nodes in a better way. Also add colors.
        val shapePart = when (op.klass) {
            OpCodeClass.Anchor -> "shape=box"
            OpCodeClass.Jump -> "shape=hexagon"
            OpCodeClass.Projection -> "shape=cds"
            OpCodeClass.Phi -> "shape=oval"
            OpCodeClass.FixedValue,
            OpCodeClass.Value -> "shape=oval style=dotted"
            OpCodeClass.Misc -> "shape=box style=dotted"
        }
        out.appendLine("  ${ident(id)} [label=$label $shapePart]")

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


