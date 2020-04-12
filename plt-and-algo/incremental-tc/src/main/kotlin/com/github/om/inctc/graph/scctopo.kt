package com.github.om.inctc.graph

sealed class GraphAlgoError: RuntimeException()

class HasCycles: GraphAlgoError()

object GraphAlgo

// http://theory.stanford.edu/~tim/w11/l/scc.pdf
fun <N: Any> GraphAlgo.sccKosaraju(g: DAG<N, *>): List<List<NodeId<N>>> {
    if (g.isEmpty) {
        return emptyList()
    }

    // Step 1: Assign post order to transposed graph.
    val postOrder = mutableSetOf<NodeId<N>>()
    for (n in g.nodes) {
        if (postOrder.contains(n)) {
            continue
        }
        // Don't actually need to transpose the graph, since we already store the predecessors.
        GraphTraversal.dfs(n, g, GraphTraversal.Order.Post, GraphTraversal.Direction.Bwd) {
            postOrder += it
        }
    }

    val sccs = mutableListOf<List<NodeId<N>>>()
    val allVisited = mutableSetOf<NodeId<N>>()

    // Step 2: Now that postOrder contains topologically sorted SCCs,
    // we can iterate it in reverse order to find out all SCCs.
    for (n in postOrder.reversed()) {
        if (allVisited.contains(n)) {
            continue
        }
        val visited = mutableListOf<NodeId<N>>()
        var isScc = false
        val preds = g.preds(n)
        GraphTraversal.dfs(n, g, GraphTraversal.Order.Pre) {
            if (allVisited.contains(it)) {
                return@dfs
            }
            allVisited += it
            visited += it
            if (!isScc && preds.contains(it)) {
                isScc = true
            }
        }
        if (isScc) {
            sccs += visited
        } else {
            sccs.addAll(visited.map { listOf(it) })
        }
    }

    return sccs
}

fun <N: Any> GraphAlgo.topoSort(g: DAG<N, *>): List<NodeId<N>> {
    if (g.isEmpty) {
        return emptyList()
    }

    // 1. Find all nodes without preds.
    val queue = g.nodes.filter { !it.hasPreds(g) }.toMutableSet()

    if (queue.isEmpty()) {
        throw HasCycles()
    }

    // 2. Do BFS on these.
    val sorted = queue.toMutableSet()
    val gb = g.toBuilder()
    while (queue.isNotEmpty()) {
        // For each node without predecessor
        val n = queue.first()
        queue -= n

        // Remove the node (and therefore all successor edges from this node)
        val succsSnapshot = gb.succs(n).toList()
        for (succ in succsSnapshot) {
            requireNotNull(gb.removeEdge(n, succ)) {
                "No edge from $n to $succ (sorted = $sorted, queue = $queue)"
            }
            if (gb.preds(succ).isEmpty() && !sorted.contains(succ)) {
                // If a successor loses all its predecessors, add it to the work list.
                queue += succ
                sorted += succ
            }
        }
        gb.removeNode(n)
    }

    if (gb.nodes.isNotEmpty()) {
        throw HasCycles()
    }

    return sorted.toList()
}

private fun <N: Any> NodeId<N>.hasPreds(g: DAG<N, *>) = g.preds(this).isNotEmpty()
