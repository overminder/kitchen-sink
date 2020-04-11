package com.github.om.inctc.graph

sealed class GraphAlgoError: RuntimeException()

class HasCycles: GraphAlgoError()

object GraphAlgo

fun <N: Any> GraphAlgo.scc(g: DAG<N, *>) {
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
        val succsSnapshot = gb.succs(n)?.toList() ?: emptyList()
        for (succ in succsSnapshot) {
            requireNotNull(gb.removeEdge(n, succ)) {
                "No edge from $n to $succ (sorted = $sorted, queue = $queue)"
            }
            if (gb.preds(succ)?.isEmpty() != false && !sorted.contains(succ)) {
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

private fun <N: Any> NodeId<N>.hasPreds(g: DAG<N, *>) = g.preds(this)?.isNotEmpty() ?: false
