package com.github.om.inctc.graph

object GraphTraversal {
    enum class Order {
        Pre,
        Post,
    }

    enum class Direction {
        Fwd,
        Bwd,
    }
}

fun <N: Any> GraphTraversal.dfs(
    start: NodeId<N>,
    g: DAG<N, *>,
    order: GraphTraversal.Order,
    direction: GraphTraversal.Direction = GraphTraversal.Direction.Fwd,
    cb: (NodeId<N>) -> Unit
) {
    fun next(n: NodeId<N>) = if (direction == GraphTraversal.Direction.Fwd) {
        g.succs(n)
    } else {
        g.preds(n)
    }

    val visited = mutableSetOf<NodeId<N>>()

    fun go(n: NodeId<N>) {
        visited += n
        if (order == GraphTraversal.Order.Pre) {
            cb(n)
        }
        next(n)?.forEach {
            if (!visited.contains(it)) {
                go(it)
            }
        }
        if (order == GraphTraversal.Order.Post) {
            cb(n)
        }
    }

    go(start)
}
