package com.github.overmind.seaofnodes.hir.nodes

case class Edge(from: Node, to: Node, ix: Int, isControlDep: Boolean) {
  // Shallow equality.
  override def equals(that: Any): Boolean = {
    that match {
      case e: Edge =>
        from.eq(e.from) && to.eq(e.to) && ix == e.ix && isControlDep == e.isControlDep
      case _ =>
        false
    }
  }

  // Shallow hash
  override def hashCode = {
    Seq(from.identityHashCode, to.identityHashCode, ix.hashCode, isControlDep.hashCode)
      .foldRight(0)(_ + _ * 41)
  }
}
