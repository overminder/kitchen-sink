package com.github.overmind.seaofnodes.hir

import com.github.overmind.seaofnodes.ast.Value
import com.github.overmind.seaofnodes.hir.nodes._

import scala.collection.mutable

sealed trait Lattice {
  // \/
  def join(that: Lattice): Lattice
  // /\
  def meet(that: Lattice): Lattice
}

object Lattice {
  def top: Lattice = Top
  def bottom: Lattice = Bottom
  def const(v: Value): Lattice = Const(v)

  case object Top extends Lattice {
    def join(that: Lattice) = that
    def meet(that: Lattice) = this
  }

  case object Bottom extends Lattice {
    def join(that: Lattice) = this
    def meet(that: Lattice) = that
  }

  case class Const(v: Value) extends Lattice {
    def join(that: Lattice) = {
      that match {
        case Top =>
          this
        case Const(v2) if v2 == v =>
          this
        case _ =>
          Bottom
      }
    }

    def meet(that: Lattice) = {
      that match {
        case Bottom =>
          this
        case Const(v2) if v2 == v =>
          this
        case _ =>
          Top
      }
    }
  }
}


case class Sccp(g: Graph, verbose: Boolean = false) {
  val flowWorklist = mutable.Queue.empty[Edge]
  val ssaWorklist = mutable.Queue.empty[Edge]
  val executableFlows = Graph.emptyEdgeSet
  val ssaEdgeValues = Graph.emptyEdgeMap[Lattice]
  val ssaValues = Graph.emptyIdentityNodeMap[Lattice]

  def run(): Unit = {
    g.entry.cfgEdges.foreach(flowWorklist.enqueue(_))
    go()
  }

  def goFlow(edge: Edge): Unit = {
    if (!executableFlows.add(edge)) {
      // Already visited.
      return
    }

    edge.to match {
      case n: BaseMergeNode =>
        n.valuePhis.foreach(goPhi)
        n.comingFromEdges.
      case ex: BaseBlockExitNode =>
        // ex.valueUses.foreach()
      case _ =>
        ()
    }
  }

  def ssaEdgeValue(ssaEdge: Edge): Lattice = {
    ssaEdgeValues(ssaEdge)
  }

  def goPhi(phi: ValuePhiNode): Unit = {
    val vlats = phi.composedInputsWithIncomingEdge.map({ case (ssaEdge, flowEdge) =>
      if (executableFlows.contains(flowEdge)) {
        ssaEdgeValue(ssaEdge)
      } else {
        // Not yet executable: be optimistic about it.
        Lattice.top
      }
    })
    val vlat = vlats.foldRight(Lattice.top) { case (a, b) =>
      a.join(b)
    }
    ssaValues += (phi -> vlat)
  }

  def goSsa(edge: Edge) = {
  }

  def go(): Unit = {
    if (flowWorklist.nonEmpty) {
      val flow = flowWorklist.dequeue()
      goFlow(flow)
      go()
    } else if (ssaWorklist.nonEmpty) {
      val ssa = ssaWorklist.dequeue()
      goSsa(ssa)
      go()
    } else {
      // Done.
    }
  }
}
