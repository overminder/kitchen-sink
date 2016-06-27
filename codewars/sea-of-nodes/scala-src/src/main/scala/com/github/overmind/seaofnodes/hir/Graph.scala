package com.github.overmind.seaofnodes.hir

import java.util
import java.util.Collections

import com.github.overmind.seaofnodes.ast._
import com.github.overmind.seaofnodes.hir.nodes._

import scala.collection.JavaConverters._
import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

object Graph {
  type NodeSet = mutable.Set[Node]
  type NodeMap[A] = mutable.Map[Node, A]

  type EdgeSet = mutable.Set[Edge]
  type EdgeMap[A] = mutable.Map[Edge, A]

  def emptyIdentitySet[A <: AnyRef] =
    Collections.newSetFromMap(new util.IdentityHashMap[A, java.lang.Boolean]()).asScala

  def emptyIdentityNodeSet: NodeSet = emptyIdentitySet[Node]
  // Doesn't need to (and probably can't) be identity-based - we use a shallow hashCode/equality
  // based key instead.
  def emptyEdgeSet: EdgeSet = mutable.Set.empty[Edge]

  def emptyIdentityNodeMap[A]: NodeMap[A] = emptyIdentityMap[Node, A]
  def emptyEdgeMap[A]: EdgeMap[A] = mutable.Map.empty[Edge, A]

  def emptyIdentityMap[A <: AnyRef, B] = new util.IdentityHashMap[A, B]().asScala

  case class UndefinedVarInGraph(name: String) extends Exception
  case class Unexpected(what: String) extends Exception

  def dfsNodeAndEdge(n: Node, onNode: Node => Unit, onEdge: Edge => Unit) = {
    val visited = emptyIdentitySet[Node]
    def go(n: Node): Unit = {
      if (visited.add(n)) {
        onNode(n)
        n.edges.foreach(e => {
          onEdge(e)
          go(e.to)
        })
        n.inputs.foreach(go)
        Option(n.predecessor).foreach(go)
      }
    }
    go(n)
  }

  case class IDomEdge(idom: Option[Node], of: Node, treeDepth: Int, loopNestingDepth: Int)

  def dfsIdom(n: Node, onEdge: IDomEdge => Unit) = {
    val visited = emptyIdentitySet[Node]
    def go(idom: Node, treeDepth: Int, loopNestingDepth: Int): Unit = {
      val newDepth = treeDepth + 1
      assert(visited.add(idom))
      idom.isIDomOf.foreach(of => {
        val newLoopNestingDepth = of match {
          case b: BaseBeginNode if b.endsWithReturn => 0
          case _: LoopBeginNode => 1 + loopNestingDepth
          case _: LoopExitNode => -1 + loopNestingDepth
          // case _: RetNode => 0
          case _ => loopNestingDepth
        }
        onEdge(IDomEdge(Some(idom), of, newDepth, newLoopNestingDepth))
        go(of, newDepth, newLoopNestingDepth)
      })
    }
    onEdge(IDomEdge(None, n, 0, 0))
    go(n, 0, 0)
  }

  def dfsEdge(n: Node)(f: Edge => Unit) = {
    dfsNodeAndEdge(n, _ => (), f)
  }

  def dfsNode(n: Node)(f: Node => Unit) = {
    dfsNodeAndEdge(n, f, _ => ())
  }
}

case class Graph(entry: GraphEntryNode, exit: GraphExitNode) {
  val valueNumbered = mutable.Map.empty[ValueNumberable, Node]

  // n should be a fresh node.
  def unique[N <: ValueNumberable](n: N): N = {
    valueNumbered.get(n) match {
      case Some(n0) =>
        n.replaceAllUsesWith(n0)
        n0.asInstanceOf[N]
      case None =>
        valueNumbered += (n -> n)
        n
    }
  }
}
