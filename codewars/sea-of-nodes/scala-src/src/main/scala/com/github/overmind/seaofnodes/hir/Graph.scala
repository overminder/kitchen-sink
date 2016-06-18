package com.github.overmind.seaofnodes.hir

import java.util
import java.util.Collections

import com.github.overmind.seaofnodes.ast._
import com.github.overmind.seaofnodes.hir.nodes._

import scala.collection.JavaConverters._
import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

object Graph {
  def emptyIdentitySet[A <: AnyRef] =
    Collections.newSetFromMap(new util.IdentityHashMap[A, java.lang.Boolean]()).asScala

  def emptyIdentityMap[A <: AnyRef, B] = new util.IdentityHashMap[A, B]().asScala

  case class UndefinedVarInGraph(name: String) extends Exception
  case class Unexpected(what: String) extends Exception

  // def interp(n: Node) = Interp.interp(n)

  case class Edge(from: Node, to: Node, ix: Int, isControlDep: Boolean)

  def dfsNodeAndEdge(n: Node, onNode: Node => Unit, onEdge: Edge => Unit) = {
    val visited = emptyIdentitySet[Node]
    def go(n: Node): Unit = {
      if (visited.add(n)) {
        onNode(n)
        n.uses.zipWithIndex.foreach({ case (i, ix) =>
          onEdge(Edge(n, i, ix, isControlDep = false))
          go(i)
        })
        n.successors.zipWithIndex.foreach({ case (s, ix) =>
          onEdge(Edge(n, s, ix, isControlDep = true))
          go(s)
        })
        n.inputs.foreach(go)
        Option(n.predecessor).foreach(go)
      }
    }
    go(n)
  }

  def dfsEdge(n: Node)(f: Edge => Unit) = {
    dfsNodeAndEdge(n, _ => (), f)
  }

  def dfsNode(n: Node)(f: Node => Unit) = {
    dfsNodeAndEdge(n, f, _ => ())
  }
}

case class Graph(entry: GraphEntryNode, exit: GraphExitNode) {
  val cached = mutable.Map.empty[Node, Node]

  // n should be a fresh node.
  def unique[N <: Node](n: N): N = {
    cached.get(n) match {
      case Some(n0) =>
        n.replaceAllUsesWith(n0)
        n.remove()
        n0.asInstanceOf[N]
      case None =>
        cached += (n -> n)
        n
    }
  }
}
