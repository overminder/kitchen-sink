package com.github.overmind.seaofnodes

import java.io.FileWriter

import scala.collection.mutable.ArrayBuffer

object DotGen {
  trait ToDot {
    def toDot: String
  }

  def buildSampleDot(out: String): Unit = {
    val g = DotGen.Graph("title")
    val a = g.addText("A")
    val b = g.addText("B")
    val c = g.addText("C")
    val d = g.addText("D")
    g.addEdge(a, b)
    g.addEdge(b, c)
    g.addEdge(b, d)
    g.addEdge(c, b)
    new FileWriter(out).append(g.toDot).close()
  }

  case class Graph(name: String) extends ToDot {
    val content = ArrayBuffer.empty[ToDot]
    var nextId = 1

    def addText(text: String): NodeId = {
      val n = NodeId(nextId)
      nextId += 1
      content += TextNode(n, text)
      n
    }

    def addEdge(from: NodeId, to: NodeId): Unit = {
      content += Edge(from, to, Options(Seq()))
    }

    def addEdge(from: NodeId, to: NodeId, options: (String, String)*): Unit = {
      content += Edge(from, to, Options(options))
    }

    def toDot = s"digraph $name {\n" +
      content.map(_.toDot).mkString("\n") +
      "\n}"
  }

  case class Options(kvs: Seq[(String, String)]) extends ToDot {
    def toDot = "[" + kvs.map({
      case (k, v) => s"""$k="$v""""
    }).mkString(" ") + "]"
  }

  case class Edge(from: NodeId, to: NodeId, options: Options) extends ToDot {
    def toDot = s"""${from.toDot} -> ${to.toDot} ${options.toDot};"""
  }

  case class TextNode(id: NodeId, text: String) extends ToDot {
    def toDot = s"${id.toDot} " + "[label=\"" + text + "\"];"
  }

  case class NodeId(v: Int) extends ToDot {
    def toDot = s"n_$v"
  }
}
