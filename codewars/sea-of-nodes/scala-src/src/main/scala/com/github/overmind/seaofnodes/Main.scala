package com.github.overmind.seaofnodes

import java.io.FileWriter

import com.github.overmind.seaofnodes.ir.Graph.GraphBuilder
import com.github.overmind.seaofnodes.ir._

import scala.io.Source

object Main {
  def interpAst(s: Ast.Stmt): Unit = {
    val res = Ast.execRootStmt(s)
    println(s"res: $res")
  }

  def buildShallowRegion(s: Ast.Stmt): Unit = {
    val builder = ShallowRegionBuilder()
    val entry = builder.buildRootStmt(s)
    ShallowRegionBuilder.dfsRegion(entry) { b =>
      println(s"$b")
    }
  }

  def buildGraph(s: Ast.Stmt, name: String): Unit = {
    val builder = ShallowRegionBuilder()
    val shallowEntry = builder.buildRootStmt(s)
    val entry = GraphBuilder().build(shallowEntry, s)

    renderNodeToDot(entry, name)
  }

  def writeFile(path: String, content: String): Unit = {
    new FileWriter(path).append(content).close()
  }

  def renderNodeToDot(s: Node, name: String): Unit = {
    writeFile(s"dots/$name.dot", DotContext(name).addNode(s).render)
  }

  def main(args: Array[String]): Unit = {
    // buildShallowRegion(Ast.Sample.returns)
    buildGraph(Ast.Sample.unreachableCodeInLoop, "loopSum")
  }
}