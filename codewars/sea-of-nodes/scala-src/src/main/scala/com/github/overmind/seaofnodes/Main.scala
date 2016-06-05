package com.github.overmind.seaofnodes

import java.io.FileWriter

import com.github.overmind.seaofnodes.ir.Graph.{DotContext, GraphBuilder}
import com.github.overmind.seaofnodes.ir.ShallowRegionBuilder

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

    new FileWriter(s"$name.dot").append(DotContext(name).addNode(entry).render).close()
  }

  def main(args: Array[String]): Unit = {
    // buildShallowRegion(Ast.Sample.loopSum)
    buildGraph(Ast.Sample.loopSum, "loopSum")
  }
}