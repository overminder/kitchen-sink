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
    val builder = ShallowRegionBuilder(s)
    Graph.dfsRegion(builder.firstRegion) { b =>
      println(s"$b")
    }
  }

  def buildGraph(s: Ast.Stmt, name: String): Unit = {
    val shallowBuilder = ShallowRegionBuilder(s)
    val builder = GraphBuilder()
    val entry = builder.build(shallowBuilder.firstRegion, shallowBuilder.endNode, s)
    // Opt.simplifyControl(entry.successor.asInstanceOf[RegionNode], builder)
    println(s"interp($name) => ${Graph.interp(entry)}")

    // renderNodeToDot(entry, name)
  }

  def writeFile(path: String, content: String): Unit = {
    new FileWriter(path).append(content).close()
  }

  def renderNodeToDot(s: Node, name: String): Unit = {
    writeFile(s"dots/$name.dot", DotContext(name).addNode(s).render)
  }

  def main(args: Array[String]): Unit = {
    // buildShallowRegion(Ast.Sample.returns)
    buildGraph(Ast.Sample.loopSum, "loopSum")
  }
}