package com.github.overmind.seaofnodes

import java.io.{FileReader, FileWriter}
import java.nio.CharBuffer

import com.github.overmind.seaofnodes.hir.Graph.GraphBuilder
import com.github.overmind.seaofnodes.hir._
import com.github.overmind.seaofnodes.hir.nodes.{DotContext, Node}

import scala.io.Source

object Main {
  def interpAst(s: ast.Stmt): Unit = {
    val res = ast.Interp.execRootStmt(s)
    println(s"res: $res")
  }

  def buildShallowRegion(s: ast.Stmt): Unit = {
    val builder = ShallowRegionBuilder(s)
    Graph.dfsRegion(builder.firstRegion) { b =>
      println(s"$b")
    }
  }

  def buildGraph(s: ast.Stmt, name: String): Unit = {
    val shallowBuilder = ShallowRegionBuilder(s)
    val builder = GraphBuilder()
    val entry = builder.build(shallowBuilder.firstRegion, shallowBuilder.endNode, s)
    // Opt.simplifyControl(entry.successor.asInstanceOf[RegionNode], builder)
    // println(s"interp($name) => ${Graph.interp(entry)}")

    renderNodeToDot(entry, name)

    // val lgb = lir.GraphBuilder(entry)
    // val lg = lgb.build()
    // println(lg)
  }

  def writeFile(path: String, content: String): Unit = {
    new FileWriter(path).append(content).close()
  }

  def readFile(path: String): String = {
    Source.fromFile(path).mkString
  }

  def renderNodeToDot(s: Node, name: String): Unit = {
    writeFile(s"dots/$name.dot", DotContext(name).addNode(s).render)
  }

  def main(args: Array[String]): Unit = {
    // buildShallowRegion(Ast.Sample.returns)
    val prog = ast.Parser.parseStmt(readFile(args(0)))
    println(s"AST: $prog")
    buildGraph(prog, "loopSum")
  }
}