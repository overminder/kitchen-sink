package com.github.overmind.seaofnodes

import java.io.FileWriter

import com.github.overmind.seaofnodes.ast.LongValue
import com.github.overmind.seaofnodes.hir.Linearize.TGraph
import com.github.overmind.seaofnodes.hir._
import com.github.overmind.seaofnodes.hir.nodes.Node
import com.github.overmind.seaofnodes.backend.x64.{Gas, ISel, X64Arch}

import scala.io.Source

object Main {
  def interpAst(s: ast.Stmt): Unit = {
    val res = ast.Interp.execRootStmt(s)
    println(s"res: $res")
  }

  def interpGraph(g: Graph, args: Seq[ast.Value]) = {
    val terp = Interp(args, verbose = false)
    println(s"Interp => ${terp.run(g.entry)}")
  }

  def buildGraph(s: ast.FuncDef, name: String): Graph = {
    // Opt.simplifyControl(entry.successor.asInstanceOf[RegionNode], builder)
    // println(s"interp($name) => ${Graph.interp(entry)}")

    val g = GraphFromAst.build(s, cfold = false)
    // Opt.simplifyControl(g.entry, g)
    // Gcm(g).scheduleEarly(true)
    // Gcm(g).scheduleLate(true)
    Gcm(g, verbose = false).run()
    renderNodeToDot(g.entry, name)
    g

    // val lgb = lir.GraphBuilder(entry)
    // val lg = lgb.build()
    // println(lg)
  }

  def graphToTrace(g: Graph): TGraph = {
    Linearize.build(g)
  }

  def writeFile(path: String, content: String): Unit = {
    new FileWriter(path).append(content).close()
  }

  def readFile(path: String): String = {
    Source.fromFile(path).mkString
  }

  def renderNodeToDot(s: Node, name: String): Unit = {
    writeFile(s"dots/$name.dot", DotFromNode.gen(name, s))
  }

  def renderTraceToDot(g: TGraph, name: String): Unit = {
    writeFile(s"dots/$name.dot", Linearize.toDot(g))
  }

  def main(args: Array[String]): Unit = {
    val (fileName, funcArgs) = if (args.length == 0) {
      ("ast-src/fibo-iter.ast", Seq(LongValue(10L)))
    } else {
      (args(0), args.drop(1).map(s => LongValue(s.toLong)).toSeq)
    }
    // buildShallowRegion(Ast.Sample.returns)
    val func = ast.Parser.parseFuncDef(readFile(fileName))
    println(s"AST: $func")
    val g = buildGraph(func, "last")
    val tg = graphToTrace(g)
    renderTraceToDot(tg, "last-trace")

    val arch = X64Arch

    val lsra = Lsra(tg, arch, verbose = true)
    lsra.run()
    lsra.printLiveness()

    val isel = ISel(lsra)
    val instrs = isel.emitGraph(tg)

    val gas = Gas(arch).instrs(instrs)
    println("GAS:")
    println(gas)

    writeFile("asm/last.s", s".globl last\nlast:\n$gas\n")

    // println("Before interp")
    // interpGraph(g, funcArgs)
  }
}