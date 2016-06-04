package com.github.overmind.seaofnodes

object Main {
  def main(args: Array[String]): Unit = {
    // val res = Ast.execRootStmt(Ast.Sample.loopSum)
    // println(s"res: $res")

    val builder = SeaIR.ShallowBlockBuilder()
    val entry = builder.buildRootStmt(Ast.Sample.ifs)
    builder.dfsBlock(entry) { b =>
      println(s"$b -> ${b.exit}")
    }
  }
}