package com.github.overmind.seaofnodes

import scala.collection.mutable;

object SeaIR {
  case class ShallowBlockBuilder() {
    // Scan through the ASTs to build all the blocks.
    import com.github.overmind.seaofnodes.Ast._

    type BlockId = Int

    sealed trait Exit
    object Exit {
      case class If(t: Block, f: Block) extends Exit
      case class Jmp(to: Block) extends Exit
      case class While(loopB: Block, endB: Block) extends Exit
      case object Return extends Exit

      def exits(e: Exit): Seq[Block] = {
        e match {
          case If(t, f) => Seq(t, f)
          case Jmp(to) => Seq(to)
          case While(a, b) => Seq(a, b)
          case Return => Seq.empty
        }
      }
    }

    case class Block(id: BlockId, var exit: Option[Exit]) {
      override def toString(): String = {
        s"<Block $id>"
      }
    }

    def dfsBlock(b: Block)(f: Block => Unit): Unit = {
      def go(b: Block, visited: mutable.Set[BlockId]): Unit = {
        if (!visited.contains(b.id)) {
          visited.add(b.id)
          f(b)
          b.exit.foreach(e => Exit.exits(e).foreach(go(_, visited)))
        }
      }
      go(b, mutable.Set.empty)
    }

    var nextBlockId = 0
    var currentBlock: Option[Block] = None
    var entryBlock: Option[Block] = None

    def buildRootStmt(s: Stmt): Block = {
      val entry = ensureBlock()
      entryBlock = Some(entry)
      buildStmt(s)
      entry
    }

    def allocBlock(): Block = {
      val b = Block(nextBlockId, None)
      nextBlockId += 1
      b
    }

    def ensureBlock(): Block = {
      currentBlock match {
        case None =>
          val b = allocBlock()
          currentBlock = Some(b)
          b
        case Some(b) => b
      }
    }

    def finishBlock(exit: Exit): Block = {
      val b = ensureBlock()
      b.exit = Some(exit)
      currentBlock = None
      b
    }

    def startBlockThatEndsWith(b: Block, s: Option[Stmt], exit: Exit): Block = {
      setCurrentBlock(b)
      s.foreach(buildStmt)
      finishBlock(exit)
    }

    def setCurrentBlock(endBlock: Block): Unit = {
      assert(currentBlock.isEmpty, s"setCurrentBlock is not None: $currentBlock")
      currentBlock = Some(endBlock)
    }

    def buildStmt(s: Stmt): Unit = {
      ensureBlock()
      s match {
        case Stmt.Begin(ss) => ss.foreach(buildStmt)

        case Stmt.If(_, t, f) =>
          val tB = allocBlock()
          val fB = allocBlock()
          val endB = allocBlock()

          finishBlock(Exit.If(tB, fB))
          startBlockThatEndsWith(tB, Some(t), Exit.Jmp(endB))
          startBlockThatEndsWith(fB, Some(f), Exit.Jmp(endB))
          setCurrentBlock(endB)

        case Stmt.While(cond, body) =>
          val checkB = allocBlock()
          val loopB = allocBlock()
          val endB = allocBlock()

          finishBlock(Exit.Jmp(checkB))
          startBlockThatEndsWith(checkB, None, Exit.While(loopB, endB))
          startBlockThatEndsWith(loopB, Some(body), Exit.Jmp(checkB))
          setCurrentBlock(endB)

        case Stmt.Ret(e) =>
          finishBlock(Exit.Return)

        case _: Stmt.Assign => ()
      }
    }
  }

  case class GraphBuilder() {
    import com.github.overmind.seaofnodes.Ast._

    def define(v: String, n: Any): Unit = ???

    def buildExpr(e: Expr) = ???
  }
}
