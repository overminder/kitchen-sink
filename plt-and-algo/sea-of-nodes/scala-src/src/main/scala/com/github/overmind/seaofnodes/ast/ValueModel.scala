package com.github.overmind.seaofnodes.ast

import scala.collection.mutable.ArrayBuffer

sealed trait Value {
  final def +(that: Value): Value = {
    LongValue(asLong + that.asLong)
  }
  final def -(that: Value): Value = {
    LongValue(asLong - that.asLong)
  }
  final def <(that: Value): Value = {
    BoolValue(asLong < that.asLong)
  }
  final def at(index: Value): Value = {
    asArray(index.asLong.toInt)
  }
  final def setAt(index: Value, to: Value): Value = {
    asArray(index.asLong.toInt) = to
    to
  }

  def asLong: Long = {
    throw UnexpectedValue("Not a LongValue", this)
  }
  def asArray: ArrayBuffer[Value] = {
    throw UnexpectedValue("Not an ArrayValue", this)
  }
  def asBoolean: Boolean = {
    throw UnexpectedValue("Not a BoolValue", this)
  }
}

sealed trait BoolValue extends Value
case object TrueValue extends BoolValue {
  override def asBoolean = true
}
case object FalseValue extends BoolValue {
  override def asBoolean = false
}
case object BoolValue {
  def apply(lval: Long): BoolValue = {
    if (lval == 0) {
      FalseValue
    } else {
      TrueValue
    }
  }
  def apply(bval: Boolean): BoolValue = {
    if (bval) {
      TrueValue
    } else {
      FalseValue
    }
  }
}
case class LongValue(lval: Long) extends Value {
  override def asLong = lval
}

case class ArrayValue(vs: ArrayBuffer[Value]) extends Value {
  override def asArray = vs
}

object ArrayValue {
  def create(len: Int): ArrayValue = {
    ArrayValue(ArrayBuffer.fill(len)(null))
  }
}

case class UnexpectedValue(reason: String, value: Value) extends Exception
