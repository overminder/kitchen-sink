package com.github.om.inctc

open class Base(@JvmField open val f1: Any?)
class Derive(@JvmField override val f1: List<Int>): Base(f1)
// ^ Essentially another field.

fun main() {
    val b = Base(null)
    val d = Derive(listOf(5))

    println("${d.f1}, ${(d as Base).f1}")

    for (f in Derive::class.java.fields) {
        println("Derive: ${f.name}, ${f.type}, by ${f.declaringClass.simpleName}");
    }

    for (f in Base::class.java.fields) {
        println("Base: ${f.name}, ${f.type}");
    }
}

