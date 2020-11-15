package com.github.om.soothello

import org.objectweb.asm.ClassReader
import org.objectweb.asm.tree.ClassNode

object OwMain {
    fun main() {
        val cpRoot = Chrysaor.rootDir / "build" / "data" / "classes" / "java" / "main"
        val className = "com.linkedin.data.lite.DataTemplate"
        val cp = cpRoot / (className.replace(".", "/") + ".class")
        val c = ClassNode()
        cp.inputStream().use {
            val cr = ClassReader(it)
            cr.accept(c, 0)
        }
        println(c.methods)
    }
}

fun main() {
    OwMain.main()
}