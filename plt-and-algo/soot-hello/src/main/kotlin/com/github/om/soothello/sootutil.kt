package com.github.om.soothello

import soot.Scene
import soot.SootClass
import soot.options.Options
import soot.tagkit.Tag
import soot.tagkit.VisibilityAnnotationTag
import java.io.File
import java.nio.file.Files
import kotlin.streams.asSequence

interface HasCp {
    val cp: List<File>

    companion object {
        operator fun invoke(cp: List<File>) = object : HasCp {
            override val cp: List<File>
                get() = cp
        }
    }
}

object SootUtil {
    fun allClassesUnder(hasCp: HasCp): Sequence<String> {
        return hasCp.cp.asSequence().flatMap { cp ->
            Files.walk(cp.toPath()).asSequence().mapNotNull { path ->
                val f = path.toFile()
                if (f.extension == "class") {
                    f.relativeTo(cp).toString()
                        .replace(".class", "")
                        .replace("/", ".")
                } else {
                    null
                }
            }
        }
    }

    fun setCp(cpSet: HasCp) {
        // Options.v().set_allow_phantom_refs(true)
        // TODO: Find correct jdk classpath
        val javacp = Scene.defaultJavaClassPath()
        val cps = (listOf(javacp) + cpSet.cp).joinToString(":")
        Options.v().set_soot_classpath(cps)
    }

    fun loadClass(name: String): SootClass {
        val sc = Scene.v().loadClassAndSupport(name)

        assert(!sc.isPhantom)
        sc.setApplicationClass()
        assert(Scene.v().getSootClass(name) === sc)
        return sc
    }

    fun printTag(tag: Tag) {
        println(buildString {
            append("name: ", tag.name, ", ")
            if (tag is VisibilityAnnotationTag) {
                append("Vis(info = ", tag.info, "; ")
                append(tag.annotations.joinToString {
                    it.type
                })
                append(")")
            }
        })
    }
}

// TODO: Somehow read cp from gradle
class GradleCpSet(
    val rootDir: File,
    val subprojects: List<String>,
) : HasCp {
    override val cp: List<File>
        get() {
            val out = mutableListOf<File>()
            val buildDir = rootDir / "build"
            tryAddPath(buildDir, null, out)
            for (p in subprojects) {
                tryAddPath(buildDir, p, out)
            }
            return out
        }

    private fun tryAddPath(buildDir: File, projectName: String?, out: MutableList<File>) {
        val pBuildDir = projectName?.let {
            buildDir / it
        } ?: buildDir
        val classesDir = pBuildDir / "classes"
        if (classesDir.isDirectory) {
            for (sourceSet in listOf("java", "kotlin")) {
                val classpath = classesDir / sourceSet / "main"
                if (classpath.isDirectory()) {
                    out += classpath
                }
            }
        }
    }
}

class ClassSig(val value: String) {
    companion object {
        fun from(className: String): ClassSig {
            assert(!className.startsWith("L"))
            assert(!className.endsWith(";"))
            return ClassSig("L" + className.replace(".", "/") + ";")
        }
    }
}
