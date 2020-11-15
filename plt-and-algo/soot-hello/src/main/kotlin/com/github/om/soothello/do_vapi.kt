package com.github.om.soothello

import soot.RefType
import soot.Scene
import soot.SootClass
import soot.Type
import soot.jimple.JimpleBody
import soot.jimple.internal.JAssignStmt
import soot.jimple.internal.JStaticInvokeExpr
import soot.options.Options
import java.io.File

object Vapi {
    fun gradleCps(): HasCp {
        val buildDir = File(System.getProperty("user.home")) / "src/voyager-api_trunk"
        return GradleCpSet(buildDir, listOf("identity-dash"))
    }

    fun initSoot() {
        Options.v().set_allow_phantom_refs(true)
        Options.v().set_ignore_resolving_levels(true)
        SootUtil.setCp(gradleCps())
        Scene.v().loadNecessaryClasses()
    }

    val TALENT_DECORATOR_CDW = "com.linkedin.talent.decorator.ContextualDecoratorWriter"
    val TALENT_DECORATOR_CDWB = "com.linkedin.talent.decorator.ContextualDecoratorWriterBinder"

    fun asBinderOrMapper(type: Type): RefType? {
        return if (type is RefType && type.className == TALENT_DECORATOR_CDW) {
            type
        } else {
            null
        }
    }
}

fun analyzeAllClasses() {
    val allKlassNames = SootUtil.allClassesUnder(Vapi.gradleCps())
    val ixGen = generateSequence(1, { it + 1 })
    val decorTypes = mutableListOf<RefType>()
    allKlassNames.take(250).zip(ixGen).forEach { (klassName, i) ->
        if (i % 10 == 0) {
            println(i)
        }
        val klass = SootUtil.loadClass(klassName)
        klass.allReferredTypes().forEach {
            Vapi.asBinderOrMapper(it)?.let {
                println("Found: $i @ $it")
                decorTypes += it
            }
        }
    }
    println(decorTypes.joinToString("\n"))
}

fun main() {
    Vapi.initSoot()
    val pdb = SootUtil.allClassesUnder(Vapi.gradleCps()).first {
        it.endsWith(".ProfileDecoratorBinder")
    }
    val psKlassName = "com.linkedin.voyager.dash.identity.profile.core.services.ProfileService"
    val psKlass = SootUtil.loadClass(pdb)
    assert(psKlass.fields.isNotEmpty())
    println(psKlass.interfaces.first)

    // val body = psKlass.getMethodByName("updateProfileSetting").retrieveActiveBody() as JimpleBody
}

fun SootClass.allReferredTypes(): Set<Type> {
    val out = mutableSetOf<Type>()
    for (f in fields) {
        out += f.type
    }
    for (m in methods) {
        out += m.parameterTypes
        out += m.returnType

        // Body types

        if (!m.isAbstract) {
            val body = m.retrieveActiveBody() as JimpleBody
            body.useBoxes.mapTo(out) { it.value.type }
            body.defBoxes.mapTo(out) { it.value.type }
            m.releaseActiveBody()
        }
    }
    return out
}
