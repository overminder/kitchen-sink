package com.github.om.soothello

import com.github.om.soothello.analyzee.AnalyzeeMain
import soot.PackManager
import soot.Scene
import soot.SootClass
import soot.SootMethod
import soot.jimple.JimpleBody
import soot.options.Options
import soot.tagkit.VisibilityAnnotationTag
import java.io.File
import java.net.URLClassLoader

object K {
    val pkg = "com.github.om.soothello.analyzee"

}

fun runtimeCps(): HasCp {
    val cl = ClassLoader.getSystemClassLoader() as URLClassLoader
    return HasCp(cl.urLs.mapNotNull {
        val s = it.toString()
        val prefix = "file:"
        assert(s.startsWith(prefix))
        File(s.removePrefix(prefix)).takeIf(File::exists)
    })
}

fun gradleCps(): HasCp {
    val cwd = System.getProperty("user.dir")
    return GradleCpSet(File(cwd), emptyList())
}

fun wholeProgramMain() {
    // Whole program is not an option as it's too slow (cg.spack gives 120k callgraph size and takes ~30 seconds,
    // while the naive one is faster but gives 200k size callgraph...)
    /*
    Options.v().set_whole_program(true)
    Options.v().setPhaseOption("cg.paddle", "on")
    SootUtil.setCp(gradleCps())

    val entryClass = Scene.v().loadClassAndSupport(AnalyzeeMain::class.java.name)
    entryClass.setApplicationClass()
    Scene.v().loadNecessaryClasses()

    Scene.v().mainClass = entryClass
    PackManager.v().runPacks()
    println(Scene.v().callGraph.size())
    */
}

fun oldMain() {
    val resourceClassName = "${K.pkg}.FooResource"
    val serviceClassName = "${K.pkg}.FooService"

    SootUtil.setCp(runtimeCps())
    // Allow incremental resolving of user classes
    Options.v().set_ignore_resolving_levels(true)
    // Always needed to resolve JDK classes, but disallow subsequent resolutions
    // -- unless we ignore resolve level, not sure what's the downside.
    Scene.v().loadNecessaryClasses()

    val resClass = SootUtil.loadClass(resourceClassName)
    val allResMethods = findAllResourceMethods(resClass)
    reachability(allResMethods.first())
}

fun reachability(entry: SootMethod) {
    val body = requireNotNull(entry.retrieveActiveBody() as? JimpleBody)
    body.firstNonIdentityStmt
}

fun findAllResourceMethods(resCls: SootClass): List<SootMethod> {
    val annSig = ClassSig.from("${K.pkg}.YoloEndpoint")

    val getFoo = resCls.getMethodByName("getFoo")

    val endpointMethods = resCls.methods.filter { m ->
        // println("${m.name}, ${m.tags}")
        val visTags = m.tags.filterIsInstance(VisibilityAnnotationTag::class.java)
        visTags.any { tag ->
            tag.annotations.any { ann ->
                ann.type == annSig.value
            }
        }
    }

    return endpointMethods
}
