package yux.ktcpg.lib

/**
 * A bunch of examples showing what kind of code triggers detekt's LibraryCodeMustSpecifyReturnType rule.
 */

fun doSomething() {
    println("HAI")
}

fun doAnotherThing(): Unit = doSomething()

/*

// This does trigger and indeed should trigger.
val a = listOf("a")

private object Foo {

    // This shouldn't trigger (parent is a private object so I wouldn't say this is a public API) but does trigger.
    // A workaround is to add `internal` modifier to it. A real fix is to make the lint rule consider fooVal's
    // *effective* visibility, rather than the *declared* visibility.
    val fooVal = listOf("foo")
}

interface Bar {
    fun doBar(): List<String>
}

private val aBar = object: Bar {

    // This doesn't trigger. The reason is that because doBar's parent is an object literal and therefore
    // KtModifierListOwner.isPublic consider doBar as a non-Public declaration.
    override fun doBar() = listOf("bar")
}

private object ABar: Bar {

    // This does trigger. Whether we should trigger in this case is debatable -- The interface already specifies
    // the return type of doBar() so if ABar is used as a Bar, I would say such return type declaration is not needed.
    override fun doBar() = listOf("bar")
}

 */
