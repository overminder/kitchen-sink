package com.github.om.inctc.lang.poly

class PprState(val sb: StringBuilder = StringBuilder()) {
    val output: String
        get() = sb.toString()

    fun text(s: String) {
        sb.append(s)
    }

    fun nl() = text("\n")

    fun pprFqName(moduleName: ModuleName, ident: Ident) {
        text("${moduleName.name}.${ident.name}")
    }

    companion object {
        fun ppr(m: Module): String {
            val st = PprState()
            m.ppr(st)
            return st.output
        }
    }
}

fun ModuleName.ppr(st: PprState) = st.text(name)
fun Ident.ppr(st: PprState) = st.text(name)
fun Visibility.ppr(st: PprState) = when (this) {
    Visibility.Public -> st.text("pub ")
    Visibility.Internal -> Unit
}

fun Module.ppr(st: PprState) {
    decls.firstOrNull()?.ppr(st)
    decls.drop(1).forEach {
        st.nl()
        it.ppr(st)
    }
}

fun Decl.ppr(st: PprState) {
    when (this) {
        is Import -> {
            st.text("use ")
            st.pprFqName(moduleName, ident)
        }
        is ValueDef -> {
            visibility.ppr(st)
            st.text("def ")
            ident.ppr(st)
            st.text(" = ")
            body.ppr(st)
        }
    }
}

fun Exp.ppr(st: PprState): Unit = when (this) {
    is Var -> ident.ppr(st)
    is Lam -> {
        st.text("fun ")
        args[0].ppr(st)
        args.drop(1).forEach {
            st.text(" ")
            it.ppr(st)
        }
        st.text(" in ")
        body.ppr(st)
        st.text(" end")
    }
    is Let -> {
        st.text("let")
        for ((ident, rhs) in bindings) {
            st.text(" ")
            ident.ppr(st)
            st.text(" = ")
            rhs.ppr(st)
        }
        st.text(" in ")
        body.ppr(st)
        st.text(" end")
    }
    is LitI -> st.text("$value")
    is If -> {
        st.text("if ")
        cond.ppr(st)
        st.text(" then ")
        then.ppr(st)
        st.text(" else ")
        else_.ppr(st)
        st.text(" end")
    }
    is App -> {
        val (f, args) = unrollApp(this)
        f.ppr(st)
        st.text("(")
        args[0].ppr(st)
        args.drop(1).forEach {
            st.text(", ")
            it.ppr(st)
        }
        st.text(")")
    }
    is BOp -> {
        // XXX Might need parenthesis
        left.ppr(st)
        st.text(" ${op.token} ")
        right.ppr(st)
    }
}

private fun unrollApp(f0: Exp): Pair<Exp, List<Exp>> {
    var f = f0
    val args = mutableListOf<Exp>()
    while (f is App) {
        args.add(f.arg)
        f = f.func
    }
    args.reverse()
    return f to args
}
