package com.github.om.inctc.parse

data class Stream(val chars: CharSequence, val index: Int) {
    fun peek(): Char? = chars.getOrNull(index)
    fun next(): ParserResult<Char>? {
        val c = peek() ?: return null
        return ParserResult(c, copy(index = index + 1))
    }

    fun peekMany(length: Int): ParserResult<CharSequence>? {
        return if (index + length <= chars.length) {
            val res = chars.subSequence(index, index + length)
            ParserResult(res, copy(index = index + length))
        } else {
            null
        }
    }

    val isEof: Boolean
        get() = index == chars.length
}

data class ParserResult<out A>(val value: A, val stream: Stream) {
    fun <B> fmap(f: (A) -> B): ParserResult<B> = ParserResult(f(value), stream)
}


sealed class Or<out A, out B>
data class Left<out A, out B>(val value: A): Or<A, B>()
data class Right<out A, out B>(val value: B): Or<A, B>()

inline class Parser<out A>(val call: (Stream) -> Sequence<ParserResult<A>>) {
    operator fun invoke(s: Stream): Sequence<ParserResult<A>> = call(s)

    fun <B> fmap(f: (A) -> B): Parser<B> {
        val me = this
        return Parser { stream ->
            me(stream).map { it.fmap(f) }
        }
    }

    fun filter(f: (A) -> Boolean): Parser<A> {
        val me = this
        return Parser { stream ->
            me(stream).filter { f(it.value) }
        }
    }

    fun <B> ignoreLeft(right: Parser<B>): Parser<B> {
        return ParserCombinators0.andThen(this, right).fmap {
            it.second
        }
    }

    fun ignoreRight(right: Parser<*>): Parser<A> {
        return ParserCombinators0.andThen(this, right).fmap {
            it.first
        }
    }

    fun run(source: CharSequence): A? = this(Stream(source, 0)).firstOrNull()?.value
}


fun <Z, A, B> ((A, B) -> Z).curried(): (A) -> (B) -> Z = { a -> { b -> invoke(a, b) } }
fun <Z, A, B, C> ((A, B, C) -> Z).curried(): (A) -> (B) -> (C) -> Z = { a -> { b -> { c -> invoke(a, b, c) } } }

// XXX A naive impl would be so inefficient. Consider memoization
fun <A, B> Parser<(A) -> B>.ap(pa: Parser<A>): Parser<B> =
    ParserCombinators0.andThen(this, pa).fmap {
        val (f, a) = it
        f(a)
    }

interface ParserCombinators {
    fun <A> makeLazy(makeP: () -> Parser<A>): Parser<A> {
        val p = lazy(makeP)
        return Parser { stream ->
            // NOTE: no eta-reduction here, or this is not lazy.
            p.value(stream)
        }
    }

    fun <A> pure(a: A): Parser<A> = Parser { stream ->
        sequenceOf(ParserResult(a, stream))
    }

    fun eof(): Parser<Unit> = Parser { stream ->
        if (stream.isEof) {
            sequenceOf(ParserResult(Unit, stream))
        } else {
            emptySequence()
        }
    }

    fun peekIf(predicate: (Char?) -> Boolean): Parser<Char?> = Parser { stream ->
        val c = stream.peek()
        if (predicate(c)) {
            sequenceOf(ParserResult(c, stream))
        } else {
            emptySequence()
        }
    }

    fun charThat(predicate: (Char) -> Boolean): Parser<Char> = Parser { stream ->
        val r = stream.next()
        if (r != null && predicate(r.value)) {
            sequenceOf(r)
        } else {
            emptySequence()
        }
    }

    fun char(c: Char): Parser<Char> = charThat { it == c }

    fun stringThat(length: Int, predicate: (CharSequence) -> Boolean): Parser<CharSequence> = Parser { stream ->
        val r = stream.peekMany(length)
        if (r != null && predicate(r.value)) {
            sequenceOf(r)
        } else {
            emptySequence()
        }
    }

    fun string(s: String): Parser<CharSequence> = stringThat(s.length) { it == s }

    fun <A, B> andThen(pa: Parser<A>, pb: Parser<B>): Parser<Pair<A, B>> = Parser { stream ->
        pa(stream).flatMap { a ->
            pb(a.stream).map { b ->
                b.fmap { a.value to b.value }
            }
        }
    }

    fun <A> orElse(pa1: Parser<A>, pa2: Parser<A>): Parser<A> = Parser { stream ->
        pa1(stream) + pa2(stream)
    }

    fun <A: Any> optional(pa: Parser<A>): Parser<A?> = orElse(pa, pure(null))

    fun <A> choice(pas: List<Parser<A>>): Parser<A> {
        val fst = pas.first()
        return pas.drop(1).fold(fst, { acc, item ->
            orElse(acc, item)
        })
    }

    fun <A> many(pa: Parser<A>): Parser<List<A>> = orElse(makeLazy { many1(pa) }, pure(emptyList()))

    fun <A> many1(pa: Parser<A>): Parser<List<A>> = andThen(pa, makeLazy { many(pa) }).fmap {
        val (head, tail) = it
        listOf(head) + tail
    }

    fun <A> sepBy(pa: Parser<A>, sep: Parser<*>): Parser<List<A>> {
        return orElse(sepBy1(pa, sep), pure(emptyList()))
    }

    fun <A> sepBy1(pa: Parser<A>, sep: Parser<*>): Parser<List<A>> {
        return andThen(pa, many(sep.ignoreLeft(pa))).fmap {
            listOf(it.first) + it.second
        }
    }

    // ASCII

    fun letter(): Parser<Char> = charThat(Char::isLetter)
    fun digit(): Parser<Char> = charThat(Char::isDigit)
    fun space(): Parser<Char> = charThat { "\t\n\r ".contains(it) }
}

object ParserCombinators0: ParserCombinators

