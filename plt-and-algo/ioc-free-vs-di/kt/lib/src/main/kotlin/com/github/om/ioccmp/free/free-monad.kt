package com.github.om.ioccmp.free

import com.github.om.ioccmp.CoffeeRequest
import com.github.om.ioccmp.PaymentMethod

sealed class Free<out A> {
    data class Pure<out A>(val a: A) : Free<A>()
    data class Join<out A>(val ma: Bind<Free<A>, *>) : Free<A>()

    fun <B> fmap(f: (A) -> B): Free<B> = when (this) {
        is Pure -> Pure(f(a))
        is Join -> Join(ma.fmap { it.fmap(f) })
    }

    fun <B> bind(f: (A) -> Free<B>): Free<B> = when (this) {
        is Pure -> f(a)
        is Join -> Join(ma.fmap { it.bind(f) })
    }

    companion object {
        fun <A> lift(op: Op<A>): Free<A> = Join(Bind(op) { it }.fmap(::Pure))
    }
}

tailrec fun <A> Free<A>.interp(opHandler: OpHandler): A {
    return when (this) {
        is Free.Pure -> a
        is Free.Join -> ma.interp(opHandler).interp(opHandler)
    }
}

interface OpHandler {
    // Hmm so we do have rank 2 type?
    fun <A> handle(op: Op<A>): A
}

data class Bind<out A, B>(val op: Op<B>, val k: (B) -> A) {
    fun <C> fmap(f: (A) -> C): Bind<C, B> = Bind(op) { b -> f(k(b)) }

    fun interp(opHandler: OpHandler): A {
        return k(opHandler.handle(op))
    }
}

sealed class Op<out A> {
    sealed class CoffeeRequestReaderOp<out A> : Op<A>() {
        data class GetPaymentMethod(val coffeeRequest: CoffeeRequest) : CoffeeRequestReaderOp<PaymentMethod>()
    }

    sealed class PaymentTransactorOp<out A> : Op<A>() {
        data class Transact(val paymentMethod: PaymentMethod) : PaymentTransactorOp<Boolean>()
    }

    companion object {
        fun getPaymentMethod(coffeeRequest: CoffeeRequest) =
            Free.lift(CoffeeRequestReaderOp.GetPaymentMethod(coffeeRequest))

        fun transact(paymentMethod: PaymentMethod) =
            Free.lift(PaymentTransactorOp.Transact(paymentMethod))
    }
}

fun makeImpl(cr: CoffeeRequest): Free<Boolean> {
    return Op.getPaymentMethod(cr).bind { paymentMethod ->
        Op.transact(paymentMethod)
    }
}

fun main() {
    val opHandler = object: OpHandler {
        override fun <A> handle(op: Op<A>): A = when (op) {
            is Op.CoffeeRequestReaderOp.GetPaymentMethod -> TODO()
            is Op.PaymentTransactorOp.Transact -> TODO()
        }
    }
    makeImpl(TODO()).interp(opHandler)
}