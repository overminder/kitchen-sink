package com.github.om.ioccmp

interface CoffeeRequest

interface PaymentMethod
interface Currency
interface CoffeeBean
interface Coffee
interface CoffeePackage

class CoffeeException(val reason: CoffeeErrorCode) : RuntimeException(messageFor(reason)) {
    companion object {
        fun messageFor(reason: CoffeeErrorCode): String {
            return "CoffeeException: $reason"
        }
    }
}

enum class CoffeeErrorCode {
    DoNotUnderstandRequest,
    TransactionNotOk,
}

interface CoffeeRequestReader<in R : CoffeeRequest, out PM : PaymentMethod, out CU : Currency, out CB : CoffeeBean> {
    fun paymentMethod(coffeeRequest: R): PM
    fun unitPrice(coffeeRequest: R): CU
    fun numberOfUnits(coffeeRequest: R): Int
    fun beanType(coffeeRequest: R): CB
}

interface CurrencyUtil<C : Currency> {
    /** invariant: n >= 1 */
    fun multiply(c: C, n: Int): C
}

interface CoffeePackager<in C : Coffee> {
    fun createPackageBuilder(): CoffeePackageBuilder<C>
}

interface CoffeePackageBuilder<in C : Coffee> {
    operator fun plusAssign(coffee: C)
    fun build(): CoffeePackage
}

interface PaymentTransactor<in P : PaymentMethod, in C : Currency> {
    fun transact(method: P, price: C): Boolean
}

interface CoffeeRequestHandler<in CR : CoffeeRequest, out CP : CoffeePackage> {
    fun handle(request: CR): CP
}

interface CoffeeMaker<in CB : CoffeeBean, out C : Coffee> {
    fun brew(bean: CB): C
}
