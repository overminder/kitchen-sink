package com.github.om.ioccmp

import java.math.BigDecimal

data class HwCreditCard(val cardNumber: String) : PaymentMethod
data class HwUsd(val amount: BigDecimal) : Currency

enum class HwCoffeeBean : CoffeeBean {
    WellDone,
    MediumRare,
}

data class HwCoffee(val bean: HwCoffeeBean) : Coffee

data class HwMutCoffeePackage(val items: MutableList<HwCoffee> = mutableListOf()) : CoffeePackageBuilder<HwCoffee> {
    override fun plusAssign(coffee: HwCoffee) {
        items += coffee
    }

    override fun build(): CoffeePackage {
        return HwCoffeePackage(items.toList())
    }
}

data class HwCoffeePackage(val items: List<HwCoffee>) : CoffeePackage

data class HwCoffeeRequest(
    val paymentMethod: HwCreditCard,
    val numberOfUnits: Int,
    val beanType: HwCoffeeBean,
) : CoffeeRequest

object HwCoffeeRequestReader : CoffeeRequestReader<HwCoffeeRequest, HwCreditCard, HwUsd, HwCoffeeBean> {
    override fun paymentMethod(coffeeRequest: HwCoffeeRequest): HwCreditCard {
        return coffeeRequest.paymentMethod
    }

    override fun unitPrice(coffeeRequest: HwCoffeeRequest): HwUsd {
        return when (coffeeRequest.beanType) {
            HwCoffeeBean.WellDone -> HwUsd(BigDecimal.ONE)
            HwCoffeeBean.MediumRare -> HwUsd((2).toBigDecimal())
        }
    }

    override fun numberOfUnits(coffeeRequest: HwCoffeeRequest): Int {
        return coffeeRequest.numberOfUnits
    }

    override fun beanType(coffeeRequest: HwCoffeeRequest): HwCoffeeBean {
        return coffeeRequest.beanType
    }
}

class HwPaymentTransactor(private val bank: HwBank) : PaymentTransactor<HwCreditCard, HwUsd> {
    override fun transact(method: HwCreditCard, price: HwUsd): Boolean {
        return bank.transactCreditCard(method.cardNumber, price)
    }
}

interface HwBank {
    fun transactCreditCard(cardNumber: String, price: HwUsd): Boolean
}

object HwCurrencyUtil : CurrencyUtil<HwUsd> {
    override fun multiply(c: HwUsd, n: Int): HwUsd {
        return HwUsd(c.amount.multiply(n.toBigDecimal()))
    }
}

object HwCoffeePackager : CoffeePackager<HwCoffee> {
    override fun createPackageBuilder(): CoffeePackageBuilder<HwCoffee> {
        return HwMutCoffeePackage()
    }
}

object HwCoffeeMaker : CoffeeMaker<HwCoffeeBean, HwCoffee> {
    override fun brew(bean: HwCoffeeBean): HwCoffee {
        return HwCoffee(bean)
    }
}
