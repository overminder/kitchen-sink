package com.github.om.ioccmp.trad

import com.github.om.ioccmp.*

fun provideRequestHandler(bank: HwBank): CoffeeRequestHandler<CoffeeRequest, CoffeePackage> {
    return TypedCoffeeRequestHandlerImpl(
        HwCoffeeRequestReader,
        HwCurrencyUtil,
        HwPaymentTransactor(bank),
        HwCoffeePackager,
        HwCoffeeMaker,
        HwCoffeeRequest::class.java,
    )
}
