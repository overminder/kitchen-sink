package com.github.om.ioccmp.trad

import com.github.om.ioccmp.*

// Generic impl

// Note that the internal types unfortunately have to be parametrized or monomorphized (or we have to add runtime
// type checking).
// If a type is purely internal (e.g. PaymentMethod), it will eventually be erased... But only until it's
// not needed. We have to keep maintaining them before then. (Sounds like GC in type system?)
class TypedCoffeeRequestHandlerImpl<CR : CoffeeRequest, CU : Currency, PM : PaymentMethod, C : Coffee, CB : CoffeeBean>(
    private val requestReader: CoffeeRequestReader<CR, PM, CU, CB>,
    private val currencyUtil: CurrencyUtil<CU>,
    private val coffeeTransactor: PaymentTransactor<PM, CU>,
    private val coffeePackager: CoffeePackager<C>,
    private val coffeeMaker: CoffeeMaker<CB, C>,
    private val requestClass: Class<CR>,
) : CoffeeRequestHandler<CoffeeRequest, CoffeePackage> {
    override fun handle(request: CoffeeRequest): CoffeePackage {
        if (!requestClass.isInstance(request)) {
            throw CoffeeException(CoffeeErrorCode.DoNotUnderstandRequest)
        }
        @Suppress("NAME_SHADOWING")
        val request = requestClass.cast(request)

        val numberOfUnits = requestReader.numberOfUnits(request)
        val price = currencyUtil.multiply(requestReader.unitPrice(request), n = numberOfUnits)
        val transactOk = coffeeTransactor.transact(
            method = requestReader.paymentMethod(request),
            price = price
        )
        if (!transactOk) {
            throw CoffeeException(CoffeeErrorCode.TransactionNotOk)
        }

        val beanType = requestReader.beanType(request)
        val builder = coffeePackager.createPackageBuilder()
        repeat(numberOfUnits) {
            builder += coffeeMaker.brew(beanType)
        }
        return builder.build()
    }
}
