package com.github.om.ioccmp.reader

import com.github.om.ioccmp.*

// Probably worth making this an anonymous sum type (HList), to be less verbose.
interface RequestHandlerComponent<CR : CoffeeRequest, CU : Currency, PM : PaymentMethod, C : Coffee, CB : CoffeeBean> {
    val requestReader: CoffeeRequestReader<CR, PM, CU, CB>
    val currencyUtil: CurrencyUtil<CU>
    val coffeeTransactor: PaymentTransactor<PM, CU>
    val coffeePackager: CoffeePackager<C>
    val coffeeMaker: CoffeeMaker<CB, C>
    val requestClass: Class<CR>
}

class CoffeeRequestHandlerImpl<CR : CoffeeRequest, CU : Currency, PM : PaymentMethod, C : Coffee, CB : CoffeeBean> {
    val handle = ReaderModule<RequestHandlerComponent<CR, CU, PM, C, CB>>().reader(::doHandle)

    private fun doHandle(comp: RequestHandlerComponent<CR, CU, PM, C, CB>): (CoffeeRequest) -> CoffeePackage {
        return { request ->
            with(comp) {
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
                builder.build()
            }
        }
    }
}