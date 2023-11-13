package com.gh.om.g.observer.listv1

import io.kotest.core.spec.style.StringSpec
import io.kotest.property.forAll

class HelloWorld : StringSpec(
    {
        "foo" {
            forAll<String, String> { a, b ->
                (a + b).length == a.length + b.length
            }
        }
    })
