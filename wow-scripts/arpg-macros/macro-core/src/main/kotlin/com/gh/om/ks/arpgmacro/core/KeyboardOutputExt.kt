package com.gh.om.ks.arpgmacro.core

import kotlin.text.iterator

fun KeyboardOutput.postPressRelease(key: String) {
    postPress(key)
    postRelease(key)
}

fun KeyboardOutput.postAsciiString(string: String) {
    for (c in string) {
        postPressRelease(c.toString())
    }
}
