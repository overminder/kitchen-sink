package macrocore

fun KeyboardOutput.postPressRelease(key: String) {
    postPress(key)
    postRelease(key)
}

fun KeyboardOutput.postAsciiString(string: String) {
    for (c in string) {
        postPressRelease(c.toString())
    }
}
