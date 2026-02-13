package com.gh.om.ks.arpgmacro.app

import java.lang.management.ManagementFactory

// https://stackoverflow.com/a/73125047
fun isDebugging(): Boolean {
    val rt = ManagementFactory.getRuntimeMXBean()
    val args = rt.inputArguments
    val jdwpPresent = args.toString().contains("jdwp")
    return jdwpPresent
}