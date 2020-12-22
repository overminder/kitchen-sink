package com.gh.om.blizzapi

object Util {
    fun expanduser(path: String): String {
        val user = System.getProperty("user.home")
        return path.replaceFirst("~".toRegex(), user)
    }
}
