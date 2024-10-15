package com.gh.om.gamemacros

enum class OS {
    Mac,
    Windows,
    Linux;

    companion object {
        val CURRENT = PlatformInferrer.getOs()
    }
}

private object PlatformInferrer {

    fun getOs(): OS? {
        //
        val osName = System.getProperty("os.name", "generic").lowercase()
        return when {
            osName.indexOf("mac") >= 0 || osName.indexOf("darwin") >= 0 -> {
                OS.Mac
            }
            osName.indexOf("win") >= 0 -> {
                OS.Windows
            }
            osName.indexOf("nux") >= 0 -> {
                OS.Linux
            }
            else -> {
                null
            }
        }
    }
}
