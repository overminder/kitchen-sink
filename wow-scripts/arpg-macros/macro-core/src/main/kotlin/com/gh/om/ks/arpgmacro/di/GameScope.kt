package com.gh.om.ks.arpgmacro.di

/**
 * The subcomponent statically knows which [GameType] is for this scope.
 */
annotation class GameScope()

enum class GameType {
    POE1,
    POE2,
    Diablo3,
    Diablo4;

    companion object {
        val ALL_POE = listOf(POE1, POE2)
        val ALL_DIABLO = listOf(Diablo3, Diablo4)
    }
}
