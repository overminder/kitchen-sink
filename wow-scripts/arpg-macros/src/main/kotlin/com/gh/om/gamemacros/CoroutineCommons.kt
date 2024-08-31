package com.gh.om.gamemacros

import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.currentCoroutineContext

suspend fun currentCoroutineScope() =
    CoroutineScope(currentCoroutineContext())
