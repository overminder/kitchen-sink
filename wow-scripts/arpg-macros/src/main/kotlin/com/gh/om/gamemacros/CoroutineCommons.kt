@file:OptIn(ExperimentalCoroutinesApi::class, FlowPreview::class)

package com.gh.om.gamemacros

import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.FlowPreview
import kotlinx.coroutines.currentCoroutineContext
import kotlinx.coroutines.flow.Flow
import kotlinx.coroutines.flow.transformLatest
import kotlinx.coroutines.time.delay
import kotlinx.coroutines.time.sample
import java.time.Duration

suspend fun currentCoroutineScope() =
    CoroutineScope(currentCoroutineContext())

fun <A> Flow<A>.sampleAndReemit(
    interval: Duration
): Flow<A> {
    return transformLatest {
        while (true) {
            emit(it)
            delay(interval)
        }
    }.sample(interval)
}

fun <A> Flow<A>.asNullable(): Flow<A?> = this
