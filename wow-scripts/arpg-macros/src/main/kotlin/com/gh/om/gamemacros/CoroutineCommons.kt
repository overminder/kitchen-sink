@file:OptIn(ExperimentalCoroutinesApi::class, FlowPreview::class)

package com.gh.om.gamemacros

import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.FlowPreview
import kotlinx.coroutines.currentCoroutineContext
import kotlinx.coroutines.flow.Flow
import kotlinx.coroutines.flow.transformLatest
import kotlinx.coroutines.time.delay
import java.time.Duration
import kotlin.random.Random
import kotlin.time.Duration.Companion.milliseconds
import kotlin.time.toJavaDuration

suspend fun currentCoroutineScope() =
    CoroutineScope(currentCoroutineContext())

fun <A> Flow<A>.sampleAndReemit(
    interval: Duration
): Flow<A> {
    return transformLatest {
        while (true) {
            emit(it)
            safeDelay(interval)
        }
    }
}

fun <A> Flow<A>.asNullable(): Flow<A?> = this

/**
 * Safe in the sense that there's a random variance
 */
suspend fun safeDelay(
    duration: Duration = Duration.ofMillis(100),
    extraMillis: Long = 10
) {
    val changedDuration = duration.toMillis() + Random.nextLong(0, extraMillis)
    delay(Duration.ofMillis(changedDuration))
}

suspend fun safeDelayK(
    duration: kotlin.time.Duration = 100.milliseconds,
    extraMillis: Long = 10
) {
    val changedDuration =
        duration + Random.nextLong(0, extraMillis).milliseconds
    delay(changedDuration.toJavaDuration())
}
