package com.gh.om.ks.arpgmacro.app

import com.gh.om.ks.arpgmacro.core.Clock
import kotlin.random.Random
import kotlin.time.Duration
import kotlin.time.Duration.Companion.milliseconds

class RealClock : Clock {
    override fun currentTimeMillis(): Long = System.currentTimeMillis()

    override suspend fun delay(duration: Duration, extraVarianceMs: Long) {
        val variance = if (extraVarianceMs > 0) Random.nextLong(0, extraVarianceMs) else 0
        val total = duration + variance.milliseconds
        kotlinx.coroutines.delay(total)
    }
}
