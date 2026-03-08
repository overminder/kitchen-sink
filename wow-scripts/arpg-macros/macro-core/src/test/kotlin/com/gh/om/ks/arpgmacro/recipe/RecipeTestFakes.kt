@file:OptIn(kotlinx.coroutines.ExperimentalCoroutinesApi::class)

package com.gh.om.ks.arpgmacro.recipe

import com.gh.om.ks.arpgmacro.core.ActiveWindowChecker
import com.gh.om.ks.arpgmacro.core.Clock
import com.gh.om.ks.arpgmacro.core.KeyboardInput
import com.gh.om.ks.arpgmacro.core.KeyboardOutput
import kotlinx.coroutines.flow.Flow
import kotlinx.coroutines.flow.MutableSharedFlow
import kotlinx.coroutines.test.TestScope
import kotlin.time.Duration

class FakeKeyboardInput : KeyboardInput {
    private val pressFlow = MutableSharedFlow<String>(extraBufferCapacity = 16)
    private val releaseFlow = MutableSharedFlow<String>(extraBufferCapacity = 16)

    override fun keyPresses(): Flow<String> = pressFlow
    override fun keyReleases(): Flow<String> = releaseFlow

    fun press(key: String) { pressFlow.tryEmit(key) }
    fun release(key: String) { releaseFlow.tryEmit(key) }
}

class FakeKeyboardOutput : KeyboardOutput {
    val pressed = mutableListOf<String>()
    val released = mutableListOf<String>()
    override fun postPress(key: String) { pressed += key }
    override fun postRelease(key: String) { released += key }
}

class FakeActiveWindowChecker(var active: Boolean = true) : ActiveWindowChecker {
    override fun isActiveWindow(anyTitles: Collection<String>) = active
}

class FakeClock(private val scope: TestScope) : Clock {
    override fun currentTimeMillis(): Long = scope.testScheduler.currentTime
    override suspend fun delay(duration: Duration, extraVarianceMs: Long) =
        kotlinx.coroutines.delay(duration)
}
