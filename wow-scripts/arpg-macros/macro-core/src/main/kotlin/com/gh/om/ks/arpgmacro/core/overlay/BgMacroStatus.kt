package com.gh.om.ks.arpgmacro.core.overlay

import com.gh.om.ks.arpgmacro.core.Clock
import kotlinx.coroutines.flow.MutableStateFlow
import kotlinx.coroutines.flow.StateFlow
import kotlinx.coroutines.flow.asStateFlow
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.ConcurrentLinkedDeque
import javax.inject.Inject

/** Receives key-press events from background macros. */
interface BgMacroEventSink {
    fun onKeyPress(macroName: String, key: String)
}

data class BgMacroStatusLine(
    val macroName: String,
    val keyCounts: List<Pair<String, Int>>,
    val runningDurationSecs: Long,
)

class BgMacroStatusTracker @Inject constructor(private val clock: Clock) : BgMacroEventSink {
    private val recentWindowMs = 15_000L

    private val events = ConcurrentLinkedDeque<BgMacroEvent>()
    private val firstSeen = ConcurrentHashMap<String, Long>()

    private val _status = MutableStateFlow<List<BgMacroStatusLine>>(emptyList())
    val status: StateFlow<List<BgMacroStatusLine>> = _status.asStateFlow()

    override fun onKeyPress(macroName: String, key: String) {
        val now = clock.currentTimeMillis()
        val cutoff = now - recentWindowMs
        val hadRecentEvents = events.any { it.macroName == macroName && it.timestamp >= cutoff }
        events.addLast(BgMacroEvent(macroName, key, now))
        if (hadRecentEvents) {
            firstSeen.putIfAbsent(macroName, now)
        } else {
            firstSeen[macroName] = now
        }
        recompute(now)
    }

    fun tick() {
        recompute(clock.currentTimeMillis())
    }

    private fun recompute(now: Long) {
        val cutoff = now - recentWindowMs
        while (events.peekFirst()?.let { it.timestamp < cutoff } == true) {
            events.pollFirst()
        }
        val grouped = events.groupBy { it.macroName }
        firstSeen.keys.retainAll(grouped.keys)
        val lines = grouped.entries.map { (macroName, macroEvents) ->
            val keyCounts = macroEvents
                .groupingBy { it.key }
                .eachCount()
                .entries
                .sortedWith(compareByDescending<Map.Entry<String, Int>> { it.value }.thenBy { it.key })
                .map { it.key to it.value }
            val startTime = firstSeen[macroName] ?: now
            BgMacroStatusLine(
                macroName = macroName,
                keyCounts = keyCounts,
                runningDurationSecs = (now - startTime) / 1000L,
            )
        }
        _status.value = lines
    }
}

private data class BgMacroEvent(
    val macroName: String,
    val key: String,
    val timestamp: Long,
)
