package com.gh.om.gamemacros.complex

import com.gh.om.gamemacros.ColorUtil
import com.gh.om.gamemacros.KeyHooks
import com.gh.om.gamemacros.MouseHooks
import com.gh.om.gamemacros.ScreenCommons
import com.gh.om.gamemacros.currentCoroutineScope
import com.gh.om.gamemacros.isPoeAndTriggerKeyEnabled
import com.gh.om.gamemacros.safeDelay
import com.gh.om.gamemacros.safeDelayK
import com.github.kwhat.jnativehook.keyboard.NativeKeyEvent
import com.github.kwhat.jnativehook.mouse.NativeMouseEvent
import kotlinx.coroutines.flow.stateIn
import net.sourceforge.tess4j.Tesseract
import net.sourceforge.tess4j.TesseractException
import java.awt.Color
import java.awt.Dimension
import java.awt.Image
import java.awt.Point
import java.awt.Rectangle
import java.awt.Robot
import java.awt.Toolkit
import java.awt.datatransfer.DataFlavor
import java.awt.image.BufferedImage
import kotlin.io.path.Path
import kotlin.io.path.div
import kotlin.time.Duration.Companion.milliseconds

object PoeAutoAlt {
    val itemInCurrencyTab = Point(452, 609)
    val altInCurrencyTab = Point(146, 361)

    val intStackWandWiderAffixes = listOf(
        "per 1",
        "Runic",
        "Acclaim",
        "Incision",
        "Destruction",
        "Vapourising",
    )

    val intStackWandPrefixes = listOf(
        // Includes both spell per 16 and lightning per 10
        "per 1",
        // T1 Spell%
        "Runic",
        // T1 Lightning attack#
        "Vapourising",
    )

    val intShield = listOf(
        "Runic",
        // T1 ES
        "Incandescent",
        // T1 ES%
        "Unfaltering",
        // T1 Hybrid ES%
        "Seraphim",
        // T1 Int
        "of the Genius"
    )

    val intShield86 = listOf(
        "Runic",
        // T1 ES%
        "Unfaltering",
        // T1 Int
        "of the Genius"
    )

    suspend fun play() {
        val isPoe = isPoeAndTriggerKeyEnabled()

        suspend fun handle(pressed: Boolean) {
            if (!pressed) {
                return
            }
            repeat(500) {
                if (!isPoe.value) {
                    return
                }
                if (getAndCheckStat(intShield)) {
                    return
                }
                altOnceToItemInCurrencyTab()
            }
        }
        LEADER_KEY.isEnabled("04").collect(::handle)
    }

    private suspend fun getAndCheckStat(checklist: List<String>): Boolean {
        val stat = getItemStatFromCurrencyTab() ?: return false
        val found = checklist.firstOrNull {
            stat.contains(it, ignoreCase = true)
        }
        if (found != null) {
            println("Found $found")
        }
        return found != null
    }

    private suspend fun altOnceToItemInCurrencyTab() {
        MouseHooks.postClick(
            point = altInCurrencyTab,
            moveFirst = true,
            button = NativeMouseEvent.BUTTON2
        )
        safeDelayK(30.milliseconds)
        MouseHooks.postClick(
            point = itemInCurrencyTab,
            moveFirst = true,
            button = NativeMouseEvent.BUTTON1
        )
        safeDelayK(30.milliseconds)
    }

    private suspend fun getItemStatFromCurrencyTab(): String? {
        MouseHooks.moveTo(itemInCurrencyTab)
        safeDelayK(30.milliseconds)

        return getDescriptionOfItemUnderMouse()
    }
}

object PoeRerollKirac {
    // With bag open
    val firstMission = Point(1037, 562)

    // Bottom bar which contains e.g. "Complete the Einhar Mission"
    val missionDescriptionTL = Point(906, 963)
    val missionDescriptionBR = Point(1371, 1059)
    val missionDescriptionSize = Dimension(
        missionDescriptionBR.x - missionDescriptionTL.x,
        missionDescriptionBR.y - missionDescriptionTL.y,
    )
    val missionDescription =
        Rectangle(missionDescriptionTL, missionDescriptionSize)
    val missionDescriptionScaledForAwt =
        scaleFromPhysicalToAwt(missionDescription)

    // Kirac mission grid's size seems to be 72x72, given 2560x1440 screen?
    val gridSizePixels = 72
    val numberOfGrids = 4
    val emptyGridColor = Color(7, 8, 9)

    val userHome =
        Path(System.getProperty("user.home"))
    val tessDataDir = userHome / "Downloads" / "tessdata-4.1.0"

    val tess by lazy {
        Tesseract().apply {
            setVariable("user_defined_dpi", "72")
            setDatapath(tessDataDir.toString())
        }
    }

    val robot by lazy {
        Robot()
    }

    suspend fun main() {
        val isPoe = isPoeAndTriggerKeyEnabled()

        val mousePos =
            MouseHooks.motionEvents().stateIn(currentCoroutineScope())

        suspend fun handle(pressed: Boolean) {
            if (!pressed) {
                return
            }
            val reportPos = mousePos.value.point
            repeat(20) {
                if (!isPoe.value) {
                    return
                }
                if (rerollOnce(reportPos)) {
                    return
                }
            }
        }
        LEADER_KEY.isEnabled("05").collect(::handle)
    }

    fun isMissionOfInterest(description: String): Boolean {
        val needles = listOf(
            "Einhar",
        )

        return needles.any { description.contains(it, ignoreCase = true) }
    }

    suspend fun rerollOnce(reportPos: Point): Boolean {
        // 1. Check if any mission matches
        if (locateMissionThat(::isMissionOfInterest)) {
            // Done!
            return true
        }

        // 2. Do reroll.
        MouseHooks.postClick(
            point = reportPos,
            button = NativeMouseEvent.BUTTON2,
            moveFirst = true,
        )
        return false
    }

    private fun missionGridCoordinates(): Sequence<Point> {
        return sequence {
            for (y in 0 until numberOfGrids) {
                for (x in 0 until numberOfGrids) {
                    val p = Point(firstMission)
                    p.translate(x * gridSizePixels, y * gridSizePixels)
                    yield(p)
                }
            }
        }
    }

    suspend fun locateMissionThat(predicate: (String) -> Boolean): Boolean {
        // 1. Find the non-empty mission grids, by checking grid color.

        // Move cursor to bag to avoid blocking the mission grid.
        MouseHooks.moveTo(PoeCoordinates.emptySpaceInRightSideOfBag)
        safeDelayK(30.milliseconds)

        var i = 0
        fun hasMission(point: Point): Boolean {
            val color = ScreenCommons.INSTANCE.getPixel(
                point.x, point.y
            ) ?: return true
            val dist = ColorUtil.absoluteDistance(color, emptyGridColor)
            i += 1
            return dist > 4
        }

        val missions = missionGridCoordinates().takeWhile(::hasMission)

        // 2. Check each by copying their content.
        for ((i, p) in missions.withIndex()) {
            MouseHooks.moveTo(p)
            // Need larger delay for robot to capture successfully.
            safeDelayK(100.milliseconds)

            val description = getMissionDescription() ?: continue
            if (predicate(description)) {
                // Found
                println("Kirac[$i]: found ${description.take(50)}")
                MouseHooks.postClick(p)
                return true
            }
        }

        return false
    }

    private fun getMissionDescription(): String? {
        val t = Toolkit.getDefaultToolkit()
        // My display setting uses 2.25x scaling,
        // so this method gives much better result.
        val captures = robot
            .createMultiResolutionScreenCapture(missionDescriptionScaledForAwt)
            .resolutionVariants
        val capture = captures.last().toBufferedImage()
        return try {
            tess.doOCR(capture)
        } catch (e: TesseractException) {
            println("Failed to OCR: $e")
            null
        }
    }

    private fun Image.toBufferedImage(): BufferedImage {
        if (this is BufferedImage) {
            return this
        }

        val bi = BufferedImage(
            getWidth(null),
            getHeight(null),
            BufferedImage.TYPE_INT_ARGB
        );

        val g = bi.createGraphics()
        g.drawImage(this, 0, 0, null)
        g.dispose()
        return bi
    }

    private fun scaleFromPhysicalToAwt(r: Rectangle): Rectangle {
        return Rectangle(
            r.x.scaleFromPhysicalToAwt(),
            r.y.scaleFromPhysicalToAwt(),
            r.width.scaleFromPhysicalToAwt(),
            r.height.scaleFromPhysicalToAwt()
        )
    }

    private fun Int.scaleFromPhysicalToAwt(): Int {
        return (this / 2.25).toInt()
    }
}

object PoeCoordinates {
    val firstItemInBag = Point(1727, 813)

    // Moving mouse to here hides any tooltip
    val emptySpaceInRightSideOfBag = Point(2429, 688)
}

object PoeStackedDeck {
    val firstItemInBag = PoeCoordinates.firstItemInBag
    val ground = Point(1628, 813)

    suspend fun unstackEntireStack() {
        val isPoe = isPoeAndTriggerKeyEnabled()

        val mouseEvents =
            MouseHooks.motionEvents().stateIn(currentCoroutineScope())

        suspend fun handle(pressed: Boolean) {
            if (!pressed) {
                return
            }
            // So we can start from any slot in bag
            val initial = mouseEvents.value.point
            repeat(20) {
                if (!isPoe.value) {
                    return
                }
                unstackOnce(initial = initial)
            }
        }
        LEADER_KEY.isEnabled("03").collect(::handle)
    }

    private suspend fun unstackOnce(initial: Point = firstItemInBag) {
        // Right click deck
        MouseHooks.postClick(
            x = initial.x,
            y = initial.y,
            button = NativeMouseEvent.BUTTON2,
            delayMs = 50,
            moveFirst = true,
        )
        safeDelay()
        MouseHooks.postClick(
            x = ground.x,
            y = ground.y,
            button = NativeMouseEvent.BUTTON1,
            delayMs = 50,
            moveFirst = true,
        )
        safeDelay()
    }
}

private suspend fun getDescriptionOfItemUnderMouse(): String? {
    KeyHooks.postPress(NativeKeyEvent.VC_CONTROL)
    safeDelayK(15.milliseconds)
    KeyHooks.postPress(NativeKeyEvent.VC_C)
    safeDelayK(15.milliseconds)
    KeyHooks.postRelease(NativeKeyEvent.VC_C)
    safeDelayK(15.milliseconds)
    KeyHooks.postRelease(NativeKeyEvent.VC_CONTROL)

    // Simulate that humans need 0.1s to read item stat.
    safeDelayK(100.milliseconds)
    return getStringFromClipboard()
}

private fun getStringFromClipboard(): String? {
    val clipboard = Toolkit.getDefaultToolkit().systemClipboard
    val flavor = DataFlavor.stringFlavor
    if (clipboard.isDataFlavorAvailable(flavor)) {
        return clipboard.getData(flavor) as? String
    }
    return null
}
