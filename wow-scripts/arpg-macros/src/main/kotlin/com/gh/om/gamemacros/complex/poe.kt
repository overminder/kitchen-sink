package com.gh.om.gamemacros.complex

import com.gh.om.gamemacros.ColorUtil
import com.gh.om.gamemacros.KeyHooks
import com.gh.om.gamemacros.MouseHooks
import com.gh.om.gamemacros.ScreenCommons
import com.gh.om.gamemacros.complex.PoeDumpBag.bagRows
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
import java.util.regex.Pattern
import kotlin.io.path.Path
import kotlin.io.path.div
import kotlin.time.Duration.Companion.milliseconds

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

    val stackSizePat = Pattern.compile("""Stack Size: (\d+)/""")

    val numberOfGrids = 4

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
            // Find all non-empty bag slots that may have reports
            MouseHooks.moveTo(PoeGraphicConstants.emptySpaceInRightSideOfBag)
            safeDelayK(100.milliseconds)
            val rerollItemSlots = PoeGraphicConstants.allGrids(
                start = PoeGraphicConstants.firstItemInBag,
                rows = bagRows,
                columns = 2,
                gridSize = 70,
            ).filter(PoeGraphicConstants::gridHasItem)

            for (slot in rerollItemSlots) {
                if (!isPoe.value) {
                    return
                }
                if (reroll(slot, isPoe::value)) {
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

    suspend fun reroll(
        reportPos: Point,
        shouldContinue: () -> Boolean,
    ): Boolean {
        // 1. Check if report exists
        MouseHooks.moveTo(reportPos)
        safeDelayK(100.milliseconds)
        val descr = PoeInteractor.getDescriptionOfItemUnderMouse() ?: ""
        val words = listOf("reroll", "report", "kirac")
        if (!words.all { descr.contains(it, ignoreCase = true) }) {
            // Is not a report
            println("${descr.take(100)} is not a report")
            return false
        }

        val stackSizeM = stackSizePat.matcher(descr)
        if (!stackSizeM.find()) {
            println("No stack size found")
            return false
        }
        val stackSize = stackSizeM.group(1).toInt()
        println("Report stack size: $stackSize")

        repeat(stackSize) {
            if (!shouldContinue()) {
                return true
            }

            // 2. Check if any mission matches
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
            safeDelayK(30.milliseconds)
        }

        return false
    }

    private fun missionGridCoordinates(): Sequence<Point> {
        return sequence {
            for (y in 0 until numberOfGrids) {
                for (x in 0 until numberOfGrids) {
                    val p = Point(firstMission)
                    p.translate(
                        x * PoeGraphicConstants.bagGridSize,
                        y * PoeGraphicConstants.bagGridSize
                    )
                    yield(p)
                }
            }
        }
    }

    suspend fun locateMissionThat(predicate: (String) -> Boolean): Boolean {
        // 1. Find the non-empty mission grids, by checking grid color.

        // Move cursor to bag to avoid blocking the mission grid.
        MouseHooks.moveTo(PoeGraphicConstants.emptySpaceInRightSideOfBag)
        safeDelayK(30.milliseconds)

        val missions =
            missionGridCoordinates().takeWhile(PoeGraphicConstants::gridHasItem)

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

/**
 * Moves all items from bag to stash.
 */
object PoeDumpBag {
    val bagRows = 5

    // Not including the last 2 columns -- assuming they hold scrolls.
    val bagColumns = 10

    val mapStashRows = 6
    val mapStashColumns = 12

    suspend fun bagToStash() {
        bagToStashEx(hotkeys = "06", forced = false)
    }

    suspend fun bagToStashForced() {
        bagToStashEx(hotkeys = "08", forced = true)
    }

    suspend fun moveMapFromStashToBag() {
        val isPoe = isPoeAndTriggerKeyEnabled()

        suspend fun handle(pressed: Boolean) {
            if (!pressed) {
                return
            }
            dumpFromSource(
                nameOfSource = "map stash",
                sourceSlots = mapStashSlots(),
                forced = false,
                shouldContinue = isPoe::value
            )
        }
        LEADER_KEY.isEnabled("09").collect(::handle)
    }

    private suspend fun bagToStashEx(
        hotkeys: String,
        forced: Boolean,
    ) {
        val isPoe = isPoeAndTriggerKeyEnabled()

        suspend fun handle(pressed: Boolean) {
            if (!pressed) {
                return
            }
            dumpFromBag(forced, isPoe::value)
        }
        LEADER_KEY.isEnabled(hotkeys).collect(::handle)
    }

    private suspend fun dumpFromBag(
        forced: Boolean,
        shouldContinue: () -> Boolean,
    ) {
        dumpFromSource(
            nameOfSource = "bag",
            sourceSlots = bagSlots(),
            forced = forced,
            shouldContinue = shouldContinue
        )
    }

    private suspend fun dumpFromSource(
        nameOfSource: String,
        sourceSlots: Sequence<Point>,
        forced: Boolean,
        shouldContinue: () -> Boolean,
    ) {

        // Move cursor to bag to avoid blocking the mission grid.
        MouseHooks.moveTo(PoeGraphicConstants.emptySpaceInRightSideOfBag)
        safeDelayK(30.milliseconds)

        // Find the non-empty slots
        val slots = sourceSlots
            .filter(PoeGraphicConstants::gridHasItem)
            .toList()
        println("Non-empty $nameOfSource slots = ${slots.size}")

        for (slot in slots) {
            if (!shouldContinue()) {
                break
            }
            MouseHooks.moveTo(slot)
            safeDelayK(30.milliseconds)

            suspend fun doClick() {
                MouseHooks.postClick(slot)
                safeDelayK(30.milliseconds)
            }

            if (forced) {
                // Ctrl-shift-click
                PoeInteractor.withControlPressed {
                    KeyHooks.withModifierKey(NativeKeyEvent.VC_SHIFT, ::doClick)
                }
            } else {
                // Ctrl-click
                PoeInteractor.withControlPressed(::doClick)
            }
        }
    }

    private fun bagSlots() = PoeGraphicConstants.allGrids(
        start = PoeGraphicConstants.firstItemInBag,
        rows = bagRows,
        columns = bagColumns,
        gridSize = 70,
    )

    private fun mapStashSlots() = PoeGraphicConstants.allGrids(
        start = PoeGraphicConstants.firstItemInMapStash,
        rows = mapStashRows,
        columns = mapStashColumns,
        gridSize = 64,
    )
}

object PoeGraphicConstants {
    val firstItemInBag = Point(1727, 813)
    val firstItemInMapStash = Point(88, 642)

    // Moving mouse to here hides any tooltip
    val emptySpaceInRightSideOfBag = Point(2429, 688)

    // Kirac mission grid's size seems to be 70x70, given 2560x1440 screen?
    // Bag seems to also be 70
    // Map stash OTOH is 64.
    val bagGridSize = 70
    val mapGridSize = 64
    val emptyGridColor = Color(7, 8, 9)

    fun allGrids(
        start: Point,
        rows: Int,
        columns: Int,
        gridSize: Int,
    ) = sequence {
        // Assuming filled by columns, but that shouldn't matter if
        // the consuming sites do the emptiness check first.
        for (x in 0 until columns) {
            for (y in 0 until rows) {
                val p = Point(start)
                p.translate(
                    x * gridSize,
                    y * gridSize
                )
                yield(p)
            }
        }
    }

    /**
     * A "grid" as in bag slot or kirac mission slot.
     */
    fun gridHasItem(point: Point): Boolean {
        val color = ScreenCommons.INSTANCE.getPixel(
            point.x, point.y
        ) ?: return true
        val dist = ColorUtil.absoluteDistance(
            color,
            emptyGridColor
        )
        // println("$point color = $color, dist = $dist")
        return dist > 4
    }
}

object PoeStackedDeck {
    val firstItemInBag = PoeGraphicConstants.firstItemInBag
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

object PoeInteractor {
    suspend fun withControlPressed(inner: suspend () -> Unit) {
        KeyHooks.withModifierKey(NativeKeyEvent.VC_CONTROL, inner)
    }

    // For copying advanced item description
    suspend fun withControlAltPressed(inner: suspend () -> Unit) {
        withControlPressed {
            KeyHooks.withModifierKey(NativeKeyEvent.VC_ALT, inner)
        }
    }

    suspend fun getDescriptionOfItemUnderMouse(): String? {
        withControlPressed {
            KeyHooks.postPress(NativeKeyEvent.VC_C)
            safeDelayK(15.milliseconds)
            KeyHooks.postRelease(NativeKeyEvent.VC_C)
            safeDelayK(15.milliseconds)
        }

        // Simulate that humans need 0.1s to read item stat.
        safeDelayK(100.milliseconds)
        return getStringFromClipboard()
    }

    suspend fun getAdvancedDescriptionOfItemUnderMouse(): String? {
        withControlAltPressed {
            KeyHooks.postPress(NativeKeyEvent.VC_C)
            safeDelayK(30.milliseconds)
            KeyHooks.postRelease(NativeKeyEvent.VC_C)
            safeDelayK(30.milliseconds)
        }

        // Simulate that humans need 0.1s to read item stat.
        safeDelayK(100.milliseconds)
        return getStringFromClipboard()
    }
}


private fun getStringFromClipboard(): String? {
    val clipboard = Toolkit.getDefaultToolkit().systemClipboard
    val flavor = DataFlavor.stringFlavor
    if (clipboard.isDataFlavorAvailable(flavor)) {
        return clipboard.getData(flavor) as? String
    }
    return null
}
