package com.gh.om.gamemacros

import java.awt.Color
import java.awt.Image
import java.awt.Point
import java.awt.Rectangle
import java.awt.Robot
import java.awt.image.BufferedImage

fun main() {
    Thread.sleep(3000)
    AwtRobotUtil.capture(Rectangle(2560, 1440))
    Thread.sleep(1000)
    val t0 = System.nanoTime()
    AwtRobotUtil.capture(Rectangle(2560, 1440))
    val t1 = System.nanoTime()
    println("dt = ${(t1 - t0) / 1000_000}")
}

object AwtRobotUtil {
    private val threadLocalRobot = ThreadLocal.withInitial(::Robot)

    fun capture(physicalRect: Rectangle): BufferedImage {
        val rect = scaleFromPhysicalToAwt(physicalRect)
        val captures = threadLocalRobot.get()
            .createMultiResolutionScreenCapture(rect)
            .resolutionVariants
        return captures.last().toBufferedImage()
    }

    fun captureScreen(): PixelGetter {
        // Simply do a full screen capture first
        val rect = Rectangle(2560, 1440)
        val image = capture(rect)
        return PixelGetter {
            val rgb = image.getRGB(it.x, it.y)
            Color(rgb)
        }
    }

    fun batchGetPixels(points: List<Point>): List<Color> {
        val pg = captureScreen()
        return points.map(pg::get)
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

fun interface PixelGetter {
    fun get(point: Point): Color
}

fun PixelGetter.get(
    x: Int,
    y: Int,
): Color {
    return get(Point(x, y))
}
