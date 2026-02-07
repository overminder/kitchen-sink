package macroapp

import com.sun.jna.Native
import com.sun.jna.platform.win32.WinDef.HDC
import com.sun.jna.platform.win32.User32
import macrocore.PixelSource
import macrocore.Screen
import macrocore.ScreenColor
import macrocore.ScreenPoint
import java.awt.Rectangle
import java.awt.Robot
import java.awt.image.BufferedImage

/**
 * Direct JNA binding for GDI32 GetPixel (not available in jna-platform's GDI32).
 */
private object Gdi32 {
    init {
        Native.register("gdi32")
    }

    @JvmStatic
    external fun GetPixel(hdc: HDC, x: Int, y: Int): Int
}

class Win32Screen : Screen {
    override fun getPixelColor(point: ScreenPoint): ScreenColor {
        val dc = User32.INSTANCE.GetDC(null)
        try {
            val colorRef = Gdi32.GetPixel(dc, point.x, point.y)
            val r = colorRef and 0xFF
            val g = (colorRef shr 8) and 0xFF
            val b = (colorRef shr 16) and 0xFF
            return ScreenColor(r, g, b)
        } finally {
            User32.INSTANCE.ReleaseDC(null, dc)
        }
    }

    override fun captureScreen(): PixelSource {
        val robot = Robot()
        val rect = Rectangle(2560, 1440)
        val image: BufferedImage = robot.createScreenCapture(rect)
        return object : PixelSource {
            override fun getPixelColor(point: ScreenPoint): ScreenColor {
                val rgb = image.getRGB(point.x, point.y)
                val r = (rgb shr 16) and 0xFF
                val g = (rgb shr 8) and 0xFF
                val b = rgb and 0xFF
                return ScreenColor(r, g, b)
            }
        }
    }
}
