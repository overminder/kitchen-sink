package com.om.kitsink.layoutpg

import java.awt.BasicStroke
import java.awt.Color
import java.awt.Dimension
import java.awt.Graphics2D
import java.awt.Point
import java.awt.Rectangle
import java.lang.Integer.max
import java.lang.Integer.min

// Try functional views

data class MeasureSpec(val size: Int, val kind: Kind) {
    companion object {
        fun exactly(size: Int) = MeasureSpec(size, Kind.Exactly)
        fun atMost(size: Int) = MeasureSpec(size, Kind.AtMost)
        fun unspecified(size: Int) = MeasureSpec(size, Kind.Unspecified)
    }

    enum class Kind {
        Exactly,
        AtMost,
        Unspecified,
    }
}

sealed class SizeSpec {
    object MatchParent : SizeSpec()
    object WrapContent : SizeSpec()
    object MatchConstraints : SizeSpec()
    data class Exactly(val value: Int) : SizeSpec()
}

open class TwoDimension<A: Any>(open val width: A, open val height: A)

data class LayoutParams(
    override val width: SizeSpec = SizeSpec.WrapContent,
    override val height: SizeSpec = SizeSpec.WrapContent
): TwoDimension<SizeSpec>(width, height)

enum class Orientation {
    Vertical,
    Horizontal,
}

typealias OChildView = Pair<ONonRootView, LayoutParams>

sealed class OView
data class ORootViewGroup(val dimen: Dimension, val child: OChildView): OView()
sealed class ONonRootView: OView()
data class ORectView(val strokeColor: Color): ONonRootView()
data class OStackViewGroup(
    val orientation: Orientation,
    val children: List<OChildView>
): ONonRootView()

class ByRef<out A: Any>(val value: A) {
    override fun equals(other: Any?): Boolean {
        if (other is ByRef<*>) {
            return value === other.value
        }
        return false
    }

    override fun hashCode(): Int {
        return value.hashCode()
    }
}

class LayoutContext {
    val measurements = mutableMapOf<ByRef<OView>, Dimension>()
    // Relative to parent.
    val arrangements = mutableMapOf<ByRef<OView>, Point>()

    fun paint(rv: ORootViewGroup, out: Graphics2D) {
        measure(rv)
        arrange(rv)
        draw(rv, out)
    }

    fun measure(rv: ORootViewGroup) {
        val (cv, lp) = rv.child
        measure(cv, asMeasureSpec(lp, rv.dimen))

        measurements += ByRef(rv) to rv.dimen
    }

    fun arrange(rv: ORootViewGroup) {
        val origin = Point()
        arrangements += ByRef(rv) to origin
        val (cv, _) = rv.child
        arrange(cv)
    }

    private fun draw(rv: ORootViewGroup, out: Graphics2D) {
        // Nothing to draw for rv.
        val (cv, _) = rv.child
        val origin = requireNotNull(arrangements[ByRef(rv)])
        draw(cv, origin, out)
    }

    private fun draw(v: ONonRootView, origin: Point, out: Graphics2D) {
        val vRef = ByRef(v)
        val dimen = requireNotNull(measurements[vRef])
        val offset = requireNotNull(arrangements[vRef])
        val position = origin.translated(offset)
        when (v) {
            is ORectView -> {
                val rect = Rectangle(position, dimen)
                out.stroke = BasicStroke(1.0f)
                out.color = v.strokeColor
                out.background = Color.WHITE
                out.draw(rect)
            }
            else -> TODO("$v")
        }
    }

    private fun arrange(v: ONonRootView) {
        val origin = Point()
        arrangements += ByRef(v) to origin
    }

    private fun measure(v: ONonRootView, specs: TwoDimension<MeasureSpec>): Dimension {
        val res = measureCore(v, specs)
        measurements += ByRef(v) to res
        return res
    }

    private fun measureCore(v: ONonRootView, specs: TwoDimension<MeasureSpec>): Dimension {
        return when (v) {
            is ORectView -> {
                // For views that don't have a size, be as large as possible.
                val w = specs.width.size
                val h = specs.height.size
                Dimension(w, h)
            }
            is OStackViewGroup -> {
                var availW = specs.width
                var availH = specs.height
                var accH = 0
                var accW = 0
                for ((cv, lp) in v.children) {
                    val dimen = measure(cv, TwoDimension(availW, availH))
                    if (v.orientation == Orientation.Horizontal) {
                        availW -= dimen.width
                        accW += dimen.width
                        accH = max(dimen.height, accH)
                    } else {
                        accW = max(dimen.width, accW)
                        accH += dimen.height
                        availH -= dimen.height
                    }
                }
                Dimension(accW, accH)
            }
            else -> TODO("$v")
        }
    }

    private fun asMeasureSpec(spec: SizeSpec, maxSize: Int): MeasureSpec {
        return when (spec) {
            is SizeSpec.WrapContent -> MeasureSpec.atMost(maxSize)
            is SizeSpec.MatchParent -> MeasureSpec.exactly(maxSize)
            is SizeSpec.Exactly -> MeasureSpec.exactly(min(maxSize, spec.value))
            else -> error("Unexpected spec: $spec")
        }
    }

    private fun asMeasureSpec(specs: TwoDimension<SizeSpec>, maxSizes: Dimension): TwoDimension<MeasureSpec> {
        return TwoDimension(
            asMeasureSpec(specs.width, maxSizes.width),
            asMeasureSpec(specs.height, maxSizes.height))
    }
}

private operator fun MeasureSpec.minus(offset: Int): MeasureSpec {
    return copy(size = size - offset)
}

private fun Point.translated(offset: Point): Point {
    val copy = Point(this)
    copy.translate(offset.x, offset.y)
    return copy
}

