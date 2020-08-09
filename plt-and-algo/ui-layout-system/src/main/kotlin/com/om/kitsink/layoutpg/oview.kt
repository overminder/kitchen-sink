package com.om.kitsink.layoutpg

import java.awt.BasicStroke
import java.awt.Color
import java.awt.Dimension
import java.awt.Graphics2D
import java.awt.Point
import java.awt.Rectangle
import java.lang.Integer.min
import kotlin.math.max

// Not very familiar with OO style views

/*


interface OView {
    fun paint(g: Graphics2D)
    fun measure(args: Pair<MeasureSpec, MeasureSpec>?): Dimension
    fun arrange()
    fun onMeasure(width: MeasureSpec, height: MeasureSpec): Dimension
    fun onArrange(pos: Point, size: Dimension)
}

interface OViewGroup: OView {
    val subviewsSnapshot: Sequence<Pair<OView, LayoutParams>>

    fun addView(v: OView, lp: LayoutParams)
}

abstract class OBaseView: OView {
    protected var lastMeasureArgs: Pair<MeasureSpec, MeasureSpec>? = null
    protected var lastMeasureResults: Dimension? = null

    override fun measure(args: Pair<MeasureSpec, MeasureSpec>?): Dimension {
        val (width, height) = requireNotNull(args ?: lastMeasureArgs)
        val dimen = onMeasure(width, height)
        lastMeasureArgs = width to height
        lastMeasureResults = dimen
        return dimen
    }

    override fun arrange() {
        val dimen = requireNotNull(lastMeasureResults)
        onArrange(Point(), dimen)
    }
}

abstract class OBaseViewGroup: OBaseView(), OViewGroup {
    override val subviewsSnapshot
        get() = subviews.asSequence().map { it.toPair() }

    protected val subviews = mutableMapOf<OView, LayoutParams>()

    override fun addView(v: OView, lp: LayoutParams) {
        require(verifyLayoutParams(v, lp)) {
            "$v can't be added with $lp"
        }
        subviews += v to lp
    }

    abstract fun verifyLayoutParams(v: OView, lp: LayoutParams): Boolean

    override fun paint(g: Graphics2D) {
        for (ch in subviews) {
            ch.key.paint(g)
        }
    }
}

private fun verifyLayoutParamsBy(lp: LayoutParams, p: (SizeSpec) -> Boolean): Boolean {
    return p(lp.width) && p(lp.height)
}

class ORootView(val dimen: Dimension): OBaseViewGroup() {
    override fun measure(args: Pair<MeasureSpec, MeasureSpec>?): Dimension {
        assert(args == null)
        return super.measure(MeasureSpec.unspecified(0) to MeasureSpec.unspecified(0))
    }

    override fun onMeasure(width: MeasureSpec, height: MeasureSpec): Dimension {
        // Ignoring width / height

        var res = Dimension()
        for (sv in subviews) {
            val lp = sv.value
            val ws = asMeasureSpec(lp.width, dimen.width)
            val hs = asMeasureSpec(lp.height, dimen.height)
            res = res.max(sv.key.measure(ws to hs))
        }
        return res
    }

    override fun verifyLayoutParams(v: OView, lp: LayoutParams): Boolean {
        return verifyLayoutParamsBy(lp, ::verifySizeSpec)
    }

    private fun asMeasureSpec(spec: SizeSpec, size: Int): MeasureSpec {
        return when (spec) {
            is SizeSpec.WrapContent -> MeasureSpec.atMost(size)
            is SizeSpec.MatchParent -> MeasureSpec.exactly(size)
            is SizeSpec.Exactly -> MeasureSpec.exactly(min(size, spec.value))
            else -> error("Unexpected spec: $this")
        }
    }

    private fun verifySizeSpec(spec: SizeSpec): Boolean {
        return when (spec) {
            is SizeSpec.WrapContent -> true
            is SizeSpec.MatchParent -> true
            is SizeSpec.Exactly -> true
            else -> false
        }
    }
}

private fun Dimension.max(other: Dimension): Dimension {
    return Dimension(max(width, other.width), max(height, other.height))
}

class OConstraintLayout(): OBaseViewGroup() {
}

class ORectView : OView {
    val rect = Rectangle(Point(0, 0), Dimension(10, 10))
    override fun paint(g: Graphics2D) {
        g.stroke = BasicStroke(1.0f)
        g.color = Color.BLUE
        g.background = Color.WHITE

        g.draw(rect)
    }
}


 */
