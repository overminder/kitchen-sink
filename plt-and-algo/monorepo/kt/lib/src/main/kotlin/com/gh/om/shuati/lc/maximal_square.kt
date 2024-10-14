package com.gh.om.shuati.lc

import kotlin.math.min

// https://leetcode.com/problems/maximal-square

fun main() {
    val input = Array(300) {
        CharArray(300) {
            OCCUPIED
        }
    }
    val t0 = System.nanoTime()
    val output = dp(input)
    val t1 = System.nanoTime()
    println("$output, took ${(t1 - t0) / 1000_000}ms")
}

/**
 * Reusing previous results: We can observe that a larger square
 * must be composed of 4 smaller squares. This means we could iteratively merge
 * smaller squares until no larger squares can be found.
 * Time complexity:
 * - m*n time to find 1-sized squares
 * - (m-2)*(n-2)*4 time to find 2-sized squares
 * - (m-4)*(n-4)*4 time to find 3-sized squares
 */

class Solution {
    fun maximalSquare(matrix: Array<CharArray>): Int {
        return tle1(matrix)
    }
}

private const val OCCUPIED = '1'

/*

private typealias FastPair = Long
private fun fastPair(x: Int, y: Int): FastPair {
    return x.toLong().shl(32).or(y.toLong())
}

private fun xOfFastPair(xy: FastPair): Int = xy.shr(32).toInt()
private fun yOfFastPair(xy: FastPair): Int = xy.and((1L).shl(32) - 1).toInt()
 */

// Actually faster than Long in tle1, as there's no extra boxing / allocation in each iteration.
private typealias FastPair = Pair<Int, Int>

private fun fastPair(
    x: Int,
    y: Int
): FastPair {
    return x to y
}

private fun xOfFastPair(xy: FastPair): Int = xy.first
private fun yOfFastPair(xy: FastPair): Int = xy.second

// O(m*n*n)
private fun tle1(input: Array<CharArray>): Int {
    val rowCount = input.size
    val columnCount = input[0].size
    val maxSquareSize = min(rowCount, columnCount)

    // Set of squares (represented by their top-left corner) with the previous [size]
    var previousSquares = input.asSequence().flatMapIndexedTo(mutableSetOf()) { y, row ->
        row.asSequence().mapIndexedNotNull { x, cell ->
            if (cell == OCCUPIED) {
                fastPair(x, y)
            } else {
                null
            }
        }
    }

    fun canCombineIntoLargerSquare(smallSquare: FastPair): Boolean {
        val x = xOfFastPair(smallSquare)
        val y = yOfFastPair(smallSquare)
        return previousSquares.contains(fastPair(x, y + 1)) &&
            previousSquares.contains(fastPair(x + 1, y)) &&
            previousSquares.contains(fastPair(x + 1, y + 1))
    }

    if (previousSquares.isEmpty()) {
        return 0
    }

    for (size in 2..maxSquareSize) {
        val squares = previousSquares.mapNotNullTo(mutableSetOf()) { position ->
            position.takeIf(::canCombineIntoLargerSquare)
        }
        if (squares.isEmpty()) {
            return (size - 1) * (size - 1)
        }
        previousSquares = squares
    }
    return maxSquareSize * maxSquareSize
}

private fun dp(input: Array<CharArray>): Int {
    val rowCount = input.size
    val columnCount = input[0].size
    var globalMax = 0

    // Maps square's right-bottom point to side length of largest square
    val output = Array(rowCount) {
        IntArray(columnCount)
    }

    for (x in 0 until columnCount) {
        for (y in 0 until rowCount) {
            val selfValue = if (input[y][x] == OCCUPIED) {
                1
            } else {
                0
            }

            val combinedValue = if (selfValue == 0) {
                selfValue
            } else {
                if (x == 0 || y == 0) {
                    // Populate from input
                    selfValue
                } else {
                    // Populate from output
                    val minOfNeighbours = minOf(output[y - 1][x], output[y][x - 1], output[y - 1][x - 1])
                    if (minOfNeighbours == 0) {
                        selfValue
                    } else {
                        minOfNeighbours + 1
                    }
                }
            }
            output[y][x] = combinedValue
            globalMax = maxOf(globalMax, combinedValue)
        }
    }

    return globalMax * globalMax
}