package com.gh.om.shuati.game_of_life

// Test code

private val SAMPLE_1: Board = arrayOf(
    intArrayOf(0, 1, 0),
    intArrayOf(0, 0, 1),
    intArrayOf(1, 1, 1),
    intArrayOf(0, 0, 0),
)

fun main() {
    nextStateInplace(SAMPLE_1)
    println(SAMPLE_1.prettyPrint())
}

// Impl code

// 0 is empty while 1 is occupied
typealias Row = IntArray
typealias Board = Array<Row>

private const val LIVE = 1
private const val DEAD = 0

fun Board.prettyPrint(): String {
    return joinToString("\n") { row ->
        row.joinToString()
    }
}

fun nextStateCopy(board: Board): Board {
    val rowCount = board.size
    val columnCount = board[0].size
    return Array(rowCount) { y ->
        IntArray(columnCount) { x ->
            val cell = board[y][x]
            val liveNeighbourCount = getLiveNeighbourCount(board = board, x = x, y = y)
            nextStateOfCell(cell = cell, liveNeighbourCount = liveNeighbourCount)
        }
    }
}

fun nextStateInplace(board: Board) {
    val rowCount = board.size
    val columnCount = board[0].size
    fun iterateBoard(f: (x: Int, y: Int) -> Unit) {
        for (y in 0 until rowCount) {
            for (x in 0 until columnCount) {
                f(x, y)
            }
        }
    }
    // 2 passes:
    // 1. populate the new cells using a separate bit
    // 2. move the bits back
    iterateBoard { x, y ->
        val cell = board[y][x]
        val liveNeighbourCount = getLiveNeighbourCount(board = board, x = x, y = y)
        board[y][x] = nextStateOfCell(cell = cell, liveNeighbourCount = liveNeighbourCount).shl(1) or cell
    }

    iterateBoard { x, y ->
        val cell = board[y][x]
        board[y][x] = cell.shr(1)
    }
}

private fun nextStateOfCell(cell: Int, liveNeighbourCount: Int): Int {
    return when {
        isLive(cell) && liveNeighbourCount < 2 -> DEAD
        isLive(cell) && (liveNeighbourCount == 2 || liveNeighbourCount == 3) -> LIVE
        isLive(cell) && liveNeighbourCount > 3 -> DEAD
        !isLive(cell) && liveNeighbourCount == 3 -> LIVE
        else -> cell
    }
}

private fun isLive(cell: Int): Boolean {
    return cell and LIVE == LIVE
}

private val NEIGHBOUR = intArrayOf(-1, 0, 1)
private fun getLiveNeighbourCount(board: Board, x: Int, y: Int): Int {
    var sum = 0
    for (dx in NEIGHBOUR) {
        for (dy in NEIGHBOUR) {
            if (dx == 0 && dy == 0) {
                continue
            }
            val row = board.getOrNull(y + dy) ?: continue
            val cell = row.getOrNull(x + dx) ?: continue
            sum += if (isLive(cell)) {
                1
            } else {
                0
            }
        }
    }
    return sum
}
