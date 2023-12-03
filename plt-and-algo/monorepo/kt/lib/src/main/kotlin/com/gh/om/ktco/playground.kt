@file:OptIn(ExperimentalCoroutinesApi::class, DelicateCoroutinesApi::class)

package com.gh.om.ktco

import java.io.Closeable
import java.lang.RuntimeException
import kotlin.coroutines.EmptyCoroutineContext
import kotlin.coroutines.suspendCoroutine
import kotlinx.coroutines.CancellationException
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.DelicateCoroutinesApi
import kotlinx.coroutines.Dispatchers
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.async
import kotlinx.coroutines.awaitAll
import kotlinx.coroutines.cancel
import kotlinx.coroutines.cancelAndJoin
import kotlinx.coroutines.channels.Channel
import kotlinx.coroutines.channels.awaitClose
import kotlinx.coroutines.coroutineScope
import kotlinx.coroutines.currentCoroutineContext
import kotlinx.coroutines.delay
import kotlinx.coroutines.flow.Flow
import kotlinx.coroutines.flow.SharingStarted
import kotlinx.coroutines.flow.callbackFlow
import kotlinx.coroutines.flow.cancel
import kotlinx.coroutines.flow.channelFlow
import kotlinx.coroutines.flow.collect
import kotlinx.coroutines.flow.collectLatest
import kotlinx.coroutines.flow.coroutineContext
import kotlinx.coroutines.flow.flow
import kotlinx.coroutines.flow.flowOn
import kotlinx.coroutines.flow.map
import kotlinx.coroutines.flow.onEach
import kotlinx.coroutines.flow.shareIn
import kotlinx.coroutines.flow.stateIn
import kotlinx.coroutines.flow.takeWhile
import kotlinx.coroutines.joinAll
import kotlinx.coroutines.launch
import kotlinx.coroutines.newFixedThreadPoolContext
import kotlinx.coroutines.newSingleThreadContext
import kotlinx.coroutines.runBlocking
import kotlinx.coroutines.supervisorScope
import kotlinx.coroutines.sync.Semaphore
import kotlinx.coroutines.withContext
import kotlinx.coroutines.yield
import org.jetbrains.annotations.Async

fun printMyThread(what: String = "Running") {
    println("$what in ${Thread.currentThread().name}")
}

/**
 * Coroutine hello world.
 */
fun launchAndRun() {
    val job = CoroutineScope(EmptyCoroutineContext).launch {
        printMyThread("delay")
        delay(1000L) // non-blocking delay for 1 second (default time unit is ms)
        println("World!") // print after delay
    }
    runBlocking {
        println("Hello!")
        job.join()
    }
}

/**
 * [channelFlow]: Unidirectional pipes
 */
fun flow1() {
    fun waitAndProduce() = channelFlow {
        printMyThread("start produce")
        delay(1000)
        // Send transfers control to the collectors.
        // Same as yield / await in https://hackage.haskell.org/package/pipes
        send(1)
        delay(1000)
        send(2)
        delay(1000)
        printMyThread("after produce last")
        // Produced in the current context, unless overridden (e.g. flowOn)
    }.flowOn(Dispatchers.Default)
    runBlocking {
        waitAndProduce().collect {
            // Consumed in the current context
            printMyThread("collect $it")
        }
    }
}

/**
 * Properly terminate a sharedFlow
 */
fun flow2() {
    val producerPool = newFixedThreadPoolContext(2, "Producer")
    val consumerPool = newFixedThreadPoolContext(2, "Consumer")
    fun waitAndProduce(): Flow<Int> = channelFlow {
        printMyThread("start produce")
        delay(1000)
        // Send transfers control to the collectors.
        // Same as yield / await in https://hackage.haskell.org/package/pipes
        send(1)
        delay(1000)
        send(2)
        delay(1000)
        printMyThread("after produce last")
        // Produced in the current context, unless overridden (e.g. flowOn)
    }.flowOn(producerPool)

    fun <A> Flow<A>.attachTerminal(): Flow<Result<A>> = channelFlow {
        collect {
            printMyThread("attachTerminal: re-yield $it")
            send(Result.success(it))
        }
        printMyThread("attachTerminal: done")
        send(Result.failure(RuntimeException("Done")))
    }

    fun <A> Flow<A>.shareAndTerminate(scope: CoroutineScope): Flow<A> = attachTerminal()
        .shareIn(scope, started = SharingStarted.Lazily, replay = 1)
        .takeWhile { it.isSuccess }
        .map { it.getOrThrow() }

    runBlocking(consumerPool) {
        // Without sharing, the same flow will be executed twice
        // Shared flow won't propagate termination, so we'll have to terminate it by ourselves.
        val flow = waitAndProduce().shareAndTerminate(this)

        val a = launch {
            flow.collect {
                // Consumed in the current context
                printMyThread("A.collect $it")
            }
        }
        val b = launch {
            flow.collect {
                // Consumed in the current context
                printMyThread("B.collect $it")
            }
        }
        joinAll(a, b)
    }

    listOf(producerPool, consumerPool).forEach(Closeable::close)
}

/**
 * [Channel] can actually be used as bidirectional pipes
 */
fun channel1() {
    val pipe = Channel<Int>()
    runBlocking {
        val a = launch {
            delay(500)
            printMyThread("A send 1")
            delay(500)
            pipe.send(1)
            delay(500)
            printMyThread("A received ${pipe.receive()}")
            delay(500)
        }
        val b = launch {
            delay(500)
            printMyThread("B received ${pipe.receive()}")
            delay(500)
            printMyThread("B send 2")
            delay(500)
            pipe.send(2)
            delay(500)
        }
        joinAll(a, b)
    }
}

/**
 * Parent scope's cancellation is propagated to child scope
 */
fun structured1(throwInsteadOfCancel: Boolean = false) {
    val parentContext = newSingleThreadContext("parent")
    val childContext = newSingleThreadContext("child")
    runBlocking {
        launch(parentContext) {
            printMyThread("Running in parentContext")
            val childJob = launch(childContext) {
                printMyThread("Running in childContext")
                delay(1000)
                printMyThread("childJob done")
                cancel()
            }
            delay(500)
            if (throwInsteadOfCancel) {
                throw RuntimeException()
            } else {
                // Canceling the parent job will also cancel the child job.
                cancel()
            }
            // Though non-suspend functions can continue to run (lol)
            printMyThread("parentJob done")
            childJob.join()
        }
        delay(2000)
    }
}

/**
 * Hmm I thought cancelling one job in [coroutineScope] will cancel all jobs.
 * Isn't that the case?
 */
fun structured2() {
    runBlocking {
        val result = coroutineScope {
            val first = async {
                delay(500)
                printMyThread("Computed first")
                1
            }
            val second = async {
                delay(100)
                cancel()
                2
            }
            first.join()
            second.join()
            first to second
        }
        println(result)
    }
}

/**
 * Illustrate that job.cancel is just throwing cancellation exception
 * to each cancel-aware suspension point. Once a Job is canceled, it
 * can still run non-suspend functions, but cancel-aware suspend functions
 * will immediately rethrow CancellationException.
 */
fun structured3() = runBlocking {
    val job = launch {
        try {
            delay(2000)
        } catch (e: CancellationException) {
            printMyThread("Caught CE")
        }
        try {
            yield()
        } catch (e: CancellationException) {
            printMyThread("CE is still there")
        }
        yield()
        printMyThread("Never executed")
    }
    delay(500)
    job.cancelAndJoin()
}

/**
 * Illustrate that calling scope.cancel itself doesn't throw CE. However it
 * still marks the Job as cancelled, so subsequent cancel-aware suspension points
 * will not run any more.
 */
fun structured4() = runBlocking {
    val job = launch {
        try {
            delay(2000)
            cancel()
            printMyThread("I've canceled myself")
        } catch (e: CancellationException) {
            printMyThread("Not actually caught")
        }
        try {
            yield()
        } catch (e: CancellationException) {
            printMyThread("CE is still there")
        }
        yield()
        printMyThread("Not executed")
    }
    job.join()
}

/**
 * Demonstrate the correct way to use callbackFlow
 */
fun callbackFlow1() {
    newFixedThreadPoolContext(2, "Producer").use { producerPool ->
        runBlocking {
            val flow = callbackFlow {
                var i = 0
                // Need to launch a new job for blocking tasks
                launch {
                    while (true) {
                        delay(50)
                        send(i)
                        printMyThread("callbackFlow: Produced $i")
                        i += 1
                    }
                }
                // This needs to happen last, because anything after will NOT be run (job is closed)
                awaitClose {
                    printMyThread("callbackFlow: Closed at $i")
                }
            }.flowOn(producerPool)
            val job = launch(Dispatchers.IO) {
                flow.onEach {
                    printMyThread("Received $it")
                }.collect()
            }
            delay(500)
            job.cancel()
        }
    }
}

fun main() {
    runBlocking {
        delay(500)
        printMyThread()
    }
}
