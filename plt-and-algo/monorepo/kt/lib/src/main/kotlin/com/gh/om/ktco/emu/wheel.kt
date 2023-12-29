package com.gh.om.ktco.emu

import com.gh.om.ktco.emu.CoPrelude.bind
import com.gh.om.ktco.emu.Interp.runBlocking
import java.util.concurrent.CompletableFuture
import java.util.concurrent.Executor
import java.util.concurrent.Executors
import java.util.concurrent.ScheduledExecutorService
import java.util.concurrent.ThreadFactory
import java.util.concurrent.TimeUnit
import kotlinx.coroutines.CancellationException

// Reinvent the wheel: Do Kt coroutine with Monad

// Cancellation propagation is configurable and bidirectional (child to parent, parent to another child)
// This needs an IORef read at every bind to check for previous exception status.
// Other exception can probably be done in the same way?

// Tree structure is immutable and can be done with just a reader monad.

// Dispatching and flowOn: Probably easier to separate the interpreter and the data.

class IORef<A>(var value: A)

sealed class CoDispatcher {
    data object Unconfined : CoDispatcher()
    class Confined(
        val name: String,
        val e: Executor
    ) : CoDispatcher() {
        override fun toString() = "Confined($name)"
    }
}

fun mkDispatcher(name: String): CoDispatcher.Confined {
    val tf = ThreadFactory {
        val t = Thread(it, "CoM.$name")
        t.isDaemon = true
        t
    }
    return CoDispatcher.Confined(name, Executors.newSingleThreadScheduledExecutor(tf))
}

@Suppress("PrivatePropertyName")
private val DefaultScheduler by lazy {
    mkDispatcher("Sched").e as ScheduledExecutorService
}

@Suppress("PrivatePropertyName")
private val DefaultDispatcher by lazy {
    mkDispatcher("Default")
}

@Suppress("PrivatePropertyName")
private val AlternativeDispatcher by lazy {
    mkDispatcher("Alt")
}

object CoCancelled : CancellationException() {
    override fun toString(): String {
        return "CoCancelled"
    }

    override fun fillInStackTrace(): Throwable {
        // Do not fill
        return this
    }
}

class CoJob(
    val exceptionRef: IORef<CancellationException?> = IORef(null),
    val onCancel: ((CancellationException) -> Boolean) = { /* handled? */ false },
    // If exists: propagate up
    val parent: CoJob? = null,
)

data class CoCtx(
    val dispatcher: CoDispatcher = CoDispatcher.Unconfined,
    val name: String? = null,
    val job: CoJob? = CoJob(),
)

class CoLaunched<A>(
    // XXX need a single source of truth for cancellation
    val f: CompletableFuture<A>,
    val job: CoJob?,
)

sealed class CoroutineM<out A> {
    data class Pure<A>(val value: A) : CoroutineM<A>()

    data class Bind<A, B>(
        val ma: CoroutineM<A>,
        val f: (A) -> CoroutineM<B>,
    ) : CoroutineM<B>()

    data object CancelSelf : CoroutineM<Unit>()
    data class Cancel(val launched: CoLaunched<*>) : CoroutineM<Unit>()

    data class Launch<A>(
        val propagateCancel: Boolean = true,
        val updateContext: ((CoCtx) -> CoCtx)? = null,
        val task: () -> CoroutineM<A>,
    ) : CoroutineM<CoLaunched<A>>()

    // Reader monad
    data object GetContext : CoroutineM<CoCtx>()

    data class Join<A>(
        val launched: CoLaunched<A>,
    ) : CoroutineM<Result<A>>()

    // TODO: Need to support immediate cancellation
    data class Delay(
        val callcc: (scheduler: ScheduledExecutorService, k: (Unit) -> Unit) -> Unit
    ) : CoroutineM<Unit>()
}

private typealias Cont<A> = (A) -> Unit

object Interp {
    fun <A> CoroutineM<A>.runBlocking(ctx: CoCtx = CoCtx()): A {
        val future = CompletableFuture<Result<A>>()
        val wrappedCo = CoroutineM.Launch { this }.bind {
            CoroutineM.Join(it)
        }
        dispatch(ctx) {
            runCont(wrappedCo, ctx) { value ->
                future.complete(value)
            }
        }
        return future.get().getOrThrow()
    }

    /**
     * Invariant: This should be run in [ctx]'s dispatcher.
     */
    private fun <A> runCont(
        co: CoroutineM<A>,
        ctx: CoCtx,
        k: Cont<A>
    ) {
        if (transitivelyCancelled(ctx.job)) {
            return
        }
        // printMyThread("runCont ${co.javaClass.simpleName} in ${ctx.dispatcher}")
        return when (co) {
            is CoroutineM.Bind<*, *> -> {
                // k must be (CoCtx, B) -> Unit
                @Suppress("UNCHECKED_CAST")
                runBind(co, ctx, k as Cont<Any?>)
            }

            CoroutineM.CancelSelf -> {
                cancelJobs(ctx.job)
            }

            is CoroutineM.Launch<*> -> {
                @Suppress("UNCHECKED_CAST")
                handleLaunch(co as CoroutineM.Launch<A>, ctx, k as Cont<CoLaunched<A>>)
            }

            is CoroutineM.Pure -> k(co.value)

            is CoroutineM.Join<*> -> {
                // Ugh this is ugly
                @Suppress("UNCHECKED_CAST")
                handleJoin(co as CoroutineM.Join<A>, ctx, k as Cont<Result<A>>)
            }

            is CoroutineM.Delay -> {
                co.callcc(DefaultScheduler) {
                    // Right now the delay is not interrupted
                    dispatch(ctx) {
                        // A must be Unit
                        @Suppress("UNCHECKED_CAST")
                        k(Unit as A)
                    }
                }
            }

            CoroutineM.GetContext -> {
                // A must be CoCtx
                @Suppress("UNCHECKED_CAST")
                k(ctx as A)
            }

            is CoroutineM.Cancel -> {
                // XXX race condition?
                co.launched.f.completeExceptionally(CoCancelled)
                cancelJobs(co.launched.job)
                // A must be Unit
                @Suppress("UNCHECKED_CAST")
                k(Unit as A)
            }
        }
    }

    private fun transitivelyCancelled(job: CoJob?): Boolean {
        for (p in generateSequence(job) { it.parent }) {
            val canceled = p.exceptionRef.value
            if (canceled != null) {
                // Don't proceed. (Join should still return)
                return true
            }
        }
        return false
    }

    private fun cancelJobs(job: CoJob?) {
        for (p in generateSequence(job) { it.parent }) {
            if (p.onCancel(CoCancelled)) {
                break
            }
        }
    }

    private fun <A> handleLaunch(
        co: CoroutineM.Launch<A>,
        ctx: CoCtx,
        k: Cont<CoLaunched<A>>
    ) {
        val future = CompletableFuture<A>()
        val ceRef = IORef<CancellationException?>(null)
        val childJob = CoJob(exceptionRef = ceRef, parent = ctx.job, onCancel = {
            ceRef.value = it
            future.completeExceptionally(it)
            val handled = !co.propagateCancel
            handled
        })
        val childCtx0 = CoCtx(job = childJob, dispatcher = ctx.dispatcher, name = ctx.name)
        val childCtx = co.updateContext?.invoke(childCtx0) ?: childCtx0
        val result = CoLaunched(future, childCtx.job)
        dispatch(childCtx) {
            runCont(co.task(), childCtx) { value ->
                future.complete(value)
            }
        }
        // A must be CoLaunched
        k(result)
    }

    private fun <A> handleJoin(
        co: CoroutineM.Join<A>,
        ctx: CoCtx,
        k: Cont<Result<A>>
    ) {
        co.launched.f.handleAsync(
            { value, exception ->
                if (exception != null) {
                    k(Result.failure(exception))
                } else {
                    k(Result.success(value))
                }
            }, ctx.dispatcher.toExecutor()
        )
    }

    private fun dispatch(
        ctx: CoCtx,
        thunk: () -> Unit
    ) {
        ctx.dispatcher.toExecutor().execute(thunk)
    }

    private fun CoDispatcher.toExecutor(): Executor {
        return when (this) {
            is CoDispatcher.Confined ->
                e

            CoDispatcher.Unconfined ->
                Executor(Runnable::run)
        }
    }

    private fun <A, B> runBind(
        co: CoroutineM.Bind<A, B>,
        ctx: CoCtx,
        k: Cont<B>
    ) {
        runCont(co.ma, ctx) { a ->
            // Might be able to save one dispatch if the dispatcher doesn't change (stack overflow though)
            dispatch(ctx) {
                runCont(co.f(a), ctx, k)
            }
        }
    }
}

object CoPrelude {
    fun delay(ms: Long): CoroutineM<Unit> {
        return CoroutineM.Delay { executor, function ->
            executor.schedule({ function(Unit) }, ms, TimeUnit.MILLISECONDS)
        }
    }

    fun <A> pure(value: A): CoroutineM<A> = CoroutineM.Pure(value)
    inline fun <reified A> launch(
        noinline updateContext: ((CoCtx) -> CoCtx)? = null,
        noinline task: () -> CoroutineM<A>
    ): CoroutineM<CoLaunched<A>> {
        val resultIsUnit = A::class == Unit::class
        return CoroutineM.Launch(propagateCancel = !resultIsUnit, updateContext, task)
    }

    fun <A> join(launched: CoLaunched<A>): CoroutineM<Result<A>> =
        CoroutineM.Join(launched)

    fun <A, B> CoroutineM<A>.bind(f: (A) -> CoroutineM<B>): CoroutineM<B> = CoroutineM.Bind(this, f)
    fun getContext(): CoroutineM<CoCtx> = CoroutineM.GetContext
    inline fun <reified A> withContext(
        noinline f: (CoCtx) -> CoCtx,
        noinline inner: () -> CoroutineM<A>
    ): CoroutineM<A> = launch(f, inner).bind {
        join(it).bind { r ->
            // XXX Now quite right?
            pure(r.getOrThrow())
        }
    }

    fun cancel(): CoroutineM<Unit> = CoroutineM.CancelSelf
    fun cancel(launched: CoLaunched<*>): CoroutineM<Unit> = CoroutineM.Cancel(launched)
    fun joinAll(vararg launcheds: CoLaunched<*>): CoroutineM<Unit> {
        return launcheds.fold(pure(Unit)) { accu, launched ->
            join(launched).bind { accu }
        }
    }

    fun printCtxName(extra: String = "") = getContext().bind {
        val tName = Thread.currentThread().name
        println("[t = $tName, ctx = ${it.name}] $extra")
        pure(Unit)
    }

    fun modifyCtx(
        name: String? = null,
        dispatcher: CoDispatcher? = null
    ): (CoCtx) -> CoCtx = {
        it.copy(name = name ?: it.name, dispatcher = dispatcher ?: it.dispatcher)
    }
}

fun delayAndPrint() {
    CoPrelude.delay(500).bind {
        CoPrelude.printCtxName("Test")
    }.runBlocking()
}

fun launchAndCancelWithinChild() {
    CoPrelude.launch(CoPrelude.modifyCtx(name = "First")) {
        CoPrelude.delay(500).bind {
            CoPrelude.printCtxName("500ms")
        }.bind {
            CoPrelude.cancel()
        }.bind {
            CoPrelude.printCtxName("After cancel")
        }
    }.bind { firstJob ->
        CoPrelude.launch(CoPrelude.modifyCtx(name = "Second", dispatcher = AlternativeDispatcher)) {
            CoPrelude.delay(1000).bind {
                CoPrelude.printCtxName("1000ms")
            }
        }.bind { secondJob ->
            CoPrelude.joinAll(firstJob, secondJob)
        }
    }.runBlocking(CoCtx(DefaultDispatcher))
}

fun launchAndCancelChildFromParent() {
    CoPrelude.launch(CoPrelude.modifyCtx(name = "First")) {
        CoPrelude.delay(500).bind {
            CoPrelude.printCtxName("500ms")
        }.bind {
            CoPrelude.delay(1000)
        }.bind {
            CoPrelude.printCtxName("1500ms -- should not reach here")
        }
    }.bind { firstJob ->
        CoPrelude.launch(CoPrelude.modifyCtx(name = "Second", dispatcher = AlternativeDispatcher)) {
            CoPrelude.delay(1000).bind {
                CoPrelude.printCtxName("1000ms")
            }
        }.bind { secondJob ->
            CoPrelude.cancel(firstJob).bind {
                CoPrelude.joinAll(firstJob, secondJob)
            }
        }
    }.runBlocking(CoCtx(DefaultDispatcher))
}

fun launchAndJoin() {
    CoPrelude.launch(CoPrelude.modifyCtx(name = "First")) {
        CoPrelude.delay(1000).bind {
            CoPrelude.pure("Ok")
        }
    }.bind { job ->
        CoPrelude.printCtxName("Start").bind {
            CoPrelude.join(job).bind { value ->
                CoPrelude.printCtxName("value = $value")
            }
        }
    }.runBlocking()
}

fun launchAndJoinCancelled() {
    CoPrelude.launch(CoPrelude.modifyCtx(name = "First")) {
        CoPrelude.delay(1000).bind {
            CoPrelude.cancel().bind {
                CoPrelude.pure("Should not be executed")
            }
        }
    }.bind { job ->
        CoPrelude.printCtxName("Start").bind {
            CoPrelude.join(job).bind { value ->
                CoPrelude.printCtxName("value = $value")
            }
        }
    }.runBlocking()
}

fun launchAndCancelParent() {
    CoPrelude.launch(CoPrelude.modifyCtx(name = "First")) {
        CoPrelude.delay(500).bind {
            CoPrelude.printCtxName("500ms")
        }.bind {
            CoPrelude.delay(1000)
        }.bind {
            CoPrelude.printCtxName("1500ms -- should not reach here")
        }
    }.bind { firstJob ->
        CoPrelude.launch(CoPrelude.modifyCtx(name = "Second", dispatcher = AlternativeDispatcher)) {
            CoPrelude.delay(1000).bind {
                CoPrelude.printCtxName("1000ms")
            }
        }.bind { secondJob ->
            CoPrelude.delay(1200).bind {
                CoPrelude.cancel().bind {
                    CoPrelude.joinAll(firstJob, secondJob)
                }
            }
        }
    }.runBlocking(CoCtx(DefaultDispatcher))
}

fun main() {
    // delayAndPrint()
    launchAndCancelChildFromParent()
    // launchAndJoin()
    // launchAndJoinCancelled()
    // launchAndCancelParent()

    /*
    */
}
