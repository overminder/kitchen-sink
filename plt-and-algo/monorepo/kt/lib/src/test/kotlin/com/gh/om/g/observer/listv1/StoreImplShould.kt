package com.gh.om.g.observer.listv1

import com.gh.om.g.observer.frp.Behavior
import com.gh.om.g.observer.frp.MutableBehavior
import kotlin.test.Test
import org.assertj.core.api.Assertions.assertThat

private typealias INode = Node<Int, Any>
private typealias IStore = StoreImpl<Int, Any>

class StoreImplShould {
    private val target = IStore()
    @Test
    fun work() {
        assertThat(1).isEqualTo(1)
    }

    @Test
    fun `watch unchanged id-less node`() {
        val (b, close) = watch(nodeOf("foo"))
        assertThat(b.value.value).isEqualTo("foo")
        assertThat(target.watchers).hasSize(1)
        assertThat(target.watchers.first().contains).isEmpty()
        close.close()
        assertThat(target.watchers).hasSize(0)
    }

    @Test
    fun `watch unchanged id-ful node`() {
        val (b, close) = watch(nodeOf("foo", id = 0))
        assertThat(b.value.value).isEqualTo("foo")
        assertThat(target.watchers).hasSize(1)
        assertThat(target.watchers.first().contains).hasSameElementsAs(listOf(0))
        close.close()
        assertThat(target.watchers).hasSize(0)
    }

    @Test
    fun `watch and change`() {
        val (b, close) = watch(nodeOf("v0", id = 0))
        target.writeAndNotify(nodeOf("v1", id = 0))
        assertThat(b.value.value).isEqualTo("v1")
        close.close()
        target.writeAndNotify(nodeOf("v2", id = 0))
        // Shouldn't change again since it's no longer watching.
        assertThat(b.value.value).isEqualTo("v1")
    }

    @Test
    fun `skip change if eq`() {
        val (b, close) = watch(nodeOf("v0", id = 0))
        var callCount = 0
        val stopObservation = b.observe {
            assert(callCount == 0) {
                "Should not be called again"
            }
            callCount += 1
        }
        target.writeAndNotify(nodeOf("v0", id = 0))
        stopObservation.close()
    }

    @Test
    fun `watch and change child`() {
        val node = nodeOf("root", next = TriState.HasValue(nodeOf("v0", id = 0)))
        val (b, close) = watch(node)
        target.writeAndNotify(nodeOf("v1", id = 0))
        assertThat(b.value.next.valueOrNull?.value).isEqualTo("v1")
        target.writeAndNotify(node)
        assertThat(b.value.next.valueOrNull?.value).isEqualTo("v0")
    }

    @Test
    fun `merge cycles to fixed point (almost)`() {
        val node0 = nodeOf("n0-v1", id = 0, next = TriState.NotPresent)
        val node1 = nodeOf("n1", id = 1, next = TriState.HasValue(node0))
        val root = nodeOf("n0-v0", id = 0, next = TriState.HasValue(node1))
        val (b, close) = watch(root)
        // Note that this is incorrect, as node0 is ignored.
        assertThat(b.value.value).isEqualTo("n0-v0")
        assertThat(b.value.next.valueOrNull?.value).isEqualTo("n1")
        target.writeAndNotify(nodeOf("n1-v2", id = 1, next = TriState.NotPresent))
        assertThat(b.value.next.valueOrNull?.value).isEqualTo("n1-v2")
        target.writeAndNotify(nodeOf("n0-v2", id = 0, next = TriState.NotPresent))
        assertThat(b.value.value).isEqualTo("n0-v2")
    }

    private fun watch(node: INode): Pair<Behavior<INode>, AutoCloseable> {
        val mb = MutableBehavior(node)
        return mb to target.watch(mb)
    }

    private fun nodeOf(value: Any, id: Int? = null, next: TriState<INode> = TriState.IsNull): INode {
        return object: INode {
            override val id: Int? = id
            override val next: TriState<INode> = next
            override val value: Any = value
            override fun equals(other: Any?): Boolean {
                if (other !is Node<*, *>) return false
                return stackSafeEq(other)
            }
        }
    }
}
