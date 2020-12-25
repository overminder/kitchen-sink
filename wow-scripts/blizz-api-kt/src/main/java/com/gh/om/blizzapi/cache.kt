package com.gh.om.blizzapi

import java.io.File
import java.sql.DriverManager
import java.util.concurrent.ConcurrentHashMap

interface Cache {
    suspend fun put(key: ByteArray, value: ByteArray?)
    suspend fun get(key: ByteArray): ByteArray?
}

class SqliteCache(private val filename: String) : Cache {
    private val connection = DriverManager.getConnection("jdbc:sqlite:$filename")

    init {
        connection.createStatement().use {
            it.executeUpdate("create table if not exists kvcache (key text primary key, value text)")
        }
    }

    fun deleteFile(): Boolean {
        connection.close()
        val f = File(filename)
        return if (f.isFile) {
            f.delete()
        } else {
            false
        }
    }

    override suspend fun put(key: ByteArray, value: ByteArray?) {
        if (value != null) {
            connection.prepareStatement("insert into kvcache values(?, ?)").use {
                it.setString(1, key.decodeToString())
                it.setString(2, value.decodeToString())
                it.execute()
            }
        } else {
            connection.prepareStatement("delete from kvcache where key = ?").use {
                it.setString(1, key.decodeToString())
                it.execute()
            }
        }
    }

    override suspend fun get(key: ByteArray): ByteArray? {
        return connection.prepareStatement("select value from kvcache where key = ?").use {
            it.setString(1, key.decodeToString())
            val rs = it.executeQuery()
            if (rs.next()) {
                rs.getString(1).toByteArray()
            } else {
                null
            }
        }
    }
}

class InMemoryCache : Cache {
    data class ContentHashed(val byteArray: ByteArray) {
        override fun equals(other: Any?): Boolean {
            if (this === other) return true
            if (javaClass != other?.javaClass) return false

            other as ContentHashed

            if (!byteArray.contentEquals(other.byteArray)) return false

            return true
        }

        override fun hashCode(): Int {
            return byteArray.contentHashCode()
        }
    }

    private val store = ConcurrentHashMap<ContentHashed, ByteArray>()

    override suspend fun put(key: ByteArray, value: ByteArray?) {
        val chKey = ContentHashed(key)
        if (value == null) {
            store.remove(chKey)
        } else {
            store[chKey] = value
        }
    }

    override suspend fun get(key: ByteArray): ByteArray? {
        return store[ContentHashed(key)]
    }
}
