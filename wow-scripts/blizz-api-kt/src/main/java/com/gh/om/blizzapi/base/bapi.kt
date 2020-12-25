package com.gh.om.blizzapi.base

import com.gh.om.blizzapi.AccessToken
import com.gh.om.blizzapi.Item

interface Bapi {
    suspend fun configure()
    suspend fun getItem(id: String): Item
    val token: AccessToken
}

interface FastBapi {
    fun getItem(id: Int): Item

    suspend fun init()
    suspend fun populateItem(id: Int)
}
