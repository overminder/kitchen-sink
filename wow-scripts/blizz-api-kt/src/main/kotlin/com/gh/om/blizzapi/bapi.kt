package com.gh.om.blizzapi

import com.google.gson.Gson
import com.google.gson.JsonSyntaxException
import com.google.gson.annotations.SerializedName
import io.ktor.client.HttpClient
import io.ktor.client.HttpClientConfig
import io.ktor.client.engine.cio.CIO
import io.ktor.client.features.auth.Auth
import io.ktor.client.features.auth.providers.basic
import io.ktor.client.features.json.GsonSerializer
import io.ktor.client.features.json.JsonFeature
import io.ktor.client.features.logging.DEFAULT
import io.ktor.client.features.logging.LogLevel
import io.ktor.client.features.logging.Logger
import io.ktor.client.features.logging.Logging
import io.ktor.client.request.forms.submitForm
import io.ktor.client.request.get
import io.ktor.client.request.url
import io.ktor.http.parametersOf
import javax.inject.Inject

interface Bapi {
    suspend fun configure(id: String, secret: String)
    suspend fun getItem(id: String): Item
    val token: AccessToken
}

class BapiImpl @Inject constructor(
    private val cache: Cache,
    private val gsonConfig: GsonConfig,
    private val gson: Gson,
) : Bapi {
    override lateinit var token: AccessToken

    override suspend fun configure(id: String, secret: String) {
        val c = HttpClient(CIO) {
            configureHttpClient(this)
            install(Auth) {
                basic {
                    sendWithoutRequest = true
                    username = id
                    password = secret
                }
            }
        }
        val postBody = parametersOf("grant_type", "client_credentials")
        token = c.submitForm(postBody) {
            url("https://us.battle.net/oauth/token")
        }
    }

    override suspend fun getItem(id: String): Item {
        tryGetCachedItem(id)?.let {
            return it
        }

        // Ref: https://github.com/chalverson/wowjavaapi/blob/master/src/org/halverson/wowapi/dao/CharacterDao.java
        // for how to access blizz api.
        val base = "https://us.api.blizzard.com"
        val endpoint = "/data/wow/item/$id?namespace=static-us&locale=en_US"
        val c = HttpClient(CIO) {
            configureHttpClient(this)
            token.installTo(this)
        }
        val json = c.get<String>("$base$endpoint")
        putCachedItem(id, json)
        return gson.fromJson(json, Item::class.java)
    }

    private suspend fun tryGetCachedItem(id: String): Item? {
        val key = "item:$id".toByteArray()
        val bs = cache.get(key) ?: return null
        return try {
            gson.fromJson(bs.decodeToString(), Item::class.java)
        } catch (e: JsonSyntaxException) {
            cache.put(key, null)
            null
        }
    }

    private suspend fun putCachedItem(id: String, json: String) {
        val key = "item:${id}".toByteArray()
        val bs = json.toByteArray()
        cache.put(key, bs)
    }

    private fun configureHttpClient(config: HttpClientConfig<*>) {
        with(config) {
            if (LOGGING) {
                install(Logging) {
                    logger = Logger.DEFAULT
                    level = LogLevel.HEADERS
                }
            }
            install(JsonFeature) {
                serializer = GsonSerializer(gsonConfig::configure)
            }
        }
    }
}

private const val LOGGING = false

data class AccessToken(@SerializedName("access_token") val value: String)

data class TimedAccessToken(
    val token: AccessToken,
    val expiryDate: Long,
)

private fun AccessToken.installTo(config: HttpClientConfig<*>) {
    val token = value
    config.install(Auth) {
        bearer(token)
    }
}
