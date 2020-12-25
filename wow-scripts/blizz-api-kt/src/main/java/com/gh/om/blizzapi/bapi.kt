package com.gh.om.blizzapi

import com.gh.om.blizzapi.base.Bapi
import com.gh.om.blizzapi.base.FastBapi
import com.gh.om.blizzapi.base.ShadowlandsGearDrops
import com.gh.om.blizzapi.base.Simc
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
import org.joda.time.DateTime
import org.joda.time.Duration
import javax.inject.Inject

private suspend inline fun <reified A> Cache.tryGetJson(key: String, gson: Gson): A? {
    val bkey = key.toByteArray()
    val bs = get(bkey) ?: return null
    return try {
        gson.fromJson(bs.decodeToString(), A::class.java)
    } catch (e: JsonSyntaxException) {
        put(bkey, null)
        null
    }
}

private suspend inline fun Cache.putJson(key: String, json: String) {
    val bkey = key.toByteArray()
    val bs = json.toByteArray()
    put(bkey, bs)
}

private fun itemCacheKey(id: String) = "item:$id"
private fun tokenCacheKey(id: String) = "token:$id"

class FastBapiImpl @Inject constructor(
    private val bapi: Bapi,
    private val slDrops: ShadowlandsGearDrops,
    private val simc: Simc.DB,
) : FastBapi {
    private val cache = mutableMapOf<Int, Item>()

    override fun getItem(id: Int): Item {
        return requireNotNull(cache[id]) {
            "id $id not in FastBapi (cache.size = ${cache.size})"
        }
    }

    private fun putItem(id: Int, item: Item) {
        cache[id] = item
    }

    override suspend fun init() {
        for (d in slDrops.dungeons + slDrops.raids) {
            for (b in d.bossWithDrops) {
                for (id in b.itemIds) {
                    populateItem(id)
                    simc.tryTradeGearToken(id)?.forEach {
                        populateItem(it)
                    }
                }
            }
        }
    }

    override suspend fun populateItem(id: Int) {
        putItem(id, bapi.getItem(id.toString()))
    }
}

class BapiImpl @Inject constructor(
    private val cache: Cache,
    private val gsonConfig: GsonConfig,
    private val gson: Gson,
    private val appConfig: AppConfig,
) : Bapi {
    override lateinit var token: AccessToken

    private suspend fun getToken(id: String, secret: String): TimedAccessToken {
        cache.tryGetJson<TimedAccessToken>(tokenCacheKey(id), gson)?.let {
            if (it.expiry < DateTime.now()) {
                return it
            }
        }
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
        val token = c.submitForm<AccessToken>(postBody) {
            url("https://us.battle.net/oauth/token")
        }
        return TimedAccessToken(token, DateTime.now() + Duration.standardSeconds(40000))
    }

    override suspend fun configure() {
        token = getToken(appConfig.client.id, appConfig.client.secret).token
    }

    override suspend fun getItem(id: String): Item {
        cache.tryGetJson<Item>(itemCacheKey(id), gson)?.let {
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
        val result = gson.fromJson(json, Item::class.java)
        cache.putJson(itemCacheKey(id), json)
        return result
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
    val expiry: DateTime,
)

private fun AccessToken.installTo(config: HttpClientConfig<*>) {
    val token = value
    config.install(Auth) {
        bearer(token)
    }
}
