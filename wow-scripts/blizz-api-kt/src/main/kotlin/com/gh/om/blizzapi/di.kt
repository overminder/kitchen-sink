package com.gh.om.blizzapi

import com.google.gson.Gson
import com.google.gson.GsonBuilder
import com.google.gson.JsonDeserializationContext
import com.google.gson.JsonDeserializer
import com.google.gson.JsonElement
import com.google.gson.JsonPrimitive
import com.google.gson.JsonSerializationContext
import com.google.gson.JsonSerializer
import dagger.Component
import dagger.Module
import dagger.Provides
import io.ktor.client.features.json.GsonSerializer
import java.io.File
import java.lang.reflect.Type
import javax.inject.Inject
import javax.inject.Scope
import javax.inject.Singleton

interface App {
    val simc: Simc
    val bapi: Bapi
    val itemScaling: ItemScaling
}

@Singleton
@Component(modules = [AppModule::class])
interface AppComponent : App {
}

@Module
class AppModule {
    @Provides
    @Singleton
    fun provideSimcReader(): SimcSource.Reader {
        return SimcSource.Reader(File(Util.expanduser("~/ref/simc")))
    }

    @Provides
    @Singleton
    fun provideBapi(bapiImpl: BapiImpl): Bapi = bapiImpl

    @Provides
    @Singleton
    fun provideGsonConfig(): GsonConfig {
        return GsonConfig { builder ->
            registerEnumType(builder, Item.Klass.values())
            registerEnumType(builder, Item.Subclass.values())
        }
    }

    @Provides
    @Singleton
    fun provideGson(gsonConfig: GsonConfig): Gson {
        val b = GsonBuilder()
        gsonConfig.configure(b)
        return b.create()
    }

    @Provides
    @Singleton
    fun provideCache(): Cache {
        return SqliteCache("kvcache.db")
    }
}

fun interface GsonConfig {
    fun configure(gsonBuilder: GsonBuilder)
}

private inline fun <reified A : Enum<A>> registerEnumType(builder: GsonBuilder, values: Array<A>) {
    builder.registerTypeAdapter(A::class.java, object: JsonSerializer<A> {
        override fun serialize(src: A, typeOfSrc: Type?, context: JsonSerializationContext?): JsonElement {
            return JsonPrimitive(src.ordinal)
        }
    })

    builder.registerTypeAdapter(A::class.java, object : JsonDeserializer<A> {
        override fun deserialize(
            json: JsonElement?,
            typeOfT: Type?,
            context: JsonDeserializationContext?
        ): A? {
            return json?.asInt?.let(values::get)
        }
    })
}
