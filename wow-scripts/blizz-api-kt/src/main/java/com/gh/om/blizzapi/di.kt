package com.gh.om.blizzapi

import ShadowlandsGearDropsImpl
import com.fatboyindustrial.gsonjodatime.Converters
import com.gh.om.blizzapi.base.Bapi
import com.gh.om.blizzapi.base.GearDropSimulatorFactory
import com.gh.om.blizzapi.base.GearDropSimulatorHelper
import com.gh.om.blizzapi.base.ShadowlandsGearDrops
import com.gh.om.blizzapi.base.Simc
import com.gh.om.blizzapi.geardrops.EquipmentStateFactoryImpl
import com.gh.om.blizzapi.geardrops.GearDropSimulatorFactoryImpl
import com.gh.om.blizzapi.geardrops.GearDropSimulatorHelperImpl
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
import java.io.File
import java.lang.reflect.Type
import java.util.function.Consumer
import java.util.function.Supplier
import javax.inject.Singleton
import kotlin.random.Random

interface App {
    val simc: Simc.DB
    val bapi: Bapi
    val config: AppConfig
    val itemScaling: Simc.ItemScaling
    val gearDropSimPresets: GearDropSimPresets
}

@Singleton
@Component(modules = [AppModule::class, ConfigModule::class])
interface AppComponent : App {
}

@Module
class ConfigModule(
    private val config: AppConfig,
    private val random: Random,
) {
    @Provides
    fun provideAppConfig() = config

    @Provides
    fun provideRandomSupplier(): Supplier<Random> = Supplier { random }
}

@Module
class AppModule {
    @Provides
    @Singleton
    fun provideSimcReader(): Simc.CxxSourceReader {
        return SimcCxxSourceReaderImpl(File(Util.expanduser("~/ref/simc")))
    }

    @Provides
    @Singleton
    fun provideSimcDB(simcDBImpl: SimcDBImpl): Simc.DB = simcDBImpl

    @Provides
    @Singleton
    fun provideSimcLangReader(impl: SimcLangReaderImpl): Simc.Lang.Reader = impl

    @Provides
    @Singleton
    fun provideShadowlandsGearDrops(): ShadowlandsGearDrops = ShadowlandsGearDropsImpl

    @Provides
    @Singleton
    fun provide(factoryImpl: GearDropSimulatorFactoryImpl): GearDropSimulatorFactory = factoryImpl

    @Provides
    @Singleton
    fun provideSimcItemScaling(itemScalingImpl: ItemScalingImpl): Simc.ItemScaling = itemScalingImpl

    @Provides
    @Singleton
    fun provideEquipmentStateFactory(equipmentStateFactoryImpl: EquipmentStateFactoryImpl): Simc.EquipmentStateFactory =
        equipmentStateFactoryImpl

    @Provides
    @Singleton
    fun provideGearDropSimulatorHelper(impl: GearDropSimulatorHelperImpl): GearDropSimulatorHelper = impl

    @Provides
    @Singleton
    fun provideBapi(bapiImpl: BapiImpl): Bapi = bapiImpl

    @Provides
    @Singleton
    fun provideGsonConfig(): GsonConfig {
        return GsonConfig { builder ->
            Converters.registerAll(builder)
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
    builder.registerTypeAdapter(A::class.java, object : JsonSerializer<A> {
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
