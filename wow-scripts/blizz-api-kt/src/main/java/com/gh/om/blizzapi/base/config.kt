package com.gh.om.blizzapi

data class AppConfig(
    val client: Client,
    val profile: Profile,
) {
    data class Client(
        val id: String,
        val secret: String,
    )
    data class Profile(
        val gears: String,
    )
}
