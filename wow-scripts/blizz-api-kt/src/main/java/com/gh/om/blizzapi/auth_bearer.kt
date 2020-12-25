package com.gh.om.blizzapi

import io.ktor.client.features.auth.Auth
import io.ktor.client.features.auth.AuthProvider
import io.ktor.client.request.HttpRequestBuilder
import io.ktor.http.HttpHeaders
import io.ktor.http.auth.HttpAuthHeader

fun Auth.bearer(token: String) {
    providers.add(BearerAuthProvider(token))
}

/**
 * Client basic authentication provider.
 */
class BearerAuthProvider(
    private val token: String,
) : AuthProvider {
    override val sendWithoutRequest: Boolean = true
    private val defaultCharset = Charsets.UTF_8

    override fun isApplicable(auth: HttpAuthHeader): Boolean {
        return true
    }

    override suspend fun addRequestHeaders(request: HttpRequestBuilder) {
        request.headers[HttpHeaders.Authorization] = createHeaderValue()
    }

    private fun createHeaderValue(): String {
        return "Bearer $token"
    }
}
