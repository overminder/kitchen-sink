plugins {
    kotlin("jvm")
    id("com.google.devtools.ksp")
    application
}

group = "org.example"
version = "1.0-SNAPSHOT"

repositories {
    mavenCentral()
    maven("https://maven.pkg.jetbrains.space/public/p/compose/dev")
    google()
}

dependencies {
    implementation(project(":macro-core"))
    implementation(project(":macro-overlay"))

    // Platform
    implementation("com.github.kwhat:jnativehook:2.2.2")
    implementation("net.java.dev.jna:jna-platform:5.14.0")
    implementation("org.jetbrains.kotlinx:kotlinx-coroutines-core:1.9.0-RC.2")

    // Dagger DI
    implementation("com.google.dagger:dagger:2.51.1")
    ksp("com.google.dagger:dagger-compiler:2.51.1")
}

application {
    mainClass.set("macroapp.MainKt")
}
