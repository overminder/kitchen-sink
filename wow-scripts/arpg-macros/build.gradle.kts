plugins {
    kotlin("jvm") version "2.0.10"
}

group = "org.example"
version = "1.0-SNAPSHOT"

repositories {
    mavenCentral()
}

dependencies {
    testImplementation(kotlin("test"))
    testImplementation("org.junit.jupiter:junit-jupiter:5.8.1")
    // https://mvnrepository.com/artifact/org.assertj/assertj-core
    testImplementation("org.assertj:assertj-core:3.26.3")

    implementation("com.github.kwhat:jnativehook:2.2.2")

    // https://mvnrepository.com/artifact/org.jetbrains.kotlinx/kotlinx-coroutines-core-jvm
    implementation("org.jetbrains.kotlinx:kotlinx-coroutines-core:1.9.0-RC.2")

    // https://mvnrepository.com/artifact/net.java.dev.jna/jna
    implementation("net.java.dev.jna:jna-platform:5.14.0")

    // mac JNA stuff
    implementation("com.github.oshi:oshi-core:6.6.5")

    // OCR
    implementation("net.sourceforge.tess4j:tess4j:5.16.0")
}

tasks.test {
    useJUnitPlatform()
}
