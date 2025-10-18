plugins {
    id("java")
    kotlin("jvm")
    application
}

group = "com.gh.om.pl.cwai"
version = "1.0-SNAPSHOT"

repositories {
    mavenCentral()
}

dependencies {
    testImplementation(platform("org.junit:junit-bom:5.10.0"))
    testImplementation("org.junit.jupiter:junit-jupiter")
    testImplementation("org.assertj:assertj-core:3.26.0")
    testRuntimeOnly("org.junit.platform:junit-platform-launcher")
    implementation(kotlin("stdlib-jdk8"))
    implementation("net.java.dev.jna:jna:5.14.0")
}

tasks.test {
    useJUnitPlatform()
}
kotlin {
    jvmToolchain(21)
}

application {
    // Kotlin top-level main in file `main.kt` resides in `MainKt`
    mainClass.set("com.gh.om.pl.cwai.MainKt")
}