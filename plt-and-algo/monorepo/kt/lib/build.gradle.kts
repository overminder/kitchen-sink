/*
 * This file was generated by the Gradle 'init' task.
 *
 * This generated file contains a sample Kotlin library project to get you started.
 * For more details take a look at the 'Building Java & JVM projects' chapter in the Gradle
 * User Manual available at https://docs.gradle.org/8.0.2/userguide/building_java_projects.html
 */

plugins {
    // Apply the org.jetbrains.kotlin.jvm Plugin to add support for Kotlin.
    alias(libs.plugins.kotlin.jvm)

    // Apply the java-library plugin for API and implementation separation.
    `java-library`
}

repositories {
    // Use Maven Central for resolving dependencies.
    mavenCentral()
}

dependencies {
    implementation(libs.kotlinx.coroutines.core)

    // Use the Kotlin JUnit 5 integration.
    testImplementation(libs.kotlin.junit5)

    // Use the JUnit 5 integration.
    testImplementation("org.junit.jupiter:junit-jupiter-engine:5.9.1")

    // assertThat().isEqualTo()
    testImplementation("org.assertj:assertj-core:3.24.2")

    // Property test (a la QuickCheck)
    testImplementation(libs.kotest.property)
    testImplementation(libs.kotest.core)
    testImplementation(libs.kotest.runner)
}

tasks.withType<Test>().forEach {
    // Use JUnit Platform for unit tests.
    it.useJUnitPlatform()
}
