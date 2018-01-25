// import com.github.jengelman.gradle.plugins.shadow.tasks.ShadowJar

group = "net.littleredcomputer"
version = "1.0-SNAPSHOT"

plugins {
    java
    application
    // id("com.github.johnrengelman.plugin-shadow") version "2.0.2"
}

application {
    mainClassName = "net.littleredcomputer.dlx.Main"
}

repositories {
    mavenCentral()
}

dependencies {
    testCompile("junit", "junit", "4.12")
    compile("com.google.guava", "guava", "23.5-jre")
    compile("org.apache.logging.log4j", "log4j-api", "2.10.0")
    compile("org.apache.logging.log4j", "log4j-core", "2.10.0")
    compile("commons-cli", "commons-cli", "1.4")
}

configure<JavaPluginConvention> {
    sourceCompatibility = JavaVersion.VERSION_1_8
}

