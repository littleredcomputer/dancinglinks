group = "net.littleredcomputer"
version = "1.0-SNAPSHOT"

plugins {
    java
    application
}

application {
    mainClassName = "net.littleredcomputer.knuth7.Main"
}

repositories {
    mavenCentral()
}

dependencies {
    testCompile("junit", "junit", "4.12")
    testCompile("com.github.npathai", "hamcrest-optional", "2.0.0")
    compile("com.google.guava", "guava", "23.5-jre")
    compile("org.apache.logging.log4j", "log4j-api", "2.10.0")
    compile("org.apache.logging.log4j", "log4j-core", "2.10.0")
    compile("commons-cli", "commons-cli", "1.4")
}

configure<JavaPluginConvention> {
    sourceCompatibility = JavaVersion.VERSION_1_8
}

