### Synopsis

Notes taken when I was reading the [Kotlin
compiler](https://github.com/JetBrains/kotlin/tree/master/compiler).

### out-of-tree sources

`runner/` contains a kotlinn runner function that need to be injected to the
kotlin repo to run. These are useful because we can run arbitrary kotlin
sources and set breakpoints on the compiler to learn about the compilation
pipelines.
