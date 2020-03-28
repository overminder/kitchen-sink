### Synopsis

Notes taken when I was reading the [Kotlin
compiler](https://github.com/JetBrains/kotlin/tree/master/compiler).

### reading notes

`notes/` contains the notes that I took while reading the source.
Note that Github's PDF viewer doesn't support links, so please [use google doc
viewer to view the generated PDF file](https://docs.google.com/viewer?url=https://github.com/overminder/kitchen-sink/raw/master/writings/kotlin-compiler/notes/main.pdf).

### out-of-tree sources

`runner/` contains a kotlinn runner function that need to be injected to the
kotlin repo to run. These are useful because we can run arbitrary kotlin
sources and set breakpoints on the compiler to learn about the compilation
pipelines.

### Faster Compiler Playground

`dylib-runner/` uses the compiler as a library. This would makes compilation
a lot faster but we lose code navigation inside the compiler (source jar
would be useful?)
