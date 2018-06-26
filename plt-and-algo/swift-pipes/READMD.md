Just a partial Swift implementation of
[Tekmo](https://www.reddit.com/user/tekmo)'s
[brilliant pipes library](https://hackage.haskell.org/package/pipes).

The performance is quite bad as we don't have rewrite rules in Swift.

XXX: this seems to be leaking sometimes. ARC is too bad...

# RUN

Get [Swift](https://swift.org/) and install its [deps](deps). Then run

    swiftc pipes.swift && ./pipes

to compile and run the example.
