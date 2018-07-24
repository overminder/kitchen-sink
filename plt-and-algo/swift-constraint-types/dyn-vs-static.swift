// Compiles on Apple Swift version 4.1.2 (swiftlang-902.0.54 clang-902.0.39.2)
// Illustrates the difference between static and dynamic protocol types.

class Foo {
    var foo: Int = 0
    var fooP2: Int = 0
}

protocol FooP: class {
    var fooP: Int { get }
    var fooP2: Int { get }
}

class Bar: Foo, FooP {
    var fooP: Int = 0
}

typealias DynType = Foo & FooP

func bothAsStaticType<A>(_ a: A) where A: Foo & FooP {
    // Note the & brings in the setter.
    a.fooP2 = 666
}

// Equivalent
func bothAsStaticType2<A>(_ a: A) where A: DynType {
}

func klassAsDynType(_ a: Foo) {
}

func protoAsDynType(_ a: FooP) {
}

func bothAsDynType(_ a: Foo & FooP) -> Int {
    return a.foo + a.fooP
}

// Equivalent
func bothAsDynType2(_ a: DynType) -> Int {
    return a.foo + a.fooP
}

var dynArray = [DynType]()
dynArray.append(Bar())

class AnyDynType: Foo & FooP {
    let impl: DynType
    init(_ impl: DynType) {
        self.impl = impl
    }

    override var foo: Int {
        get { return impl.foo }
        set { impl.foo = newValue }
    }
    var fooP: Int {
        return impl.fooP
    }
    override var fooP2: Int {
        get { return impl.fooP2 }
        set { impl.fooP2 = newValue }
    }
}

for x in dynArray {
    // x is a DynType so these static typed funcs can't infer x's type...
    // bothAsStaticType(x)
    // bothAsStaticType2(x)
    // We need a dyn-to-static type wrapper:
    bothAsStaticType(AnyDynType(x))
    bothAsStaticType2(AnyDynType(x))

    klassAsDynType(x)
    protoAsDynType(x)
    _ = bothAsDynType(x)
    _ = bothAsDynType2(x)
}

