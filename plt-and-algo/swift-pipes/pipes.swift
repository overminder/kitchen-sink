// The uninhabited type.
public final class Void {
    private init() {}
}

// Based on https://hackage.haskell.org/package/pipes with
// only minor differences: we only support the pull-based
// interface and one kind of monad, the cont monad.
//
// We also don't have a strong enough type system to force effectful
// actions to happen inside the monad - it's therefore the user's
// responsibility to ensure this.
//
// The indirect keyword is used here as a serious optimization - boxed object repr helps to
// reduce excessive copying in the then() function. Under swiftc-2.2 -O, a simple sum loop
// is 400% (!) faster (100k iterations/s vs 400k iterations/s) when the Proxy type is
// annotated with the indirect keyword. (XXX: on my old Haswell laptop both
// variants perform equally.)
indirect public enum Proxy<I, O, R> {

    // Request the upstream to provide an input (pull).
    case Request(I -> Proxy<I, O, R>)

    // Respond to the downstream's request with an output.
    // The resulting Proxy is inside a thunk since that a good way
    // to implement laziness here. It's not a waste of space / efficiency
    // as after all if we don't put a thunk here, we will still need to
    // box the Proxy by adding an indirect annotation (XXX: it's not the case
    // anymore now that the whole type is boxed).
    case Respond(O, () -> Proxy<I, O, R>)

    // The value is behind a monadic action.
    case RunM(Cont<Proxy<I, O, R>>)

    // A pure value.
    case Pure(R)
    
    public func bind<R2>(f: R -> Proxy<I, O, R2>) -> Proxy<I, O, R2> {
        while (true) {
            switch (self) {
            case .Request(let ik):
                return .Request({ i in ik(i).bind(f) })
            case .Respond(let o, let m_):
                return .Respond(o, { m_().bind(f) })
            case .RunM(let mp):
                return .RunM(mp.bind({ p_ in .Pure(p_.bind(f)) }))
            case .Pure(let r):
                return f(r)
            }
        }
    }

    // Not quite useful as the data constructor provides better type inference support.
    public static func pure(r: R) -> Proxy<I, O, R> {
        return .Pure(r)
    }
    
    public func fmap<R2>(f: R -> R2) -> Proxy<I, O, R2> {
        return self.bind({ a in .Pure(f(a)) })
    }

    public func thatReturns<R2>(r: R2) -> Proxy<I, O, R2> {
        return self.fmap({ _ in r })
    }
    
    public func then<O2>(p2: Proxy<O, O2, R>) -> Proxy<I, O2, R> {
        return then_(self, p2)
    }
}

public class Proxies {
    public static func lifted<I, O, R>(f: I -> O) -> Proxy<I, O, R> {
        return .Request({ i in .Respond(f(i), { lifted(f) }) })
    }
    
    public static func liftedEither<I, O, R>(f: I -> Either<R, O>) -> Proxy<I, O, R> {
        return .Request({ i in
            switch (f(i)) {
            case .Left(let r):
                return .Pure(r)
            case .Right(let o):
                return .Respond(o, { liftedEither(f) })
            }
        })
    }
    
    public static func eachP<I, O>(xs: AnyGenerator<O>) -> Proxy<I, O, ()> {
        if let a = xs.next() {
            return .Respond(a, { eachP(xs) })
        } else {
            return .Pure(())
        }
    }
    
    public static func logWithTag<A, R>(tag: String) -> Proxy<A, A, R> {
        return .RunM(.Pure(Proxy<A, A, R>.Request { a in
            print("[\(tag)] \(a)")
            return .Respond(a, { logWithTag(tag) })
        }))
    }

    public static func printC<A>() -> Proxy<A, Void, ()> {
        return .RunM(.Pure(Proxy<A, Void, ()>.Request { a in
            print(a)
            return printC()
        }))
    }

    public static func enumFromP(i: Int) -> Proxy<Void, Int, ()> {
        return .Respond(i, { enumFromP(i + 1) })
    }

    public static func takeP<A>(n: Int) -> Proxy<A, A, ()> {
        if (n <= 0) {
            return .Pure()
        } else {
            return .Request({ a in
                return .Respond(a, { self.takeP(n - 1) })
            })
        }
    }
    
    // I can't use type equalvalence here, and the subtype constaint provided by the
    // extension doesn't play well with type inference.
    public static func runEffect<R>(p: Proxy<Void, Void, R>, _ k: R -> ()) {
        runEffect_(p, k)
    }
}

// See Pipes.Core.(+>>) and (>>~)
// I inlined (>>~) so that we can do trampolining if the composition is pure.
func then_<I, M, O, R>(i2m0: Proxy<I, M, R>, _ m2o0: Proxy<M, O, R>) -> Proxy<I, O, R> {
    var i2m = i2m0
    var m2o = m2o0

    while (true) {
        switch (m2o) {
        case .Request(let mk):
            switch (i2m) {
            case .Request(let ik):
                return .Request({ i in then_(ik(i), m2o) })
            case .Respond(let m, let i2m_):
                i2m = i2m_()
                m2o = mk(m)
                continue
            case .RunM(let mp):
                return .RunM(mp.bind { i2m_ in
                    .Pure(then_(i2m_, m2o))
                })
            case .Pure(let r):
                return .Pure(r)
            }
        case .Respond(let o, let m2o_):
            return .Respond(o, { then_(i2m, m2o_()) })
        case .RunM(let mp):
            return .RunM(mp.bind { m2o_ in
                .Pure(then_(i2m, m2o_))
            })
        case .Pure(let r):
            return .Pure(r)
        }
    }
    
}

// Run the rest of the pipe (i.e., the continuations). This also does trampolining.
func runEffect_<I: Void, O: Void, R>(p0: Proxy<I, O, R>, _ k: R -> ()) {
    var p = p0
    while (true) {
        switch (p) {
        case .Pure(let r):
            return k(r)
        case .RunM(let mp):
            switch (mp.deref()) {
            case .Pure(let p_):
                p = p_
            case .Run(let runP):
                runP { p_ in runEffect_(p_, k) }
                return
            }
        default:
            fatalError("Not reachable")
        }
    }
}

final class SumP {
    var i: Int = 0
    
    func consume() -> Proxy<Int, Void, ()> {
        return .Request({ di in
            self.i += di
            return .RunM(.Pure(self.consume()))
        })
    }
    
    func consumeSync() -> Proxy<Int, Void, ()> {
        return .Request({ di in
            self.i += di
            return self.consumeSync()
        })
    }
}

// A continuation monad with the support for trampoling immediately available values.
//
// Different from the Proxy type, this performs a bit better (~20%) without the indirect keyword.
// I guess its because all the variants's payload types (A, <closure> and <closure>) are already
// boxed and they have the same size.
public enum Cont<A> {
    case Pure(A)
    case Run((A -> ()) -> ())
    case Thunk(() -> Cont<A>)
    
    public func bind<B>(f: A -> Cont<B>) -> Cont<B> {
        switch (self) {
        case .Pure(let a):
            return .Thunk({
                f(a)
            })
        case .Run(let runA):
            return .Run({ k in
                runA({ a in
                    f(a).run(k)
                })
            })
        case .Thunk(let thunk):
            return .Thunk({
                thunk().bind(f)
            })
        }
    }
    
    public func deref() -> StrictCont<A> {
        var m = self
        while (true) {
            switch (m) {
            case .Pure(let a):
                return .Pure(a)
            case .Run(let runA):
                return .Run(runA)
            case .Thunk(let thunk):
                m = thunk()
                continue
            }
        }
    }
    
    public func run(k: A -> ()) {
        deref().run(k)
    }
    
    public static func pure(a: A) -> Cont<A> {
        return .Pure(a)
    }
    
    public func fmap<B>(f: A -> B) -> Cont<B> {
        switch (self) {
        case .Pure(let a):
            return .Thunk({ .Pure(f(a)) })
        case .Run(let runA):
            return .Run({ k in runA({ a in k(f(a)) }) })
        case .Thunk(let thunk):
            return .Thunk({ thunk().fmap(f) })
        }
    }
}

public class Promise<A> {
    var value: PromiseValue<A> = PromiseValue<A>.NotYet([])
    
    public static func pure(a: A) -> Promise<A> {
        let p = Promise()
        p.fire(a)
        return p
    }
    
    public func asCont() -> Cont<A> {
        return Cont<A>.Run({ k in
            self.attachListener(k)
        })
    }
    
    public func attachListener(k: A -> ()) -> Promise<A> {
        value.attachListener(k)
        return self
    }
    
    public func fire(a: A) -> Promise<A> {
        precondition(tryFire(a), "Fired multiple times - used tryFire instead")
        return self
    }
    
    public func tryFire(a: A) -> Bool {
        return value.tryFire(a)
    }
    
    public func fmap<B>(f: A -> B) -> Promise<B> {
        let pb = Promise<B>()
        attachListener({ a in pb.fire(f(a)) })
        return pb
    }
}

enum PromiseValue<A> {
    case NotYet([A -> ()])
    case Pure(A)
    
    mutating func attachListener(k: A -> ()) {
        switch (self) {
        case .NotYet(var ks):
            ks.append(k)
            self = .NotYet(ks)
        case .Pure(let a):
            k(a)
        }
    }
    
    mutating func tryFire(a: A) -> Bool {
        switch (self) {
        case .NotYet(let ks):
            for k in ks {
                k(a)
            }
            self = .Pure(a)
            return true
        case .Pure(_):
            return false
        }
    }
}

// Without the thunk variant.
public enum StrictCont<A> {
    case Pure(A)
    case Run((A -> ()) -> ())
    
    // Run the cont in a tail-recursive manner. This relies that the user to correctly
    // use the .Pure constructor to represent immediately available values.
    public func run(k: A -> ()) {
        switch (self) {
        case .Pure(let a):
            k(a)
        case .Run(let runA):
            runA(k)
        }
    }
}

// The venerated anonymous union type. As usual, the default Functor implementation is right-biased.
public enum Either<E, A> {
    case Left(E)
    case Right(A)
    
    public func isRight() -> Bool {
        switch (self) {
        case .Left(_):
            return false
        case .Right(_):
            return true
        }
    }
    
    public func bind<B>(f: A -> Either<E, B>) -> Either<E, B> {
        switch (self) {
        case .Left(let e):
            return .Left(e)
        case .Right(let a):
            return f(a)
        }
    }
    
    public func fmap<B>(f: A -> B) -> Either<E, B> {
        switch (self) {
        case .Left(let e):
            return .Left(e)
        case .Right(let a):
            return .Right(f(a))
        }
    }
    
    public func fmapRight<F>(f: E -> F) -> Either<F, A> {
        switch (self) {
        case .Left(let e):
            return .Left(f(e))
        case .Right(let a):
            return .Right(a)
        }
    }
    
    public func elim<B>(a2b: A -> B, _ e2b: E -> B) -> B {
        switch (self) {
        case .Left(let e):
            return e2b(e)
        case .Right(let a):
            return a2b(a)
        }
    }
}

public class Eithers {
    public static func fromTry<A>(f: () throws -> A) -> Either<ErrorType, A> {
        do {
            return .Right(try f())
        } catch (let e) {
            return .Left(e)
        }
    }
}

// The identity function.
func id<A>(a: A) -> A { return a }

// The elimination function for Optional<A>, with a lazily evaluated `otherwise` branch.
func maybe<A, B>(mbA: A?, _ a2b: A -> B, _ orB: () -> B) -> B {
    if let a = mbA {
        return a2b(a)
    } else {
        return orB()
    }
}


let sum = SumP()
let eff = Proxies.enumFromP(0)
    .then(Proxies.takeP(100000))
    // consumeSync has 2x the performance of the asynchronous variant.
    .then(sum.consumeSync())

Proxies.runEffect(eff) {
    print("res = \(sum.i)")
}

