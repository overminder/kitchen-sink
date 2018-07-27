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

    // request the upstream to provide an input (pull).
    case request(I -> Proxy<I, O, R>)

    // respond to the downstream's request with an output.
    // The resulting Proxy is inside a thunk since that a good way
    // to implement laziness here. It's not a waste of space / efficiency
    // as after all if we don't put a thunk here, we will still need to
    // box the Proxy by adding an indirect annotation (XXX: it's not the case
    // anymore now that the whole type is boxed).
    case respond(O, () -> Proxy<I, O, R>)

    // The value is behind a monadic action.
    case runM(Cont<Proxy<I, O, R>>)

    // A pure value.
    case pure(R)
    
    public func bind<R2>(f: @escaping R -> Proxy<I, O, R2>) -> Proxy<I, O, R2> {
        while (true) {
            switch (self) {
            case .request(let ik):
                return .request({ i in ik(i).bind(f) })
            case .respond(let o, let m_):
                return .respond(o, { m_().bind(f) })
            case .runM(let mp):
                return .runM(mp.bind({ p_ in .pure(p_.bind(f)) }))
            case .pure(let r):
                return f(r)
            }
        }
    }

    // Not quite useful as the data constructor provides better type inference support.
    public static func pure(r: R) -> Proxy<I, O, R> {
        return .pure(r)
    }
    
    public func fmap<R2>(f: R -> R2) -> Proxy<I, O, R2> {
        return self.bind({ a in .pure(f(a)) })
    }

    public func thatReturns<R2>(_ r: R2) -> Proxy<I, O, R2> {
        return self.fmap({ _ in r })
    }
    
    public func then<O2>(_ p2: Proxy<O, O2, R>) -> Proxy<I, O2, R> {
        return then_(self, p2)
    }
}

public class Proxies {
    public static func lifted<I, O, R>(_ f: @escaping I -> O) -> Proxy<I, O, R> {
        return .request({ i in .respond(f(i), { lifted(f) }) })
    }
    
    public static func liftedEither<I, O, R>(_ f: @escaping I -> Either<R, O>) -> Proxy<I, O, R> {
        return .request({ i in
            switch (f(i)) {
            case .Left(let r):
                return .pure(r)
            case .Right(let o):
                return .respond(o, { liftedEither(f) })
            }
        })
    }
    
    public static func eachP<I, O>(_ xs: AnyGenerator<O>) -> Proxy<I, O, ()> {
        if let a = xs.next() {
            return .respond(a, { eachP(xs) })
        } else {
            return .pure(())
        }
    }
    
    public static func logWithTag<A, R>(_ tag: String) -> Proxy<A, A, R> {
        return .runM(.pure(Proxy<A, A, R>.request { a in
            print("[\(tag)] \(a)")
            return .respond(a, { logWithTag(tag) })
        }))
    }

    public static func printC<A>() -> Proxy<A, Void, ()> {
        return .runM(.pure(Proxy<A, Void, ()>.request { a in
            print(a)
            return printC()
        }))
    }

    public static func enumFromP(_ i: Int) -> Proxy<Void, Int, ()> {
        return .respond(i, { enumFromP(i + 1) })
    }

    public static func takeP<A>(_ n: Int) -> Proxy<A, A, ()> {
        if (n <= 0) {
            return .pure()
        } else {
            return .request({ a in
                return .respond(a, { self.takeP(n - 1) })
            })
        }
    }
    
    // I can't use type equalvalence here, and the subtype constaint provided by the
    // extension doesn't play well with type inference.
    public static func runEffect<R>(_ p: Proxy<Void, Void, R>, _ k: @escaping R -> ()) {
        runEffect_(p, k)
    }
}

// See Pipes.Core.(+>>) and (>>~)
// I inlined (>>~) so that we can do trampolining if the composition is pure.
func then_<I, M, O, R>(_ i2m0: Proxy<I, M, R>, _ m2o0: Proxy<M, O, R>) -> Proxy<I, O, R> {
    var i2m = i2m0
    var m2o = m2o0

    while (true) {
        switch (m2o) {
        case .request(let mk):
            switch (i2m) {
            case .request(let ik):
                return .request({ i in then_(ik(i), m2o) })
            case .respond(let m, let i2m_):
                i2m = i2m_()
                m2o = mk(m)
                continue
            case .runM(let mp):
                return .runM(mp.bind { i2m_ in
                    .pure(then_(i2m_, m2o))
                })
            case .pure(let r):
                return .pure(r)
            }
        case .respond(let o, let m2o_):
            return .respond(o, { then_(i2m, m2o_()) })
        case .runM(let mp):
            return .runM(mp.bind { m2o_ in
                .pure(then_(i2m, m2o_))
            })
        case .pure(let r):
            return .pure(r)
        }
    }
    
}

// run the rest of the pipe (i.e., the continuations). This also does trampolining.
func runEffect_<I: Void, O: Void, R>(_ p0: Proxy<I, O, R>, _ k: @escaping R -> ()) {
    var p = p0
    while (true) {
        switch (p) {
        case .pure(let r):
            return k(r)
        case .runM(let mp):
            switch (mp.deref()) {
            case .pure(let p_):
                p = p_
            case .run(let runP):
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
        return .request({ di in
            self.i += di
            return .runM(.pure(self.consume()))
        })
    }
    
    func consumeSync() -> Proxy<Int, Void, ()> {
        return .request({ di in
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
    case pure(A)
    case run((A -> ()) -> ())
    case Thunk(() -> Cont<A>)
    
    public func bind<B>(_ f: @escaping A -> Cont<B>) -> Cont<B> {
        switch (self) {
        case .pure(let a):
            return .Thunk({
                f(a)
            })
        case .run(let runA):
            return Cont.run({ k in
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
            case .pure(let a):
                return .pure(a)
            case .run(let runA):
                return .run(runA)
            case .Thunk(let thunk):
                m = thunk()
                continue
            }
        }
    }
    
    public func run(_ k: @escaping_ A -> ()) {
        deref().run(k)
    }
    
    public static func pure(a: A) -> Cont<A> {
        return .pure(a)
    }
    
    public func fmap<B>(_ f: @escaping A -> B) -> Cont<B> {
        switch (self) {
        case .pure(let a):
            return .Thunk({ .pure(f(a)) })
        case .run(let runA):
            return Cont.run({ k in runA({ a in k(f(a)) }) })
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
        return Cont<A>.run({ k in
            self.attachListener(k)
        })
    }
    
    public func attachListener(_ k: @escaping A -> ()) -> Promise<A> {
        value.attachListener(k)
        return self
    }
    
    public func fire(_ a: A) -> Promise<A> {
        precondition(tryFire(a), "Fired multiple times - used tryFire instead")
        return self
    }
    
    public func tryFire(_ a: A) -> Bool {
        return value.tryFire(a)
    }
    
    public func fmap<B>(_ f: @escaping_ A -> B) -> Promise<B> {
        let pb = Promise<B>()
        attachListener({ a in pb.fire(f(a)) })
        return pb
    }
}

enum PromiseValue<A> {
    case NotYet([A -> ()])
    case pure(A)
    
    mutating func attachListener(_ k: @escaping A -> ()) {
        switch (self) {
        case .NotYet(var ks):
            ks.append(k)
            self = .NotYet(ks)
        case .pure(let a):
            k(a)
        }
    }
    
    mutating func tryFire(_ a: @escaping A) -> Bool {
        switch (self) {
        case .NotYet(let ks):
            for k in ks {
                k(a)
            }
            self = .pure(a)
            return true
        case .pure(_):
            return false
        }
    }
}

// Without the thunk variant.
public enum StrictCont<A> {
    case pure(A)
    case run((A -> ()) -> ())
    
    // run the cont in a tail-recursive manner. This relies that the user to correctly
    // use the .pure constructor to represent immediately available values.
    public func run(_ k: A -> ()) {
        switch (self) {
        case .pure(let a):
            k(a)
        case .run(let runA):
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

