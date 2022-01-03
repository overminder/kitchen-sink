### Inspiration

We've been using dependency injection (DI) a lot in "enterprise" codebases,
to achieve inversion of control (IoC). This allows us to cleanly separate
the codebase into smaller components (modules), which helps with:
- Team work (developers can work on different modules in parallel)
- Unit testing (A module can be tested on its own, and any of its dependencies
  can be mocked)
- Readability and maintenance (each module can be reasoned about separately)

Besides OOP-style DI, are there any other approaches of IoC?

### IoC in FP

I happened to know that FP languages, Haskell in particular, have other
means to achieve IoC:
- Reader monad hides function parameters. This may seem to be trivial
  but it does capture the essence of IoC. Coupled with type classes and
  type inference, it's natural to just write functions and use whatever
  dependency that's needed. The function's inferred type will show exactly
  its dependencies.
  + E.g. see Datatypes a la carte
- Free monad builds up binding structures that can be interpreted in any
  way. Each use case can define their own interpreter (unit testing,
  production, etc).

## Comparison

It's good to have alternatives. But how do there approaches compare?

### Testing

It's common to see Mockito-style mocks in OOP. The mocks are seemingly
declarative, but the order matters! So essentially each mock is effectful,
and at the end the test code often becomes operational and imperative.

I guess we don't necessarily want the same test style in FP (do you want
your test to be in a `Mock` monad?). Property based tests are more common
in FP. However not all tests can be written as property tests.

There are definitely ways to do property-based testing in OOP, and when
done correctly they should look similar to FP. However the overall support
for property-based testing (ADT, type classes etc) is kind of lacking in OOP...

