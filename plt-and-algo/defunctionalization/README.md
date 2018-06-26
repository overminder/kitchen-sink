## Basic Idea

Instead of representing closures as a single `(funcEntryPtr, payloads)`, we
split them into two parts:

- (funcTag, payloads)
- `apply :: Closure -> Value`

## Issues

The problem is, the apply function can get very big. Consider that compilers
usually have superlinear complexity, it would be very slow to compile
this function.

## Related Work

Sandboxed environments such as WebAssembly make use of this approach,
instead of the direct approach, for security reasons.

### Readings

- Defunctionalization at Work
- Polymorphic Typed Defunctionalization
- Definitional Interpreters for Higher-Order Programming Languages
