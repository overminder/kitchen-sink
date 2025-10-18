### Parsing String into SExp

SExp is a simple s-expression, which can be an atom (sym or int) or a list of SExps.

```
sym-start ::= ( [a-zA-Z!@#$%^&*_+|:<>?/\/\-=.] )+
digit ::= [0-9]
SSym ::= sym-start (sym-start | digit)*
SInt ::= '-'? digit+
SExp ::= SSym | SInt | SLit
SList ::= '(' SExp* ')' | '[' SExp* ']'
comment ::= ';' (any-char)* '\n'
```

For example (omitting sourceLoc field for brevity),

- "123" is parsed into SInt(123)
- "(123)" is parsed into SList(SInt(123))
- "(123 456)" is parsed into SList(SInt(123), SInt(456))
- "foo" is parsed into SSym("foo")
- "(foo bar)" is parsed into SList(SSym("foo"), SSym("bar"))
- "(define x (+# 1 2))" is parsed into SList(SSym("define"), SSym("x"), SList(SSym("+#"), SInt(1), SInt(2)))
- "-123" is parsed into SInt(-123). Here even though both SSym and SInt rules match, SInt takes precedence.

Each SExp also has a sourceLoc field, representing the starting location of the expression in the source code. This is important for error reporting and debugging.

### Parsing SExp into Exp

Exp is a more complex expression, representing binding structures, function abstractions, applications, and primitive values and operations.

```
(let
  ([x 1]
   [y 2])
  (+# x y))
;; Is parsed into ELet(listOf("x" to EInt(1), "y" to EInt(2)), EPrimOp(PrimOp.INT_ADD, listOf(EVar("x"), EVar("y"))))

(lambda (x y) (+# x y))
;; Is parsed into EAbs(listOf("x", "y"), EPrimOp(PrimOp.INT_ADD, listOf(EVar("x"), EVar("y"))))
```

The list of primitive ops include:

- "+#" for INT_ADD
- "-#" for INT_SUB
- "<#" for INT_LT
