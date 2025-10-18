### Evaluation in Interpreter

In a broader sense, expressions can be evaluated into values. Evaluation can happen in many ways.
Specifically in interp.kt, we build an interpreter by visiting the AST (`Exp`) to evaluate it into an `IValue`. The
`evaluate` function takes both an `Exp` and an `IEnv` that describes the name-value bindings of the environment.

The interpreter evaluation rules are:

* Literals are no-op: (eval <int>) => <int>, (eval <bool>) => <bool>
* Variables are looked up in the environment: (eval some-var) => (lookup some-var in <env>)
* Lambda abstraction: (eval (lambda (x) <body>)) => IVClosure(abs = <the lambda exp>, env = current <env>)
* Application: (eval (<func-exp> <arg-exps>)) => this one is more involved:
    1. evaluate <func-exp> and <arg-exps> into <func-value> and <arg-values>
    2. check that <func> is an IVClosure
    3. non-destructively extend IVClosure.env by binding <arg-values> to the arg names from IVClosure.abs.args (remember to check that the number of arguments match),
    4. continue to evaluate IVClosure.abs.body in the extended environment from (3), and return its value
* If-exp: (eval (if <cond-exp> <then-exp> <else-exp>)) => this one is also more involved:
    1. evaluate <cond-exp> into <cond-value>
    2. check that <cond-value> is a boolean
    3. if <cond-value> is true, evaluate <then-exp> into <then-value>
    4. if <cond-value> is false, evaluate <else-exp> into <else-value>
    5. return <then-value> or <else-value> based on the result of (2)
* Let-exp: (eval (let <name-exp-pairs> <body>)) => this one is also more involved:
    1. evaluate all exp in <name-exp-pairs>
    2. non-destructively extend <env> by binding the exp values from (1) to the corresponding names from <name-exp-pairs>
    3. continue to evaluate <body> in the extended env from (2), and return its value
* Letrec-exp: (eval (letrec <name-exp-pairs> <body>)) => this one is also more involved:
    1. non-destructively extend the current <env>: For each name in <name-exp-pairs>, freshly allocate a mutable cell (
       `ICell`), and bind the cell with the name. Note that this implementation also requires variable lookup to check and unwrap cells (and throw errors when the cell is uninitialized).
    2. evaluate all exp in <name-exp-pairs>, under the extended <env> from (1)
    3. continue to evaluate <body> in the extended env from (1), and return its value
