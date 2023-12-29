def hello := "world"

def add1 (n: Nat): Nat := n + 1

#eval add1 5
#eval (1 - 2 : Int)
#check (add1 : Nat → Nat)

def joinStringsWith (x y z : String) : String := String.append y (String.append x z)

#eval joinStringsWith ", " "hello" "world"
#check joinStringsWith ", "

def volume (height width depth : Nat) : Nat := height * width * depth

#eval volume 1 2 3

def Str : Type := String

structure Point where
  x : Float
  y : Float
deriving Repr

-- Nice struct field overload
structure PointN where
  x : Nat
  y : Nat
deriving Repr

def somePoint := { x := 0, y := 0 : Point }
-- Nice dot property accessor
#eval somePoint.x
-- Which is the same thing as
#eval Point.x somePoint
-- Update a record
#eval { somePoint with x := 2 }

-- Generalized dot syntax
#eval [1, 2].append [3]
-- Even though map is (A → B) -> [A] → [B], .map still works in the expected way.
-- The "method receiver" is inferred by exact type matching (this does mean autocompletion needs to
-- index a lot more methods... or does it only search in the receiver's namespace, i.e. List?)
#eval [1, 2].map (λx ↦ x)
#eval (List.map add1 [1,2])
-- doesn't work: #eval (add1.map [1,2])

-- .1: Universal shorthand for the first component
#check (1, 2).1

def Prod.str : Nat × Nat → String :=
  λ(x, y) => "(" ++ toString x ++ ", " ++ toString y ++ ")"

-- Can't reuse the same function name -- Overloading is done in other ways
def Prod.str2 : Int × Int → String :=
  λ(x, y) => "(" ++ toString x ++ ", " ++ toString y ++ ")"

#check Sum
#check Option

#check (·  + 1)
#check (·  + · )
