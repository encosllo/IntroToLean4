-- # Basic Syntax

-- This is a comment

/-
This is a multi-line comment.
It can span multiple lines.
Useful for longer explanations.
-/

-- The `#check` command is used to inspect the type of
-- an expression, definition, or theorem in Lean
#check 42
#check 'h'
#check ['h', 'e', 'l', 'l', 'o']
#check "hello"
#check true
#check Nat

-- The `#print` command allows you to inspect
-- the definition of a function, theorem, or
-- other named entity
#print Bool
#print Nat
#print Char
#print List
#print String

-- We cannot `#print Type` because this is a built-in concept
-- in Lean's logical foundation, not a user-defined
-- term or definition
-- #print Type

-- The `def` keyword is used to define a function or a value

-- Definition of number pi
def pi : Float := 3.1415926
-- Definition of the sum of two natural numbers
def sum (a b : Nat) : Nat := a + b

-- The `fun` keyword is used to define anonymous
-- functions (also known as lambda functions).
-- We will write `\lambda` to write λ

-- Two anonymous ways of defining
-- the sum of two natural numbers
#check fun (a b : Nat) => a + b
#check λ (a b : Nat) => a + b

-- The function type
-- if A and B are types, then A → B is another type,
-- the type of all mappings from A to B
-- We will write `\to` to write the arrow

-- The type of all mappings from Nat to Nat
#check Nat → Nat
-- An example of an element of the above type
#check sum 3

-- Two new ways of defining the sum of two natural numbers
-- Using `fun`
def sum2 : Nat → Nat → Nat := fun a b => a + b
-- The next approach utilizes the keywords `by`, `intro`, and `exact`
-- The `by` keyword signals that the function definition will
-- be constructed interactively using *tactics*
-- Tactics are commands that assist in building definitions
-- or proofs step by step.
-- To enter the interactive proof mode, we indent the text.
-- Specifically, the `intro` tactic
-- is used to introduce the function's arguments, while the
-- `exact` tactic is used to provide the precise value
-- that satisfies the goal; in this case, producing
-- a natural number
def sum3 : Nat → Nat → Nat := by
    intro a b
    exact a + b

-- The `cases` tactic splits the definition into
-- two branches based on the value of the input
-- We will use it to define the `Negation` function
-- for Booleans
def BoolNot : Bool → Bool := by
  intro b
  cases b
  -- b = false
  exact true
  -- b = true
  exact false

-- The `match` keyword is used for pattern matching
-- This is a more concise way to handle different
-- cases of the input
def BoolNot2 : Bool → Bool := by
  intro b
  match b with
    | false => exact true
    | true  => exact false

-- The `let` keyword  is used to define local variables
-- or terms within a proof or expression
def sphereVolume (r : Float) : Float :=
  let pi : Float := 3.1415926
  (4/3) * pi * r^3

-- The `#eval` command is used to evaluate an expression
-- and display its result
#eval sum 3 4
#eval (sum 3) 4
#eval (fun (a b : Nat) => a + b) 3 4
--
#eval pi
#eval Nat.succ 4
#eval UInt32.isValidChar 104
#eval 'h'.val
#eval String.mk ['h', 'e', 'l', 'l', 'o']
#eval "hello".data

-- The keyword `variable` is used to declare variables
-- that can be used later in the code
-- These variables are implicitly available in the
-- context of any theorem, definition, or proof that follows
variable (m n : Nat)
#check m

-- We can also create namespaces and define variables within
-- them. Namespaces help organize code and can be collapsed
-- in the editor to improve readability.
-- Variables defined inside a namespace are only
-- accessible within that namespace
namespace WorkSpace
-- Define a natural number `r` with the value 27
def r : Nat := 27
-- The variable `r` is perfectly defined within the namespace
#eval r
end WorkSpace

-- Evaluating `r` outside the namespace will result
-- in an error
-- #eval r  -- Error: unknown identifier 'r'

-- To access `r`, we must reference it using its namespace
#eval WorkSpace.r  -- Output: 27

-- The `open` keyword is used to bring definitions,
-- theorems, or namespaces into the current scope
open WorkSpace
#eval r
