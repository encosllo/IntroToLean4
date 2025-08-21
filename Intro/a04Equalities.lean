-- # Equalities

variable (X : Type)
variable (x y a b c d : X)
variable (P : X → Prop)

-- ## Equality
#check Eq
#check Eq x y
#check x = y

#print Eq

-- Negation of Equality `≠` (`\neq`)
#check Ne
#check Ne x y
#check x ≠ y

-- ## Reflexivity
-- `Eq.rfl` is the unique constructor for `Eq`
-- It returns an element of type `a = a`
-- It can also be used as `rfl`, where the variable `a`
-- is implicit
theorem TEqRfl {a : X} : a = a := by
  exact rfl

-- Lean will allow `rfl` on any pair of terms that are
-- definitionally equal
theorem T1 : 2 + 2 = 4 := by
  exact rfl

-- ## Symmetry
-- If we have `a = b` as a hypothesis, we can infer
-- `b = a` by applying the symmetric property of equality
#print Eq.symm

theorem TEqSymm (h : a = b) : (b = a) := by
  exact Eq.symm h -- also (exact h.symm)

-- ## Transitivity
-- If we have `a = b` and `b = c` as a hypothesis, we can
-- infer `a = c` by applying the transitive property of
-- equality
#print Eq.trans

theorem TEqTrans (h1 : a = b) (h2 : b = c) : (a = c) := by
  exact Eq.trans h1 h2 -- also (exact h1.trans h2)

-- ## Rewrite
-- We can use an equality to `rewrite` occurrences of either
-- side of the equation, either globally throughout an
-- expression or selectively in specific locations
-- We can also use `rw`
theorem TEqRw (h1 : a = b) : P b ↔ P a := by
  apply Iff.intro
  -- P b → P a
  intro h2
  rewrite [h1] -- rewrites the goal using h1
  exact h2
  -- P a → P b
  intro h2
  rw [h1] at h2 -- rewrites h2 using h1
  exact h2

-- ## Calc
-- The `calc` command is used to perform calculations
-- or proofs by chaining together a series of equalities
-- or inequalities
theorem TCalc (h1 : a = b) (h2 : b = c) (h3: c = d) : (a = d) := by
  calc
    a = b := by rw [h1]
    _ = c := by rw [h2]
    _ = d := by rw [h3]

-- ## Types with meaningful equality
-- While equality is defined for all types, its meaning
-- depends on the type
-- #eval x = y -- Returns error
#eval 2 + 2 = 4 -- Returns true

-- Some types have decidable equality, meaning there is
-- an algorithm to determine whether two terms of that
-- type are equal
#check DecidableEq
#print DecidableEq

-- We provide a proof that `Bool` has decidable
-- equality. In it we use the keyword `noConfusion`
-- It expresses the fact that different constructors
-- of an inductive type are disjoint and injective
def DecidableEqBool : DecidableEq Bool := by
  intro a b
  match a, b with
    | false, false => exact isTrue rfl
    | false, true  => exact isFalse (fun h => Bool.noConfusion h)
    | true , false => exact isFalse (fun h => Bool.noConfusion h)
    | true , true  => exact isTrue rfl

-- Other examples of types with decidable equality
#check Nat.decEq
#check Int.decEq
#check String.decEq

-- The following function recieves two natural
-- numbers `n` and `m` and returns `true` if they
-- are equal and `false` otherwise
-- It uses the `by_cases` tactic
def Charp : Nat → Nat → Bool := by
  intro n m
  by_cases n = m
  -- Case n = m
  exact true
  -- Case n ≠ m
  exact false

-- This is an alternative description using
-- `if ... then ... else`
def Charp2 : Nat → Nat → Bool :=
fun n m => if n = m then true else false

-- In general equality in an arbitrary type is
-- non necessarily computable. Thus, the above
-- function in an arbitrary type is marked as
-- `noncomputable`
noncomputable def Charpoint {A : Type} : A → A → Bool := by
  intro a b
  by_cases a = b
  -- Case a = b
  exact true
  -- Case a ≠ b
  exact false

-- To avoid the above modifier, we have to
-- explicitly assume that the arbitrary type `A`
-- has decidable equality
def Charpoint2 {A : Type} [DecidableEq A] : A → A → Bool :=
fun n m => if n = m then true else false

-- In `Prop` equality is logical equivalence (`↔`)
-- Equality in `Prop` is not decidable
#check propext
#print propext

-- `propext` is an axiom
-- Axioms are assumed by definition,
-- rather than being derived from existing theorems

theorem TEqProp {Q : Prop} : (Q ∧ True) = Q := by
  apply propext
  apply Iff.intro
  -- Q ∧ True → Q
  intro h2
  exact h2.left
  -- Q → Q ∧ True
  intro h2
  apply And.intro
  exact h2
  trivial

-- We can always check the axioms on which a theorem
-- relies upon using `#print axioms`
#print axioms TEqProp
