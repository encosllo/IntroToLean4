-- # Quantifiers
-- To avoid highlighting unused variables
set_option linter.unusedVariables false

-- We next introduce an arbitrary type `A`
variable (A : Type)

-- ## Predicates
-- A predicate `P` on `A` is a an element of type
-- `A → Prop`
variable (P Q : A → Prop)

-- ### Examples of predicates
-- `False` predicate
def PFalse {A : Type} : A → Prop := fun _ => False

-- `True` predicate
def PTrue {A : Type} : A → Prop := fun _ => True

-- ### Operations on predicates
-- We can
-- Intersection of two predicates
def PAnd {A : Type} (P Q : A → Prop) : A → Prop := by
  intro a
  exact P a ∧ Q a

-- We introduce notation for the intersection (`\and`)
notation : 65 lhs:65 " ∧ " rhs:66 => PAnd lhs rhs
#check P ∧ Q

-- Union of two predicates
def POr {A : Type} (P Q : A → Prop) : A → Prop := by
  intro a
  exact P a ∨ Q a

-- We introduce notation for the union (`\or`)
notation : 65 lhs:65 " ∨ " rhs:66 => POr lhs rhs
#check P ∨ Q

-- Implication of two predicates
def PImplies {A : Type} (P Q : A → Prop) : A → Prop := by
  intro a
  exact P a → Q a

-- We introduce notation for the implication (`\to`)
notation : 65 lhs:65 " → " rhs:66 => PImplies lhs rhs
#check P → Q

-- Double Implication of two predicates
def PDImplies {A : Type} (P Q : A → Prop) : A → Prop := by
  intro a
  exact P a ↔ Q a

-- We introduce notation for the double implication (`\iff`)
notation : 65 lhs:65 " ↔ " rhs:66 => PDImplies lhs rhs
#check P ↔ Q

-- Negation of a predicate
def PNot {A : Type} (P : A → Prop) : A → Prop := by
  intro a
  exact ¬ (P a)

-- We introduce notation for negation (`\not`)
notation : 65  "¬" rhs:66 => PNot rhs
#check ¬P

-- ## Universal quantifier `∀` (`\forall`)
-- The expression `∀ (a : A), P a` is a proposition
-- that asserts that `P a` is true for every `a : A`
#check ∀ (a : A), P a

-- The binding of `∀` does not require to
-- explicitly recall the type of the variable
#check ∀a, P a

-- The binding of `∀` can also be implicit
#check ∀ {a : A}, P a

-- To prove a statement of the form `∀ (a : A), P a`,
-- we typically use the `intro` tactic (or just write a
-- `lambda` function directly in term mode)
-- This introduces an arbitrary element `a` of type `A`
-- and requires us to prove `P a` for that arbitrary `a`
/- theorem T1 uses `sorry`
  theorem T1 : ∀ (a : A), P a := by
    intro a
    sorry
-/

-- On the other hand, if we have a hypothesis
-- `h : ∀ (a : A), P a` and we want to use it
-- for a specific value `a : A`, we can apply
-- `h` on `a` to get `P a`
variable (a : A)
variable (h : ∀ (a : A), P a)
#check (h a)

-- The `specialize` tactic allows us
-- to instantiate a general hypothesis with particular
-- values, making it easier to work with in our proof
theorem T2 (z : A) (h : ∀ (a : A), P a) : P z := by
  specialize h z
  exact h

-- The `specialize` tactic does not work when
-- the binding is implicit. We can explicitly
-- introduce the variable using `@`
theorem T2b (z : A) (h : ∀ {a : A}, P a) : P z := by
  specialize @h z
  exact h

-- ## Existential quantifier `∃` (`\exists`)
-- The expression `∃ (a : A), P xa` is a proposition that
-- asserts that `P a` is true for some `a : A`
#check ∃ (a : A), P a

-- The binding of `∃` does not require to
-- explicitly recall the type of the variable
#check ∃ a, P a

-- The binding of `∃` cannot be implicit
-- The following returns error
-- `#check ∃ {a : A}, P a`

-- There is, however, an inductive type associated
-- to the existential quatifier called `Exists`
#check Exists P
#print Exists

-- The single constructor, `Exists.intro`, constructs
-- a proof of `Exists P` given a witness `a : A` and
-- a proof that `a` satisfies `P`
theorem T3 (z : A) (h : P z) : ∃ (a : A), P a := by
  exact Exists.intro z h

-- Since `Exists` is an inductive type, we can use `cases`
-- on proofs of this type, recovering the witness and
-- the proof that is satisfies the predicate `P`
variable (R : Prop)
theorem T4 (h1 : ∃ (a : A), P a) (h2 : ∀ (a : A), P a → R) : R := by
  cases h1
  rename_i a h3
  specialize h2 a
  exact h2 h3

-- Another alternative is to use `Exists.elim`,
-- the eliminator of the `Exists` type
theorem T5 (h1 : ∃ (a : A), P a) (h2 : ∀ (a : A), P a → R) : R := by
  apply Exists.elim h1
  exact h2

namespace a03Exercises
-- Exercises
open Classical
variable (a b c : A)
variable (R : Prop)

theorem E1 : (∃ (a : A), R) → R := by
  intro h
  cases h
  rename_i a h
  exact h

theorem E2 (a : A) : R → (∃ (a : A), R) := by
  intro h
  apply Exists.intro a
  exact h

theorem E3 : (∃ (a : A), P a ∧ R) ↔ (∃ (a : A), P a) ∧ R := by
  apply Iff.intro
  -- (∃ a, P a ∧ R) → (∃ a, P a) ∧ R
  intro h
  cases h
  rename_i a h
  apply And.intro
  -- Left
  apply Exists.intro a
  exact h.left
  -- Right
  exact h.right
  -- (∃ a, P a) ∧ R → ∃ a, P a ∧ R
  intro h
  cases h.left
  rename_i a h1
  apply Exists.intro a
  apply And.intro
  exact h1
  exact h.right

theorem E4 : (∃ (a : A), (P ∨ Q) a) ↔ (∃ (a : A), P a) ∨ (∃ (a : A), Q a) := by
  apply Iff.intro
  -- (∃ a, (P ∨ Q) a) → (∃ a, P a) ∨ ∃ a, Q a
  intro h1
  cases h1
  rename_i a h1
  cases h1
  -- inl
  rename_i h1
  apply Or.inl
  apply Exists.intro a
  exact h1
  -- inr
  rename_i h1
  apply Or.inr
  apply Exists.intro a
  exact h1
  -- ((∃ a, P a) ∨ ∃ a, Q a) → ∃ a, (P ∨ Q) a
  intro h1
  cases h1
  -- inl
  rename_i h1
  cases h1
  -- inl
  rename_i a h1
  apply Exists.intro a
  exact Or.inl h1
  -- inr
  rename_i h1
  cases h1
  rename_i a h1
  apply Exists.intro a
  exact Or.inr h1

theorem E5 : (∀ (a : A), P a) ↔ ¬(∃ (a : A), (¬P) a) := by
  apply Iff.intro
  -- (∀ (a : A), P a) → ¬∃a, (¬P) a
  intro h1 h2
  cases h2
  rename_i a h2
  exact h2 (h1 a)
  -- (¬∃a, (¬P) a) → ∀ (a : A), P a
  intro h1 a
  false_or_by_contra
  rename_i h2
  have h3 : ∃ (a : A), (¬P) a := by
    apply Exists.intro a
    exact h2
  exact h1 h3

theorem E6 : (∃ (a : A), P a) ↔ ¬ (∀ (a : A), (¬P) a) := by
  apply Iff.intro
  -- (∃a, P a) → ¬∀ (a : A), (¬P) a
  intro h1 h2
  cases h1
  rename_i a h1
  specialize h2 a
  exact h2 h1
  -- (¬∀ (a : A), (¬P) a) → ∃a, P a
  intro h1
  false_or_by_contra
  rename_i h2
  have h3 : ∀ (a : A), (¬ P) a := by
    intro a
    false_or_by_contra
    rename_i h3
    have h4 : P a ∨ ¬ P a := em (P a)
    cases h4
    -- inl
    rename_i h4
    have h5 : ∃ (a : A), P a := Exists.intro a h4
    exact h2 h5
    -- inr
    rename_i h4
    exact h3 h4
  exact h1 h3

theorem E7 : (¬∃ (a : A), P a) ↔ (∀ (a : A), (¬P) a) := by
  apply Iff.intro
  -- (¬∃ a, P a) → ∀ (a : A), (¬P) a
  intro h1 a h2
  have h3 : ∃ (a : A), P a := Exists.intro a h2
  exact h1 h3
  -- (∀ (a : A), (¬P) a) → ¬∃ a, P a
  intro h1 h2
  cases h2
  rename_i a h2
  specialize h1 a
  exact h1 h2

theorem E8 : (¬∀ (a : A), P a) ↔ (∃ (a : A), (¬P) a) := by
  apply Iff.intro
  -- (¬∀ (a : A), P a) → ∃ a, (¬P) a
  intro h1
  false_or_by_contra
  rename_i h2
  have h3 : ∀ (a : A), P a := by
    intro a
    false_or_by_contra
    rename_i h3
    have h4 : ∃ (a : A), (¬ P) a := Exists.intro a h3
    exact h2 h4
  exact h1 h3
  -- (∃ a, (¬P) a) → ¬∀ (a : A), P a
  intro h1 h2
  cases h1
  rename_i a h1
  specialize h2 a
  exact h1 h2

theorem E9 : (∀ (a : A), P a → R) ↔ (∃ (a : A), P a) → R := by
  apply Iff.intro
  -- (∀ (a : A), P a → R) → (∃a, P a) → R
  intro h1 h2
  cases h2
  rename_i a h2
  exact (h1 a) h2
  -- ((∃ a, P a) → R) → ∀ (a : A), P a → R
  intro h1 a h2
  have h3 : ∃ (a : A), P a := Exists.intro a h2
  exact h1 h3

theorem E10 (a : A) : (∃ (a : A), P a → R) → (∀ (a : A), P a) → R := by
  intro h1 h2
  cases h1
  rename_i a2 h1
  specialize h2 a2
  exact h1 h2

theorem E11 (a : A) : (∃ (a : A), R  →  P a) → (R → ∃ (a : A), P a) := by
  intro h1 h2
  cases h1
  rename_i a2 h1
  apply Exists.intro a2
  exact h1 h2

end a03Exercises
