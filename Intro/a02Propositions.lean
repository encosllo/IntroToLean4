-- # Propositions
-- `Prop` is the type of all propositions in Lean
-- This is a built-in concept
#check Prop
-- #print Prop -- Returns error

-- Propositions are statements that express a definite claim
-- Examples of propositions are
#check 2 + 2 = 4
#check 3 < 1

-- In Lean, a proposition is a type that represents a
-- logical statement. Thus, propositions are itself types
variable (P : Prop)
variable (h : P)
-- We need to understand `h` as a proof of `P`
#check h

-- A proposition is considered true if and only if there
-- exists a term of its type. In other words, if you can
-- construct a term `h : P`, then `P` is true.
-- If no such term exists, then `P` is false.

-- ## First theorem
-- To enter the interactive proof mode, we indent the text
theorem Th1 (h : P) : P := by
  exact h

-- `Th1` has type `∀ (P : Prop), P → P`
#check Th1
-- `Th1 P` has type `P → P`
#check Th1 P
-- `Th1 P h` has type `P`
#check Th1 P h

-- `Th1` adapts to the input type
variable (Q : Prop)
-- `Th1 Q` has type `Q → Q`
#check Th1 Q

-- Lean automatically generalizes our original
-- definition of `Th1` to its most general form
#print Th1

-- Second theorem with implicit variables
theorem Th2 {P : Prop} (h : P) : P := by
  exact h

-- `Th2` has type `∀ {P : Prop}, P → P`
#check Th2
-- `Th2 h` has type `P`
#check Th2 h

-- Third theorem applying a previous theorem
theorem Th3 {P : Prop} (h : P) : P := by
  apply Th2
  exact h

-- Fourth theorem using `have` to get an intermediate result
theorem Th4 {P : Prop} (h : P) : P := by
  have h2 : P := by
    exact h
  exact h2

-- We can ask Lean which theorem to `apply`
theorem Th5 {P : Prop} (h : P) : P := by
  apply?
-- or which `exact` result is needed
theorem Th6 {P : Prop} (h : P) : P := by
  exact?

-- ### First example
-- Examples are anonymous theorems
example (a : P) : P := by
  exact a

-- ### Sorry
-- `sorry` allows you to temporarily
-- skip the proof of a theorem or definition
/- The following theorem uses `sorry`
  theorem Th7 (h : P) : P := by
    sorry
-/

-- ## Logical Connectives

-- ### Conjunction (∧): Logical And
#check And P Q
#check P ∧ Q

#print And

-- To prove a proposition of the form `P ∧ Q`
-- we need a proof of `P` and a proof of `Q`
theorem ThAndIn (hP : P) (hQ : Q) : P ∧ Q := by
  exact And.intro hP hQ

-- From a proof of `P ∧ Q`, we can obtain a proof of `P`
theorem ThAndOutl (h : P ∧ Q) : P := by
  exact h.left
-- We can also obtain a proof for `Q`
theorem ThAndOutr (h : P ∧ Q) : Q := by
  exact h.right

-- ### Disjunction (∨): Logical Or
#check Or P Q
#check P ∨ Q

#print Or

-- From a proof of `P`, we can obtain a proof of `P ∨ Q`
theorem ThOrInl (h : P) : P ∨ Q := by
  exact Or.inl h
-- From a proof of `Q`, we can obtain a proof of `P ∨ Q`
theorem ThOrInr (h : Q) : P ∨ Q := by
  exact Or.inr h

-- Inductive types allow us to prove by `cases`
-- From a proof of `P ∨ Q`, we can obtain a proof of `Q ∨ P`
theorem ThOrCases (h : P ∨ Q) : Q ∨ P := by
  cases h
  -- Case 1
  rename_i hP
  exact Or.inr hP
  -- Case 2
  rename_i hQ
  exact Or.inl hQ

-- We can alternatively use the keyword `Or.elim`
theorem ThOrCases2 (h : P ∨ Q) : Q ∨ P := by
  apply Or.elim h
  -- Case P
  intro hP
  exact Or.inr hP
  -- Case Q
  intro hQ
  exact Or.inl hQ

-- ### Implication
#check P → Q

-- From a proof of `Q`, we can obtain a proof of `P → Q`
theorem ThImpIn (hQ : Q) : P → Q := by
  intro _ -- No need to name the hypothesis
  exact hQ

-- From a proof `P → Q` and a proof of `P`,
-- we can obtain a proof of `Q`
theorem ThModusPonens (h : P → Q) (hP : P) : Q := by
  exact h hP

-- ### Double implication
#check Iff P Q
#check P ↔ Q

#print Iff

-- `P ↔ Q` is a shorthand for `(P → Q) ∧ (Q → P)`
-- From `P ↔ Q` we can derive `(P → Q) ∧ (Q → P)`
theorem ThIffOut (h : P ↔ Q) : (P → Q) ∧ (Q → P) := by
  apply And.intro
  -- Left
  exact h.mp
  -- Right
  exact h.mpr
-- From `(P → Q)` and `(Q → P)` we can derive `P ↔ Q`
theorem ThIffIn (h1 : P → Q) (h2 : Q → P) : P ↔ Q := by
  exact Iff.intro h1 h2

-- ### True
#check True
#print True

-- `True` can always be obtained
theorem ThTrueIn : True := by
  exact True.intro

-- An alternative way to obtain a
-- proof of `True` is to write `trivial`
#check trivial

-- `Trivial` is an element of type `True`
theorem ThTrivial : True := by
  exact trivial

-- ### False
#check False
#print False

-- Having an element of type `False`
-- leads to a contradiction.
-- Having `False` implies any other proposition
-- False implies any proposition
theorem ThExFalso : False → P := by
  intro h
  exact False.elim h

-- ### Negation
#check Not P
#check ¬P

#print Not

-- `¬P` is defined as `P → False`
-- In order to prove `¬P`, we must assume `P`
-- and obtain a contradiction
theorem ThModusTollens (h1 : P → Q) (h2 : ¬Q) : ¬P := by
  -- Assume P is true (to prove ¬P, which is P → False).
  intro h3
  -- Derive Q from P → Q and P.
  have h4 : Q := by
    exact h1 h3
  -- Use ¬Q (Q → False) and Q to derive False.
  exact h2 h4

-- ## Decidable propositions
-- A proposition is `decidable` if we can
-- constructively determine whether it
-- is true or false
#check Decidable
#print Decidable

-- True is decidable
def DecidableTrue : Decidable True := by
  exact isTrue trivial

-- False is decidable
def DecidableFalse : Decidable False := by
  exact isFalse id

-- If `P` is decidable, then `¬ P` is decidable
def DecidableNot {P : Prop} : Decidable P → Decidable (¬ P) := by
  intro hP
  match hP with
    | isFalse hP => exact isTrue  (fun h => False.elim (hP h))
    | isTrue hP  => exact isFalse (fun h => False.elim (h hP))

-- If `P` and `Q` are decidable, then `P ∧ Q` is decidable
def DecidableAnd {P Q : Prop} : Decidable P → Decidable Q → Decidable (P ∧ Q) := by
  intro hP hQ
  match hP, hQ with
    | isFalse hP, _           => exact isFalse (fun h => hP h.left)
    | _         , isFalse hQ  => exact isFalse (fun h => hQ h.right)
    | isTrue hP , isTrue hQ   => exact isTrue (And.intro hP hQ)

-- If `P` and `Q` are decidable, then `P ∨ Q` is decidable
def DecidableOr {P Q : Prop} : Decidable P → Decidable Q → Decidable (P ∨ Q) := by
  intro hP hQ
  match hP, hQ with
    | isTrue hP , _            => exact isTrue (Or.inl hP)
    | _         , isTrue hQ    => exact isTrue (Or.inr hQ)
    | isFalse hP, isFalse hQ   => exact isFalse (fun h => h.elim hP hQ)

-- If `P` and `Q` are decidable, then `P → Q` is decidable
def DecidableImplies {P Q : Prop} : Decidable P → Decidable Q → Decidable (P → Q) := by
  intro hP hQ
  match hP, hQ with
    | isFalse hP , _          => exact isTrue  (fun h => False.elim (hP h))
    | _          , isTrue hQ  => exact isTrue  (fun _ => hQ)
    | isTrue hP  , isFalse hQ => exact isFalse (fun h => hQ (h hP))

-- If `P` and `Q` are decidable, then `P ↔ Q` is decidable
def DecidableIff {P Q : Prop} : Decidable P → Decidable Q → Decidable (P ↔ Q) := by
  intro hP hQ
  have hPtoQ : Decidable (P → Q) := DecidableImplies hP hQ
  have hQtoP : Decidable (Q → P) := DecidableImplies hQ hP
  match hPtoQ, hQtoP with
    | isFalse hPtoQ, _ => exact isFalse (fun h => hPtoQ h.mp)
    | _, isFalse hQtoP => exact isFalse (fun h => hQtoP h.mpr)
    | isTrue  hPtoQ, isTrue  hQtoP => exact isTrue (Iff.intro hPtoQ hQtoP)

-- ## Classical Logic
-- We open the `Classical` namespace
open Classical
-- We use `Classical.em` to prove the excluded middle
theorem ThExcludedMiddle : P ∨ ¬P := by
  exact em P

-- Classical Logic allows proofs by contradiction
theorem ThDoubNeg : P ↔ ¬¬P := by
  apply Iff.intro
  -- Implication P → ¬¬P
  intro hP
  intro hNP
  exact hNP hP
  -- Implication ¬¬P → P
  intro hNNP
  have hF : ¬ P → False := by
    intro hNP
    exact hNNP hNP
  apply byContradiction hF

-- Exercises extracted from Daniel Clemente webpage
-- EN https://www.danielclemente.com/logica/dn.en.pdf
namespace a02Exercises
variable (A B C D I L M P Q R : Prop)

theorem T51 (h1 : P) (h2 : P → Q) : P ∧ Q := by
  apply And.intro
  exact h1
  exact h2 h1

theorem T52 (h1 : P ∧ Q → R) (h2 : Q → P) (h3: Q) : R := by
  have h4 : P ∧ Q := by
    apply And.intro
    exact h2 h3
    exact h3
  exact h1 h4

theorem T53 (h1 : P → Q) (h2 : Q → R) : P → (Q ∧ R) := by
  intro h
  apply And.intro
  exact h1 h
  exact h2 (h1 h)

theorem T54 (h1 : P) : Q → P := by
  intro _
  exact h1

theorem T55 (h1 : P → Q) (h2 : ¬Q) : ¬P := by
  intro h3
  exact h2 (h1 h3)

theorem T56 (h1 : P → (Q → R)) : Q → (P → R) := by
  intro hQ hP
  exact h1 hP hQ

theorem T57 (h1 : P ∨ (Q ∧ R)) : P ∨ Q := by
  cases h1
  -- inl
  rename_i hP
  exact Or.inl hP
  -- inr
  rename_i hQR
  exact Or.inr hQR.left

theorem T58 (h1 : (L ∧ M) → ¬P) (h2 : I → P) (h3 : M) (h4 : I) : ¬L := by
  intro h5
  have h6 : L ∧ M := by
    exact And.intro h5 h3
  have h7 : ¬P := by exact h1 h6
  have h8 : P := by exact h2 h4
  exact h7 h8

theorem T59 : P → P := by
  intro h
  exact h

theorem T510 : ¬ (P ∧ ¬P) := by
  intro h
  exact h.right h.left

theorem T511 : P ∨ ¬P := by
  exact em P

theorem T512 (h1 : P ∨ Q) (h2 : ¬P) : Q := by
  cases h1
  -- inl
  rename_i h1
  exact False.elim (h2 h1)
  -- inr
  rename_i h1
  exact h1

theorem T513 (h1 : A ∨ B) (h2 : A → C) (h3 : ¬D → ¬B) : C ∨ D := by
  cases h1
  -- inl
  rename_i h1
  exact Or.inl (h2 h1)
  -- inr
  rename_i h1
  have h4 : D ∨ ¬D := by exact em D
  cases h4
  -- inl
  rename_i h4
  exact Or.inr h4
  -- inr
  rename_i h4
  apply False.elim
  exact h3 h4 h1

theorem T514 (h1 : A ↔ B) : (A ∧ B) ∨ (¬A ∧ ¬B) := by
  rw [h1]
  simp
  exact em B

end a02Exercises
