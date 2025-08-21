-- # Relations
-- set_option linter.unusedVariables false

-- A relation on a type `A` is a predicate
-- of type `A → A → Prop`. That is, a relation
-- `R : A → A → Prop` considers two elements `a b : A`
-- and returns the proposition `R a b`, whenever `a` and `b`
-- are related under `R`

-- Note that, since relations are predicates on two
-- input variables we can prove that two relations are equal
-- if and only if they relate the same elements
-- (using `funext` twice) if and only if the predicates
-- are equivalent on the same elements (using `propext`)
theorem TEqRel {A : Type} {R S : A → A → Prop} : R = S ↔ ∀ (a1 a2 : A), R a1 a2 ↔ S a1 a2 := by
  apply Iff.intro
  -- R = S → ∀ (a1 a2 : A), R a1 a2 ↔ S a1 a2
  intro h a1 a2
  apply Iff.intro
  -- R a1 a2 → S a1 a2
  intro hR
  rw [h.symm]
  exact hR
  -- S a1 a2 → R a1 a2
  intro hS
  rw [h]
  exact hS
  -- (∀ (a1 a2 : A), R a1 a2 ↔ S a1 a2) → R = S
  intro h
  apply funext
  intro a1
  apply funext
  intro a2
  apply propext
  exact h a1 a2

-- ### Some interesting relations on `A`
-- The `empty` relation on `A` relates no elements at all
def empty {A : Type} : A → A → Prop := fun _ _ => False

-- The `total` relation on `A` relates all the element of `A`
def total {A : Type} : A → A → Prop := fun _ _ => True

-- The `diag` (diagonal) relation on `A`, where each
-- element is related only to itself
def diag {A : Type} : A → A → Prop := fun x y => (x = y)

namespace Relations
-- ## Types of relations
-- We introduce some interesting relations

-- **Reflexive** relation
def Reflexive {A : Type} (R : A →  A → Prop) : Prop :=
∀{a : A}, R a a

-- **Symmetric** relation
def Symmetric {A : Type} (R : A → A → Prop) : Prop :=
∀{a1 a2 : A}, R a1 a2 → R a2 a1

-- **Antisymmetric** relation
def Antisymmetric {A : Type} (R : A → A → Prop) : Prop :=
∀{a1 a2 : A}, R a1 a2 → R a2 a1 → (a1 = a2)

-- **Transitive** relation
def Transitive {A : Type} (R : A → A → Prop) : Prop :=
∀{a1 a2 a3 : A}, R a1 a2 → R a2 a3 → R a1 a3

-- **Serial** relation
def Serial {A : Type} (R : A → A → Prop) : Prop :=
∀{a1 : A}, ∃ (a2 : A), R a1 a2

-- **Euclidean** relation
def Euclidean {A : Type} (R : A → A → Prop) : Prop :=
∀{a1 a2 a3 : A}, R a1 a2 → R a1 a3 → R a2 a3

-- **Partially Functional** relation
def PartiallyFunctional {A : Type} (R : A → A → Prop) : Prop :=
∀{a1 a2 a3 : A}, R a1 a2 → R a1 a3 → a2 = a3

-- **Functional** relation
def Functional {A : Type} (R : A → A → Prop) : Prop :=
∀(a1 : A), ∃ (a2 : A), ∀(a3 : A), R a1 a3 ↔ a2 = a3

-- **Weakly Dense** relation
def WeaklyDense {A : Type} (R : A → A → Prop) : Prop :=
∀{a1 a2 : A}, (R a1 a2 → ∃ (a3 : A), (R a1 a3) ∧ (R a3 a2))

-- **Weakly Connected** relation
def WeaklyConnected {A : Type} (R : A → A → Prop) : Prop :=
∀{a1 a2 a3 : A}, R a1 a2 → R a1 a3 → ((R a2 a3) ∨ (a2 = a3) ∨ (R a3 a2))

-- **Weakly Directed** relation
def WeaklyDirected {A : Type} (R : A → A → Prop) : Prop :=
∀{a1 a2 a3 : A}, R a1 a2 → R a1 a3 →
∃ (a4 : A), ((R a2 a4) ∧ (R a3 a4))

namespace Diagonal
-- ### An example: the diagonal
-- The diagonal is reflexive
theorem TDiagRefl {A : Type} : Reflexive (@diag A) := by
  intro a
  exact rfl

-- The diagonal is symmetric
theorem TDiagSymm {A : Type} : Symmetric (@diag A) := by
  intro a1 a2 h
  exact h.symm

-- The diagonal is antisymmetric
theorem TDiagASymm {A : Type} : Antisymmetric (@diag A) := by
  intro a1 a2 h1 _
  exact h1

-- The diagonal is transitive
theorem TDiagTrans {A : Type} : Transitive (@diag A) := by
  intro a1 a2 a3 h1 h2
  exact h1.trans h2

-- The diagonal is serial
theorem TDiagSer {A : Type} : Serial (@diag A) := by
  intro a
  apply Exists.intro a
  exact rfl

-- The diagonal is Euclidean
theorem TDiagEucl {A : Type} : Euclidean (@diag A) := by
  intro a1 a2 a3 h1 h2
  exact h1.symm.trans h2

-- The diagonal is partially functional
theorem TDiagPFunc {A : Type} : PartiallyFunctional (@diag A) := by
  intro a1 a2 a3 h1 h2
  exact h1.symm.trans h2

-- The diagonal is functional
theorem TDiagFunc {A : Type} : Functional (@diag A) := by
  intro a
  apply Exists.intro a
  intro z
  apply Iff.intro
  -- diag a z → a = z
  intro h
  exact h
  -- a = z → diag a z
  intro h
  exact h

-- The diagonal is weakly dense
theorem TDiagWDense {A : Type} : WeaklyDense (@diag A) := by
  intro a1 a2 h1
  apply Exists.intro a1
  apply And.intro
  -- Left
  exact rfl
  -- Right
  exact h1

-- The diagonal is weakly connected
theorem TDiagWConn {A : Type} : WeaklyConnected (@diag A) := by
  intro a1 a2 a3 h1 h2
  exact Or.inl (h1.symm.trans h2)

-- The diagonal is weakly directed
theorem TDiagWDir {A : Type} : WeaklyDirected (@diag A) := by
  intro a1 a2 a3 h1 h2
  apply Exists.intro a1
  apply And.intro
  -- Left
  exact h1.symm
  -- Right
  exact h2.symm
end Diagonal

-- ### Exercises
namespace a08RelExercises
-- Extracted from Zach, R. (2019). Boxes and Diamonds: An Open Introduction to Modal Logic
-- https://builds.openlogicproject.org/courses/boxes-and-diamonds/bd-screen.pdf

variable (A : Type)
variable (R : A → A → Prop)

-- Reflexive implies serial
theorem TRefltoSerial : Reflexive R → Serial R := by
  intro h
  intro a
  apply Exists.intro a
  exact h

-- For a symmetric relation, transitive and Euclidean are equivalent
theorem TSymmTransIffSer (hS : Symmetric R) : Transitive R ↔ Euclidean R := by
  apply Iff.intro
  -- Transitive R → Euclidean R
  intro hT
  intro a1 a2 a3 h1 h2
  have h3 : R a2 a1 := hS h1
  exact hT h3 h2
  -- Euclidean R → Transitive R
  intro hE a1 a2 a3 h1 h2
  have h3 : R a2 a1 := hS h1
  exact hE h3 h2

-- If a relation is symmetric then it is weakly directed
theorem TSymmtoWDir : Symmetric R → WeaklyDirected R := by
  intro hS
  intro a1 a2 a3 h1 h2
  apply Exists.intro a1
  apply And.intro
  -- Left
  exact hS h1
  -- Right
  exact hS h2

-- If a relation is Euclidean and antisymmetric,
-- then it is weakly directed
theorem TEuclASymmtoWDir : Euclidean R → Antisymmetric R → WeaklyDirected R := by
  intro hE hA a1 a2 a3 h1 h2
  have h3 : R a2 a3 := hE h1 h2
  have h4 : R a3 a2 := hE h2 h1
  have h5 : a2 = a3 := hA h3 h4
  apply Exists.intro a2
  apply And.intro
  -- Left
  rw [h5.symm] at h3
  exact h3
  -- Right
  exact h4

-- If a relation is Euclidean, then it is weakly connected
theorem TEucltoWConn : Euclidean R → WeaklyConnected R := by
  intro hE a1 a2 a3 h1 h2
  apply Or.inl
  exact hE h1 h2

-- If a relation is functional, then it is serial
theorem TFunctoSer : Functional R → Serial R := by
  intro hF a
  specialize hF a
  cases hF
  rename_i Fa h
  apply Exists.intro Fa
  specialize h Fa
  rw [h]

-- If a relation is symmetric and transitive,
-- then it is Euclidean
theorem TSymmTranstoEucl : Symmetric R → Transitive R → Euclidean R := by
  intro hS hT a1 a2 a3 h1 h2
  exact hT (hS h1) h2

-- If a relation is reflexive and Euclidean,
-- then it is symmetric
theorem TReflEucltoSymm : Reflexive R → Euclidean R → Symmetric R := by
  intro hR hE a1 a2 h1
  have h2 : R a1 a1 := by exact hR
  exact hE h1 h2

-- If a relation is symmetric and Euclidean,
-- then it is transitive
theorem TSymmEucltoTrans : Symmetric R → Euclidean R → Transitive R := by
  intro hS hE a1 a2 a3 h1 h2
  exact hE (hS h1) h2

-- If a relation is serial, symmetric and transitive,
-- then it is reflexive
theorem TSerSymmTranstoRefl : Serial R → Symmetric R → Transitive R → Reflexive R := by
  intro hSe hSy hT a
  specialize @hSe a
  cases hSe
  rename_i a1 h1
  exact hT h1 (hSy h1)

end a08RelExercises
end Relations

namespace Operations
-- In this section we define operations on relations
variable (A : Type)
variable (R S : A → A → Prop)

-- Composition of two relations
def composition {A : Type} (R S : A → A → Prop) : A → A → Prop := by
  intro a1 a3
  exact ∃ (a2 : A), (R a1 a2) ∧ (S a2 a3)

-- We introduce notation for the composition (`\circ`)
notation : 65 lhs:65 " ∘ " rhs:66 => composition lhs rhs
#check R ∘ S

-- Inverse of a relation
def inverse {A : Type} (R : A → A → Prop) : A → A → Prop := by
  intro a1 a2
  exact R a2 a1

-- We introduce notation for the inverse (`^`)
notation : 65 lhs:65 "^" => inverse lhs
#check R^

-- Meet of two relations
def meet {A : Type} (R S : A → A → Prop) : A → A → Prop := by
  intro a1 a2
  exact (R a1 a2) ∧ (S a1 a2)

-- We introduce notation for the meet  (`\and`)
notation : 65 lhs:65 " ∧ " rhs:66 => meet lhs rhs
#check R ∧ S

-- Join of two relations
def join {A : Type} (R S : A → A → Prop) : A → A → Prop := by
  intro a1 a2
  exact (R a1 a2) ∨ (S a1 a2)

-- We introduce notation for the join (`\or`)
notation : 65 lhs:65 " ∨ " rhs:66 => join lhs rhs
#check R ∨ S

-- ### Exercises
namespace a08OpExercises
variable {A : Type}
variable (R S T : A → A → Prop)

-- Associativity of composition
theorem TAssComp : R ∘ (S ∘ T) = (R ∘ S) ∘ T := by
  funext a1 a2
  apply propext
  apply Iff.intro
  -- (R ∘ (S ∘ T)) a1 a2 → (R ∘ S ∘ T) a1 a2
  intro h1
  apply Exists.elim h1
  intro a3 ⟨h1, h2⟩
  apply Exists.elim h2
  intro a4 ⟨h3, h4⟩
  apply Exists.intro a4
  apply And.intro
  apply Exists.intro a3
  apply And.intro
  exact h1
  exact h3
  exact h4
  -- (R ∘ S ∘ T) a1 a2 → (R ∘ (S ∘ T)) a1 a2
  intro h1
  apply Exists.elim h1
  intro a3 ⟨h2, h3⟩
  apply Exists.elim h2
  intro a4 ⟨h4, h5⟩
  apply Exists.intro a4
  apply And.intro
  exact h4
  apply Exists.intro a3
  apply And.intro
  exact h5
  exact h3

-- The diagonal is a left neutral element for the composition
theorem TDiagL : R ∘ (@diag A) = R := by
  funext a1 a2
  apply propext
  apply Iff.intro
  -- (R ∘ diag) a1 a2 → R a1 a2
  intro h1
  apply Exists.elim h1
  intro a3 ⟨h2, h3⟩
  rw [h3.symm]
  exact h2
  -- R a1 a2 → (R ∘ diag) a1 a2
  intro h1
  apply Exists.intro a2
  apply And.intro
  exact h1
  exact rfl

-- The diagonal is a right neutral element for the composition
theorem TDiagR : (@diag A) ∘ R = R := by
  funext a1 a2
  apply propext
  apply Iff.intro
  -- (diag ∘ R) a1 a2 → R a1 a2
  intro h1
  apply Exists.elim h1
  intro a3 ⟨h2, h3⟩
  rw [h2]
  exact h3
  -- R a1 a2 → (diag ∘ R) a1 a2
  intro h1
  apply Exists.intro a1
  apply And.intro
  exact rfl
  exact h1

-- Inverse properties
-- The inverse relation of the inverse relation
-- is the original relation
theorem TInvInv : (R^)^ = R := by
  funext a1 a2
  apply propext
  apply Iff.intro
  -- (R^ ^) a1 a2 → R a1 a2
  intro h1
  exact h1
  -- R a1 a2 → (R^ ^) a1 a2
  intro h1
  exact h1

-- The inverse of the composition
theorem TInvComp : (R ∘ S)^ = (S^) ∘ (R^) := by
  funext a1 a3
  apply propext
  apply Iff.intro
  -- (R ∘ S^) a1 a2 → (S^ ∘ (R^)) a1 a2
  intro h1
  apply Exists.elim h1
  intro a2 ⟨h2, h3⟩
  apply Exists.intro a2
  apply And.intro
  exact h3
  exact h2
  -- (S^ ∘ (R^)) a1 a3 → (R ∘ S^) a1 a3
  intro h1
  apply Exists.elim h1
  intro a2 ⟨h2, h3⟩
  apply Exists.intro a2
  apply And.intro
  exact h3
  exact h2

-- The inverse of the meet
theorem TInvMeet : (R ∧ S)^ = (S^) ∧ (R^) := by
  funext a1 a2
  apply propext
  apply Iff.intro
  -- (R ∧ S)^ a1 a2 → ((S^) ∧ (R^)) a1 a2
  intro ⟨h1, h2⟩
  apply And.intro
  exact h2
  exact h1
  -- ((S^) ∧ (R^)) a1 a2 → (R ∧ S)^ a1 a2
  intro ⟨h1, h2⟩
  apply And.intro
  exact h2
  exact h1

-- The inverse of the join
theorem TInvJoin : (R ∨ S)^ = (S^) ∨ (R^) := by
  funext a1 a2
  apply propext
  apply Iff.intro
  -- (R ∨ S)^ a1 a2 → ((S)^ ∨ (R^)) a1 a2
  intro h1
  cases h1
    -- inl
  rename_i h1
  exact Or.inr h1
    -- inr
  rename_i h1
  exact Or.inl h1
  -- ((S)^ ∨ (R^)) a1 a2 → (R ∨ S)^ a1 a2
  intro h1
  cases h1
    -- inl
  rename_i h1
  exact Or.inr h1
    -- inr
  rename_i h1
  exact Or.inl h1

-- Distributivity of composition on the left over join
theorem TDisL : R ∘ (S ∨ T) = (R ∘ S) ∨ (R ∘ T) := by
  funext a1 a3
  apply propext
  apply Iff.intro
  -- (R ∘ (S ∨ T)) a1 a2 → (R ∘ S ∨ (R ∘ T)) a1 a2
  intro ⟨a2, ⟨h1,h2⟩⟩
  cases h2
    -- inl
  rename_i h2
  apply Or.inl
  apply Exists.intro a2
  exact And.intro h1 h2
    -- inr
  rename_i h2
  apply Or.inr
  apply Exists.intro a2
  exact And.intro h1 h2
  -- (R ∘ S ∨ (R ∘ T)) a1 a3 → (R ∘ (S ∨ T)) a1 a3
  intro h1
  cases h1
    -- inl
  rename_i h1
  apply Exists.elim h1
  intro a2 ⟨h2,h3⟩
  apply Exists.intro a2
  apply And.intro
  exact h2
  exact Or.inl h3
    -- inr
  rename_i h1
  apply Exists.elim h1
  intro a2 ⟨h2,h3⟩
  apply Exists.intro a2
  apply And.intro
  exact h2
  exact Or.inr h3

-- Distributivity of composition on the right over join
theorem TDisR : (R ∨ S) ∘ T = (R ∘ T) ∨ (S ∘ T) := by
  funext a1 a3
  apply propext
  apply Iff.intro
  -- (R ∨ S ∘ T) a1 a3 → (R ∘ T ∨ (S ∘ T)) a1 a3
  intro h1
  apply Exists.elim h1
  intro a2 ⟨h2, h3⟩
  cases h2
    -- inl
  rename_i h2
  apply Or.inl
  apply Exists.intro a2
  exact And.intro h2 h3
    -- inr
  rename_i h2
  apply Or.inr
  apply Exists.intro a2
  exact And.intro h2 h3
  -- (R ∘ T ∨ (S ∘ T)) a1 a3 → (R ∨ S ∘ T) a1 a3
  intro h1
  cases h1
    -- inl
  rename_i h1
  apply Exists.elim h1
  intro a2 ⟨h2, h3⟩
  apply Exists.intro a2
  apply And.intro
  exact Or.inl h2
  exact h3
    -- inr
  rename_i h1
  apply Exists.elim h1
  intro a2 ⟨h2, h3⟩
  apply Exists.intro a2
  apply And.intro
  exact Or.inr h2
  exact h3

-- Empty is a left zero for the composition
theorem TEmptLZ : (@empty A) ∘ R = (@empty A) := by
  funext a1 a2
  apply propext
  apply Iff.intro
  -- (empty ∘ R) a1 a2 → empty a1 a2
  intro h1
  apply Exists.elim h1
  intro a3 ⟨h2, _⟩
  exact False.elim h2
  -- empty a1 a2 → (empty ∘ R) a1 a2
  intro h1
  exact False.elim h1

-- Empty is a right zero for the composition
theorem TEmptRZ : R ∘ (@empty A) = (@empty A) := by
  funext a1 a2
  apply propext
  apply Iff.intro
  -- (R ∘ empty) a1 a2 → empty a1 a2
  intro h1
  apply Exists.elim h1
  intro a3 ⟨_, h3⟩
  exact False.elim h3
  -- empty a1 a2 → (R ∘ empty) a1 a2
  intro h1
  exact False.elim h1

end a08OpExercises
end Operations
