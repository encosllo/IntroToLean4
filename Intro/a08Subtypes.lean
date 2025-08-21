-- # Subtypes
import a03Quantifiers
import a05Functions
open Inj Surj Bij
-- set_option linter.unusedVariables false

-- We define variables `A : Type` and
-- `P : A → Prop`, a predicate on `A`
variable (A : Type)
variable (P : A → Prop)
-- With this information we can obtain `Subtype P`
-- the subtype of all the elements of type `A`
-- that satisfy `P`
#check Subtype P
-- An alternative notation is
#check { a : A // P a }

#print Subtype

-- ### Examples of Subtypes (from a03Quantifiers)
-- #### The False Subtype
def SFalse {A : Type} := { a : A // PFalse a}

-- #### The True Subtype
def STrue {A : Type} := { a : A // PTrue a}

-- ## The Image Subtype
def Im {A B : Type} (f : A → B) : Type := { b : B // ∃ (a : A), f a = b}

-- ## Elements of a Subtype type
-- To create an element of a `Subtype P`, we use
-- the `Subtype.mk a` function, which maps an element `a : A`
-- and a proof of `P a` to an element of type `Subtype P`
variable (a : A)
variable (h : P a)
#check Subtype.mk a h

-- Two elements of type `Subtype P` are equal
-- if and only if the corresponding values in `A` are equal
#check Subtype.eq     -- `a1.val = a2.val → a1 = a2`
#check Subtype.eq_iff -- `a1.val = a2.val ↔ a1 = a2`

-- ### The inclusion function
-- The inclusion function
def inc {A : Type} {P : A → Prop} : Subtype P → A := by
  intro a
  exact a.val

-- The inclusion function is injective
theorem Tincinj {A : Type} {P : A → Prop} : injective (@inc A P) := by
  intro a1 a2 h1
  exact Subtype.eq h1

-- ## Restriction
-- The restriction of a function
def rest {A B : Type} {P : A → Prop} (f : A → B) : Subtype P → B := by
  intro a
  exact f a.val

-- ## Correstriction
-- Correstriction of a function
def correst {A B : Type} {Q : B → Prop} (f : A → B) (h : ∀ (b : Im f), Q b.val) : A → Subtype Q := by
  intro a
  have ha : ∃ (a1 : A), f a1 = f a := by
    apply Exists.intro a
    exact rfl
  apply Subtype.mk (f a) (h ⟨f a, ha⟩)

-- ## Birrestriction
-- Birrestriction of a function `birrest = correst ∘ rest`
def birrest {A B : Type} {P : A → Prop} {Q : B → Prop} (f : A → B) (h : ∀ (a : A), P a → Q (f a)) : Subtype P → Subtype Q := by
  apply correst (rest f)
  intro ⟨b, ⟨a, ha⟩⟩
  simp
  specialize h a.val
  have hb : f a.val = b := ha
  rw [hb] at h
  exact h a.property

-- In particular, if a predicate `P1` on `A` implies a predicate
-- `P2` on `A` then there exists a way of transforming elements
-- of type `Subtype P1` into elements of `Subtype P2`
-- For this we simply birrestrict the identity
def SubtoSub {A : Type} {P1 P2 : A → Prop} (h : ∀ (a : A), P1 a → P2 a) : Subtype P1 → Subtype P2 := birrest id h

namespace a08Exercises
-- If two predicates are equivalent, then the
-- corresponding subtypes are equal
theorem TEqSubtype {A : Type} {P1 P2 : A → Prop} (h : ∀ (a : A), P1 a ↔ P2 a) : Subtype P1 = Subtype P2 := by
  have h1 : P1 = P2 := by
    funext a
    apply propext
    exact h a
  rw [h1]

-- Universal property of subtypes
-- Im (inc) = Subtype
theorem TUPSub {A : Type} {P : A → Prop} : Im (@inc A P) = Subtype P := by
  apply TEqSubtype
  intro a1
  apply Iff.intro
  -- (∃ a, inc a = a1) → P a1
  intro h1
  apply Exists.elim h1
  intro a2 h2
  rw [h2.symm]
  apply Subtype.property
  -- P a1 → ∃ a, inc a = a1
  intro h1
  apply Exists.intro (Subtype.mk a1 h1)
  exact rfl

-- Restriction `rest f = f ∘ inc`
theorem TRest {A B : Type} {f : A → B} {P : A → Prop}: (@rest A B P f) = f ∘ (@inc A P) := by
  exact rfl

-- Universal property of the correstriction
-- `f = inc ∘ correst`
theorem TUPCorrest {A B : Type} {Q : B → Prop} {f : A → B} (h : ∀ (b : Im f), Q b.val) : f = (@inc B Q) ∘ (correst f h) := by
  exact rfl

-- Unicity
theorem TUPCorrestUn {A B : Type} {Q : B → Prop} {f : A → B} (h : ∀ (b : Im f), Q b.val) (g : A → Subtype Q) (h1 : f = (@inc B Q) ∘ g) : (correst f h) = g := by
  apply funext
  intro a
  apply Subtype.eq
  calc
    (correst f h a).val = ((@inc B Q) ∘ (correst f h)) a := by exact rfl
    _                   = f a                            := by exact congrFun (TUPCorrest h) a
    _                   = ((@inc B Q) ∘ g) a             := by exact congrFun h1 a
    _                   = (g a).val                      := by exact rfl
end a08Exercises

namespace Equalizers
-- ## Equalizers
-- The equalizer of two functions `f g : A → B`
-- is the type of elements `a : A` such that `f a = g a`
-- It is a subtype of `A`
def Eq {A B : Type} (f g : A → B) : Type := { a : A // f a = g a}

-- The inclusion function from the equalizer to `A`
def incEq {A B : Type} (f g : A → B) : Eq f g → A := @inc A (fun a => f a = g a)

-- The inclusion function satisfies that `f ∘ (incEq f g) = g ∘ (incEq f g)`
theorem TEqInc {A B : Type} (f g : A → B) : f ∘ (incEq f g) = g ∘ (incEq f g) := by
  apply funext
  intro a
  calc
    (f ∘ (incEq f g)) a = f a.val             := rfl
    _                   = g a.val             := a.property
    _                   = (g ∘ (incEq f g)) a := rfl

-- Universal property of the equalizer
-- If there is another function `h : C → A` satisfying
-- `f ∘ h = g ∘ h`, then there exists a function `u : C → Eq f g`
def u {A B C : Type} {f g : A → B} {h : C → A} (h1 : f ∘ h = g ∘ h) : C → Eq f g := by
  intro c
  exact Subtype.mk (h c) (congrFun h1 c)

-- The function `u` satisfies that `incEq f g ∘ u = h`
theorem TEqIncEq {A B C : Type} {f g : A → B} {h : C → A} (h1 : f ∘ h = g ∘ h) : (incEq f g) ∘ (u h1) = h := by
  apply funext
  intro c
  exact rfl

-- The function `u` is unique in the sense that if there is another function
-- `v : C → Eq f g` satisfying `incEq f g ∘ v = h`, then `v = u`
theorem TEqUni {A B C : Type} {f g : A → B} {h : C → A} (h1 : f ∘ h = g ∘ h) (v : C → Eq f g) (h2 : (incEq f g) ∘ v = h) : v = u h1 := by
  apply funext
  intro c
  apply Subtype.eq
  calc
    (v c).val = ((incEq f g) ∘ v) c := rfl
    _         = h c                 := congrFun h2 c
    _         = (u h1 c).val        := rfl


namespace a08ExercisesEq
-- The function `incEq` is a monomorphism
theorem TincEqMono {A B : Type} {f g : A → B} : monomorphism (incEq f g) := by
  intro C v1 v2 h1
  apply funext
  intro a
  apply Subtype.eq
  calc
    (v1 a).val  = (incEq f g ∘ v1) a  := rfl
    _           = (incEq f g ∘ v2) a  := congrFun h1 a
    _           = (v2 a).val          := rfl


-- An epic `incEq` is an isomorphism
theorem TincEqEpi {A B : Type} {f g : A → B} : epimorphism (incEq f g) → isomorphism (incEq f g) := by
  intro h1
  have h2 : f = g := by
    apply @h1 B f g
    exact TEqInc f g
  let fu : A → Eq f g := by
    apply @u A B A f g id
    exact h2
  apply Exists.intro fu
  apply And.intro
  -- fu ∘ incEq f g = id
  funext a
  apply Subtype.eq
  exact rfl
  -- incEq f g ∘ fu = id
  apply TEqIncEq

end a08ExercisesEq

end Equalizers
