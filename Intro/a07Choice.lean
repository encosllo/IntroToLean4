-- # Choice
import a05Functions

-- ## Inhabited
-- `Inhabited α` is a typeclass that says that `α`
--  has a designated element, called `(default : α)`
-- This is sometimes referred to as a "pointed type".
#print Inhabited

-- A typeclass in Lean is a special kind of structure that
-- specifies a set of properties or operations that a type
-- can have. We will learn more about

-- To define an specific example of a class we will use the
-- `instance` or `def` keywords. For the typeclass
-- `Inhabited` we only need to provide the default element
instance InBool : Inhabited Bool := {
  default:= true
  }

#check InBool
#print InBool
#eval InBool.default

-- Lean already has some instances of inhabited types
#print instInhabitedBool -- default := false
#print instInhabitedProp -- default := True
#print instInhabitedNat  -- default := Nat.zero

-- ## Nonempty
-- The `Nonempty` type is an inductive proposition
-- that asserts the existence of at least one element
-- in a given type
#print Nonempty

-- For example, we can provide a proof of `Nonempty Bool`
theorem TNEBool : Nonempty Bool := Nonempty.intro true

-- ### Inhabited implies Nonempty
-- We have a straightforward implication,
-- if a type is inhabited, then it is also nonempty
def InhabitedToNonempty {A : Type} : Inhabited A → Nonempty A := by
  intro h
  exact Nonempty.intro h.default

-- The reverse implication, `Nonempty A → Inhabited A`,
-- does not always hold in constructive logic
-- A proof of `Nonempty A` only asserts the existence of
-- an element without providing a specific one, whereas
-- `Inhabited A` requires a concrete, predefined
-- default value

-- ## Classical.choice
-- In classical logic, we can recover `Inhabited A`
-- from `Nonempty A` using the axiom of choice
-- (`Classical.choice`), but this is noncomputable,
-- meaning we cannot explicitly construct the
-- default element
#print Classical.choice

-- `Classical.choice` is an axiom
-- Many axioms, such as `Classical.choice`, are
-- nonconstructive in nature, meaning they assert
-- the existence of certain objects without providing
-- explicit constructions
-- As a result, these axioms are often `noncomputable`

-- ### Nonempty implies Inhabited in Classical Logic
-- We can now define the reverse implication
-- in Classical Logic
noncomputable def NonemptyToInhabited {A : Type} : Nonempty A → Inhabited A := by
  intro h
  have a : A := Classical.choice h
  exact Inhabited.mk a

-- The function above is marked as `noncomputable`
-- because the choice of an element is nonconstructive

-- ### Classical.choose
-- The command `Classical.choose` is a function from
-- classical logic that allows for the selection of an
-- element satisfying a given predicate
#check Classical.choose
-- The command `Classical.choose_spec` guarantees that
-- the extracted element satisfies the given predicate
#check Classical.choose_spec

-- Alternative commands are
#check Exists.choose
#check Exists.choose_spec

-- We prove that `Nonempty A ↔ ∃ (a : A), a = a`
theorem TInj {A : Type} : Nonempty A ↔ ∃ (a : A), a = a := by
  apply Iff.intro
  -- Nonempty A → ∃ a, a = a
  intro h
  apply Exists.intro (Classical.choice h)
  exact rfl
  -- (∃ a, a = a) → Nonempty A
  intro h
  have a : A := Exists.choose h
  exact Nonempty.intro a

-- ## Exercises
namespace a06Exercises
open Inj
open Surj
open Bij
open a05BijExercises
-- Under `Classical.Choice`, if a function is injective and
-- the domain is `Nonempty` then the function has a left inverse
theorem TInjtoHasLeftInv {A B : Type} {f : A → B} : injective f → Nonempty A → hasleftinv f := by
  intro h1 h2
  let g : B → A := by
    intro b
    by_cases h3 : ∃ (a : A), f a = b
    --
    exact Exists.choose h3 -- The alternative h3.choose is also valid
    --
    exact Classical.choice h2
  apply Exists.intro g
  funext a
  have h3 : ∃ (a' : A), f a' = f a := by
    apply Exists.intro a
    exact rfl
  have h4 : f (Exists.choose h3) = f a := Exists.choose_spec h3
  calc
    (g ∘ f) a = g (f a)           := by exact rfl
    _         = Exists.choose h3  := by exact dif_pos h3
    _         = a                 := by exact h1 h4
    _         = id a              := by exact rfl

-- Under `Classical.Choice`, every surjective function
-- has a right inverse
noncomputable def Inverse {A B : Type} (f : A → B) (h : surjective f) : B → A := by
  intro b
  specialize @h b
  exact Exists.choose h

-- Under `Classical.Choice`, the inverse of a surjective
-- function is a right inverse
theorem InvR {A B : Type} (f : A → B) (h : surjective f) :  f ∘ (Inverse f h) = id := by
  funext b
  specialize @h b
  exact Exists.choose_spec h

-- Under `Classical.Choice`, every surjective function has a right inverse
theorem TSurjtoHasRightInv {A B : Type} {f : A → B} : surjective f → hasrightinv f := by
  intro h
  apply Exists.intro (Inverse f h)
  exact InvR f h

-- Under `Classical.Choice`, the inverse of a bijective function is a left inverse
theorem InvL {A B : Type} (f : A → B) (h : bijective f) : (Inverse f h.right) ∘ f = id := by
  funext a
  have hs : surjective f := h.right
  specialize @hs (f a)
  exact h.left (Exists.choose_spec hs)

-- Under `Classical.Choice` bijective and isomorphism are
-- equivalent concepts
theorem TCarBijIso {A B : Type} {f : A → B} : bijective f ↔ isomorphism f := by
  apply Iff.intro
  -- bijective f → isomorphism f
  intro h
  apply Exists.intro (Inverse f h.right)
  apply And.intro
  exact InvL f h
  exact InvR f h.right
  -- isomorphism f → bijective f
  exact TCarIsotoBij

end a06Exercises
