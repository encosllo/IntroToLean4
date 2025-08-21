import a05Functions
open Inj
open Surj

namespace Empty
-- ## Empty type
-- The empty type is a type that has no values
-- It is denoted by `Empty` in Lean
#check Empty
#print Empty

-- This means that if we have a value of type `Empty`,
-- we can use it to construct a value of any other type
def emptyToAny {A : Type} : Empty → A := by
  intro x
  exact Empty.elim x

-- The interesting thing about the `emptytoAny` function
-- is that it is unique up to definitional equality
theorem emptyToAnyUnique {A : Type} {f g : Empty → A} : f = g := by
  funext x
  exact Empty.elim x

-- This implies that the `emptyToAny` function with codomain `Empty`, is
-- in particular, the identity function on `Empty`
theorem emptyToAnyId : @emptyToAny Empty = id := by
  funext x
  exact Empty.elim x

-- All the elements of `Empty` are equal
theorem emptyUnique : ∀ (x y : Empty), x = y := by
  intro x _
  exact Empty.elim x

-- The `emptyToAny` function is injective
theorem emptyToAnyInj {A : Type} : injective (@emptyToAny A) := by
  intro x _ _
  exact Empty.elim x

-- Under `Classical.choice`, if the `emptyToAny` function is surjective,
-- the codomain cannot be `nonempty`
theorem emptyToAnySurj {A : Type} : surjective (@emptyToAny A) ↔ ¬ (Nonempty A)  := by
  apply Iff.intro
  -- surjective emptyToAny → ¬ Nonempty A
  intro h1 h2
  have a : A := Classical.choice h2
  have h3 : ∃ (x : Empty), emptyToAny x = a := by
    exact h1
  apply Exists.elim h3
  intro z _
  exact Empty.elim z
  -- ¬ Nonempty A → surjective emptyToAny
  intro h1 a
  have h2 : Nonempty A := Nonempty.intro a
  apply False.elim (h1 h2)
end Empty

namespace Unit
-- ## Unit type
-- The unit type is a type that has exactly one value
-- It is denoted by `Unit` in Lean
#check Unit
#print Unit

-- The unit type has one value, denoted by `()`
#check ()

-- There is always a function from any type to the unit type
def anyToUnit {A : Type} : A → Unit := by
  intro _
  exact ()

-- The `anyToUnit` function is unique up to definitional equality
theorem anyToUnitUnique {A : Type} {f g : A → Unit} : f = g := by
  funext x
  exact rfl

-- This implies that the `anyToUnit` function with codomain `Unit`, is
-- in particular, the identity function on `Unit`
theorem anyToUnitId : @anyToUnit Unit = id := by
  funext x
  exact rfl

-- All the elements of `Unit` are equal
theorem unitUnique : ∀ (x y : Unit), x = y := by
  intro x _
  exact rfl

-- The `anyToUnit` function is injective if,
-- and only if, the domain has only one element
theorem anyToUnitInj {A : Type} : injective (@anyToUnit A) ↔ (∀ (a1 a2 : A), a1 = a2) := by
  apply Iff.intro
  -- injective anyToUnit → ∀ (a1 a2 : A), a1 = a2
  intro h1 a1 a2
  have h2 : anyToUnit a1 = anyToUnit a2 := by
    exact rfl
  exact h1 h2
  -- ∀ (a1 a2 : A), a1 = a2 → injective anyToUnit
  intro h1 x y _
  exact h1 x y

-- Under `Classical.choice`, the `anyToUnit` function is
-- surjective if and only if the domain is `Nonempty`
theorem anyToUnitSurj {A : Type} : surjective (@anyToUnit A) ↔ Nonempty A := by
  apply Iff.intro
  -- surjective anyToUnit → Nonempty A
  intro h1
  have h2 : ∃ (a : A), anyToUnit a = () := by
    exact h1
  apply Exists.elim h2
  intro a _
  exact Nonempty.intro a
  -- Nonempty A → surjective anyToUnit
  intro h1
  intro a
  apply Exists.intro (Classical.choice h1)
  exact rfl

end Unit
