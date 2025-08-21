-- # Functions
-- Declare foue arbitrary types `A`, `B`, `C` and `D`
variable (A B C D : Type)

-- Check the type `A → B` of all functions from `A` to `B`
-- `A` is the domain and `B` the codomain
#check A → B

-- Declare a mapping `f`
variable (f : A → B)

-- Declare an element `a` of type `A`
variable (a : A)

-- Apply the function `f` to `a`
-- This is an element of type `B`
#check f a

-- ## Equality
-- Two functions `f, g : A → B` are equal if and only if
-- they produce the same output for every input,
-- meaning that for all `a : A`, we have `f a = g a`
theorem TEqApl : f = g ↔ ∀ (a : A), f a = g a := by
  apply Iff.intro
  -- f = g → ∀ (a : A), f a = g a
  intro h a
  exact congrFun h a
  -- (∀ (a : A), f a = g a) → f = g
  intro h
  exact funext h

-- ## Composition
-- If `f : A → B` and `g : B → C` are functions,
-- then its composition, written `g ∘ f` is an
-- element of type `A → C`
variable (g : B → C)
#check g ∘ f

-- Composition of functions is associative
theorem TCompAss {f : A → B} {g : B → C} {h : C → D} :
h ∘ (g ∘ f) = (h ∘ g) ∘ f := by
  funext a
  exact rfl

-- ## The identity function
#print id
-- We can disable the automatic insertion of implicit
-- parameters by using `@`
#check @id A

-- The identity function is a neutral element
-- for composition, both on the left and on the right
theorem TIdNeutral : (f ∘ id = f) ∧ (id ∘ f = f) := by
  apply And.intro
  -- f ∘ id = f
  funext a
  exact rfl
  -- id ∘ f = f
  funext a
  exact rfl

namespace Inj
-- Definition of injective function
def injective {A B : Type} (f : A → B) : Prop :=
∀{a1 a2 : A}, (f a1 = f a2) → (a1 = a2)

-- Definition of monomorphism
def monomorphism {A B : Type} (f : A → B) : Prop :=
∀{C : Type}, ∀{g h : C → A}, f∘g = f∘h → g = h

-- Left inverse
def hasleftinv {A B : Type} (f : A → B) : Prop :=
∃ (g : B → A), g∘f = id

-- The identity is injective
theorem TIdInj : injective (@id A) := by
  -- rw [injective] -- rw to recover the definition
  intro a1 a2 h
  calc
    a1 = id a1 := by exact rfl
    _  = id a2 := by exact h
    _  = a2    := by exact rfl

-- The identity is a monomorphism
theorem TIdMon : monomorphism (@id A) := by
  -- rw [monomorphism] -- rw to recover the definition
  intro C g h h1
  calc
    g = id ∘ g := by exact rfl
    _ = id ∘ h := by exact h1
    _ = h      := by exact rfl

-- The identity has a left inverse
theorem TIdHasLeftInv : hasleftinv (@id A) := by
  -- rw [hasleftinv] -- rw to recover the definition
  apply Exists.intro id
  exact rfl

-- ## Exercises
namespace a05InjExercises
-- Negation of injective
theorem TNegInj {A B : Type} {f: A → B} : ¬ (injective f) ↔ ∃ (a1 a2 : A),
f a1 = f a2 ∧ a1 ≠ a2 := by
  -- sorry
  apply Iff.intro
  -- ¬injective f → ∃ a1 a2, f a1 = f a2 ∧ a1 ≠ a2
  intro h1
  rw [injective] at h1
  false_or_by_contra
  rename_i h2
  have h3 : ∀ {a1 a2 : A}, f a1 = f a2 → a1 = a2 := by
    intro a1 a2 h3
    false_or_by_contra
    rename_i h4
    have h5 : ∃ (a1 a2 : A), f a1 = f a2 ∧ a1 ≠ a2 := by
      apply Exists.intro a1
      apply Exists.intro a2
      apply And.intro
      exact h3
      exact h4
    exact h2 h5
  exact h1 h3
  -- (∃ a1 a2, f a1 = f a2 ∧ a1 ≠ a2) → ¬injective f
  intro h1
  cases h1
  rename_i a1 h1
  cases h1
  rename_i a2 h1
  intro h
  rw [injective] at h
  specialize h h1.left
  exact h1.right h

-- The composition of injective functions is injective
theorem TCompInj {A B : Type} {f : A → B} {g : B → C} (h1 : injective f) (h2 : injective g) :
injective (g∘f) := by
  -- sorry
  intro a1 a2 h3
  specialize h2 h3
  exact h1 h2

-- If the composition (g∘f) is injective, then f is injective
theorem TCompRInj {A B : Type} {f : A → B} {g : B → C} (h1: injective (g∘f)) : (injective f) := by
  intro a1 a2 h
  have h2 : g (f a1) = g (f a2) := by
    exact congrArg g h
  exact h1 h2

-- Injective and Monomorphisms are equivalent concepts
theorem TCarMonoInj {A B : Type} {f : A → B} : injective f ↔ monomorphism f := by
  apply Iff.intro
  -- injective f → monomorphism f
  intro h1
  intro C g h h2
  funext c
  have h3 : f (g c) = f (h c) := by
    calc
      f (g c) = (f ∘ g) c := by exact rfl
      _       = (f ∘ h) c := by exact congrFun h2 c
      _       = f (h c)   := by exact rfl
  exact h1 h3
  -- monomorphism f → injective f
  intro h1
  intro a1 a2 h2
  rw [monomorphism] at *
  let g : Bool → A := by
    intro _
    exact a1
  let h : Bool → A := by
    intro _
    exact a2
  have h3 : f ∘ g = f ∘ h := by
    funext z
    calc
      (f ∘ g) z = f a1      := by exact rfl
      _         = f a2      := by exact h2
      _         = (f ∘ h) z := by exact rfl
  specialize h1 h3
  calc
    a1 = g true := by exact rfl
    _  = h true := by exact congrFun h1 true
    _  = a2     := by exact rfl

-- If a function has left inverse then it is injective
theorem THasLeftInvtoInj {A B : Type} {f : A → B} : hasleftinv f → injective f := by
  intro h1 a1 a2 h2
  cases h1
  rename_i g h1
  calc
    a1 = id a1      := by exact rfl
    _  = (g ∘ f) a1 := by exact congrFun h1.symm a1
    _  = g (f a1)   := by exact rfl
    _  = g (f a2)   := by exact congrArg g h2
    _  = (g ∘ f) a2 := by exact rfl
    _  = id a2      := by exact congrFun h1 a2
    _  = a2         := by exact rfl

end a05InjExercises
end Inj

namespace Surj
-- Definition of surjective function
def surjective {A B : Type} (f : A → B) : Prop :=
∀{b : B}, ∃ (a : A), f a = b

-- Definition of epimorphism
def epimorphism {A B : Type} (f : A → B) : Prop :=
∀{C : Type}, ∀{g h : B → C}, g∘f = h∘f → g = h

-- Right inverse
def hasrightinv {A B : Type} (f : A → B) : Prop :=
∃ (g : B → A), f∘ g = id

-- The identity is surjective
theorem TIdSurj : surjective (@id A) := by
  -- rw [surjective] -- rw to recover the definition
  intro a
  apply Exists.intro a
  exact rfl

-- The identity is an epimorphism
theorem TIdMon : epimorphism (@id A) := by
  -- rw [epimorphism] -- rw to recover the definition
  intro C g h h1
  calc
    g = g ∘ id := by exact rfl
    _ = h ∘ id := by exact h1
    _ = h      := by exact rfl

-- The identity has a right inverse
theorem TIdHasRightInv : hasrightinv (@id A) := by
  -- rw [hasrightinv] -- rw to recover the definition
  apply Exists.intro id
  exact rfl

-- ## Exercises
namespace a05SurjExercises
-- Negation of surjective
theorem TNegSurj {A B : Type} {f: A → B} : ¬ (surjective f) ↔ ∃ (b : B), ∀ (a : A), f a ≠ b := by
  apply Iff.intro
  -- ¬surjective f → ∃ b, ∀ (a : A), f a ≠ b
  intro h1
  rw [surjective] at h1
  false_or_by_contra
  rename_i h2
  have h3 : ∀{b : B}, ∃ (a : A), f a = b := by
    intro b
    false_or_by_contra
    rename_i h4
    have h5 : ∃ (b : B), ∀ (a : A), f a ≠ b := by
      apply Exists.intro b
      intro a
      false_or_by_contra
      rename_i h5
      have h6 : ∃ (a : A), f a = b := by
        exact Exists.intro a h5
      exact h4 h6
    exact h2 h5
  exact h1 h3
  -- (∃ b, ∀ (a : A), f a ≠ b) → ¬surjective f
  intro h1
  cases h1
  rename_i b h1
  intro h2
  have h3 : ∃ (a : A), f a = b := h2
  cases h3
  rename_i a h3
  specialize h1 a
  exact h1 h3

-- The composition of surjective functions is surjective
theorem TCompSurj {A B : Type} {f : A → B} {g : B → C} (h1 : surjective f)
(h2 : surjective g) : surjective (g∘f) := by
  intro c
  have h3 : ∃ (b : B), g b = c := h2
  cases h3
  rename_i b h3
  have h4 : ∃ (a : A), f a = b := h1
  cases h4
  rename_i a h4
  apply Exists.intro a
  calc
    (g ∘ f) a = g (f a) := by exact rfl
    _         = g b     := by exact congrArg g h4
    _         = c       := by exact h3

-- If the composition (g∘f) is surjective, then g is surjective
theorem TCompLSurj {f : A → B} {g : B → C} (h1: surjective (g∘f))
: (surjective g) := by
  intro c
  have h2 : ∃ (a : A), (g ∘ f) a = c := h1
  cases h2
  rename_i a h2
  apply Exists.intro (f a)
  exact h2

-- Surjective and Epimorphism are equivalent concepts
theorem TCarEpiSurj {A B : Type} {f : A → B} : surjective f ↔ epimorphism f := by
  apply Iff.intro
  -- surjective f → epimorphism f
  intro h1
  intro C g h h2
  funext b
  have h3 : ∃ (a : A), f a = b := h1
  cases h3
  rename_i a h3
  calc
    g b = g (f a)   := by exact congrArg g h3.symm
    _   = (g ∘ f) a := by exact rfl
    _   = (h ∘ f) a := by exact congrFun h2 a
    _   = h (f a)   := by exact rfl
    _   = h b       := by exact congrArg h h3
  -- epimorphism f → surjective f
  intro h1 b
  rw [epimorphism] at h1
  false_or_by_contra
  rename_i h2
  let g : B → Prop := by
    intro z
    exact ∃ (a : A), f a = z
  let h : B → Prop := by
    intro _
    exact True
  have h3 : g ∘ f = h ∘ f := by
    funext a
    apply propext
    apply Iff.intro
    -- (g ∘ f) a → (h ∘ f) a
    intro _
    exact trivial
    -- (h ∘ f) a → (g ∘ f) a
    intro _
    apply Exists.intro a
    exact rfl
  have h4 : g = h := by exact h1 h3
  have h5 : g b = h b := by exact congrFun h4 b
  have h6 : True := trivial
  have h7 : h b = True := by exact rfl
  have h8 : g b = ∃ (a : A), f a = b := by exact rfl
  rw [h7.symm, h5.symm, h8] at h6
  exact h2 h6

-- If a function has right inverse then it is surjective
theorem THasRightInvtoInj {A B : Type} {f : A → B} : hasrightinv f → surjective f := by
  intro h b
  cases h
  rename_i g h
  apply Exists.intro (g b)
  calc
    f (g b) = (f ∘ g) b := by exact rfl
    _       = id b      := by exact congrFun h b
    _       = b         := by exact rfl

end a05SurjExercises
end Surj

namespace Bij
open Surj Inj a05InjExercises a05SurjExercises

-- Definition of bijective function
def bijective {A B : Type} (f : A → B) : Prop :=
injective f ∧ surjective f

-- Definition of isomorphism
def isomorphism {A B : Type} (f : A → B) : Prop :=
∃ (g : B → A), g∘f = id ∧ f∘g = id

-- The identity is bijective
theorem TIdBij : bijective (@id A) := by
  -- rw [bijective] -- rw to recover the definition
  apply And.intro
  exact TIdInj A
  exact TIdSurj A

-- The identity is an isomorphism
theorem TIdMon : isomorphism (@id A) := by
  rw [isomorphism] -- rw to recover the definition
  apply Exists.intro id
  apply And.intro
  exact rfl
  exact rfl

-- ## Exercises
namespace a05BijExercises
-- The composition of bijective functions is bijective
theorem TCompBij {A B : Type} {f : A → B} {g : B → C} (h1 : bijective f)
(h2 : bijective g) : bijective (g∘f) := by
  rw [bijective] at *
  apply And.intro
  apply TCompInj
  exact h1.left
  exact h2.left
  apply TCompSurj
  exact h1.right
  exact h2.right

-- A function is an isomorphism if and only if
-- it has left and right inverse
theorem TCarIso {A B : Type} {f : A → B} : isomorphism f ↔ (hasleftinv f ∧ hasrightinv f) := by
  apply Iff.intro
  -- isomorphism f → hasleftinv f ∧ hasrightinv f
  intro h
  cases h
  rename_i g h1
  apply And.intro
  -- hasleftinv f
  exact Exists.intro g h1.left
  -- hasrightinv f
  exact Exists.intro g h1.right
  -- hasleftinv f ∧ hasrightinv f → isomorphism f
  intro ⟨h1, h2⟩
  cases h1
  rename_i g h1
  cases h2
  rename_i h h2
  have h3 : g = h := by
    calc
      g = g ∘ id      := by exact rfl
      _ = g ∘ (f ∘ h) := by exact congrArg (Function.comp g) h2.symm
      _ = (g ∘ f) ∘ h := by exact rfl
      _ = id ∘ h      := by exact congrFun (congrArg Function.comp h1) h
      _ = h           := by exact rfl
  apply Exists.intro g
  apply And.intro
  exact h1
  rw [h3]
  exact h2

-- Every isomorphism is bijective
theorem TCarIsotoBij {A B : Type} {f : A → B} : isomorphism f → bijective f := by
  intro h1
  have h2 : hasleftinv f  := by exact (TCarIso.mp h1).left
  have h3 : hasrightinv f := by exact (TCarIso.mp h1).right
  have h4 : injective f   := by exact THasLeftInvtoInj h2
  have h5 : surjective f  := by exact THasRightInvtoInj h3
  exact And.intro h4 h5

end a05BijExercises
end Bij
