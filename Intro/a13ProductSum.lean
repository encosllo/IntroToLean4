import a05Functions
import a10Equivalence
import a13EmptyUnit
import Paperproof
open Inj
open Surj
open Bij
open Empty
open Unit

namespace Product
-- ## Product type
-- The product type is a type that has two values
-- It is denoted by `A × B` in Lean `times`
#check Prod
#print Prod

variable (A B : Type)
#check A × B

-- To produce a value of type `A × B`, we need to provide
-- a value of type `A` and a value of type `B`
def toPair {A B : Type} : A → B → A × B := by
  intro a b
  exact ⟨a, b⟩

-- We can also use the `Prod.mk` constructor to produce a value of type `A × B`
def toPair' {A B : Type} : A → B → A × B := by
  intro a b
  exact Prod.mk a b

-- The `Prod` type has two projections, `fst` and `snd`,
-- that allow us to extract the first and second values, respectively
def π1 {A B : Type} : (A × B) → A := by
  intro p
  exact p.fst

def π2 {A B : Type} : (A × B) → B := by
  intro p
  exact p.snd

-- Two values of type `A × B` are equal if and only if
-- their first and second components are equal
-- For this we can use the `Prod.ext` function
theorem prodEq {A B : Type} (p1 p2 : A × B) : (p1 = p2) ↔ (π1 p1 = π1 p2) ∧ (π2 p1 = π2 p2) := by
  apply Iff.intro
  -- p1 = p2 → π1 p1 = π1 p2 ∧ π2 p1 = π2 p2
  intro h
  apply And.intro
  exact congrArg π1 h
  exact congrArg π2 h
  -- π1 p1 = π1 p2 ∧ π2 p1 = π2 p2 → p1 = p2
  intro ⟨h1, h2⟩
  apply Prod.ext
  exact h1
  exact h2

-- The universal property of the product type is that
-- if we have a function `f : C → A` and a function `g : C → B`,
-- we can construct a function `h : C → A × B` such that
-- `π1 ∘ h = f` and `π2 ∘ h = g`
def toProd {A B C : Type} (f : C → A) (g : C → B) : (C → A × B) := by
  intro c
  exact Prod.mk (f c) (g c)

-- The `toProd` function satisfies that the corresponding
-- composition with the projections `π1` and `π2`
-- give us back the original functions `f` and `g`
theorem toProdp1 {A B C : Type} (f : C → A) (g : C → B) : π1 ∘ (toProd f g) = f := by
  funext c
  exact rfl

theorem toProdp2 {A B C : Type} (f : C → A) (g : C → B) : π2 ∘ (toProd f g) = g := by
  funext c
  exact rfl

-- The universal property also states that if we have
-- a function `h : C → A × B`, satisfying `π1 ∘ h = f`
-- and `π2 ∘ h = g`, then `h` must be equal to `toProd f g`
theorem toProdUnique {A B C : Type} {f : C → A} {g : C → B} {h : C → A × B} : (π1 ∘ h = f) → (π2 ∘ h = g) → (h = toProd f g) := by
  intro h1 h2
  funext c
  apply Prod.ext
  exact congrFun h1 c
  exact congrFun h2 c

-- ## Product type of a family of types
-- For a type of indices `I`, the product type of
-- a family of types `𝔸 : I → Type` is a type
-- that has a value for each type in the family
-- It is denoted by `∀ (i : I), 𝔸 i` in Lean
variable (I : Type)
variable (𝔸 : I → Type)
#check ∀ (i : I), 𝔸 i

-- To produce a value of type `∀ (i : I), 𝔸 i`, we need to
-- provide a value of type `𝔸 i` for every `i : I`
def toPairg {I : Type} {𝔸 : I → Type} : ((i : I) → 𝔸 i) → ∀ (i : I), 𝔸 i := by
  intro 𝕗 i
  exact 𝕗 i

-- The `∀ (i : I), 𝔸 i` type has a projection
-- that allows us to extract the value for a given `i : I`
def π {I : Type} {𝔸 : I → Type} (i : I) : (∀ (i : I), 𝔸 i) → 𝔸 i := by
  intro 𝕒
  exact 𝕒 i

-- Two values of type `∀ (i : I), 𝔸 i` are equal if and only if
-- their `i`-th components are equal for every `i : I`
theorem prodEqg {I : Type} {𝔸 : I → Type} (𝕒1 𝕒2 : ∀ (i : I), 𝔸 i) : (𝕒1 = 𝕒2) ↔ ∀ (i : I), π i 𝕒1 = π i 𝕒2 := by
  apply Iff.intro
  -- 𝕒1 = 𝕒2 → ∀ (i : I), π i 𝕒1 = π i 𝕒2
  intro h i
  exact congrArg (π i) h
  -- (∀ (i : I), π i 𝕒1 = π i 𝕒2) → 𝕒1 = 𝕒2
  intro h
  funext i
  exact h i

-- The universal property of the product type is that
-- if we have a function `𝕗 i : C → 𝔸 i` for every `i : I`
-- we can construct a function `h : C → ∀ (i : I), 𝔸 i` such that
-- `(π i) ∘ h = 𝕗 i` for every `i : I`
def toProdg {I C : Type} {𝔸 : I → Type} (𝕗 : (i : I) → C → 𝔸 i) : C → (∀ (i : I), 𝔸 i) := by
  intro c i
  exact (𝕗 i) c

-- The `toProdg` function satisfies that the corresponding
-- composition with the projections `π i`
-- give us back the original functions `𝕗 i`
theorem toProdpg {I C : Type} {𝔸 : I → Type} (𝕗 : (i : I) → C → 𝔸 i) (i : I) : (π i) ∘ (toProdg 𝕗) = 𝕗 i := by
  funext c
  exact rfl

-- The universal property also states that if if we have
-- a function `h : C → ∀ (i : I), 𝔸 i`, satisfying `(π i) ∘ h = (𝕗 i)`
-- for every `i : I` then `h` must be equal to `toProdg f`
theorem toProdgUnique {I C : Type} {𝔸 : I → Type} {𝕗 : (i : I) → C → 𝔸 i} {h : C → ∀ (i : I), 𝔸 i} : (∀ (i : I), (π i) ∘ h = (𝕗 i)) → (h = toProdg 𝕗) := by
  intro hp
  funext c
  funext i
  exact congrFun (hp i) c

-- ## Exercises
-- The product is commutative
theorem prodComm {A B : Type} : (A × B) ≅ (B × A) := by
  let f : (A × B) → (B × A) := toProd π2 π1
  let g : (B × A) → (A × B) := toProd π2 π1
  let h : isomorphism f := by
    apply Exists.intro g
    apply And.intro
    -- g ∘ f = id
    funext e
    exact Prod.ext rfl rfl
    -- f ∘ g = id
    funext e
    exact Prod.ext rfl rfl
  apply Nonempty.intro
  exact Subtype.mk f h

-- The product is associative
theorem prodAssoc {A B C : Type} : ((A × B) × C) ≅ (A × (B × C)) := by
  let f : ((A × B) × C) → (A × (B × C)) := toProd (π1 ∘ π1) (toProd (π2 ∘ π1) π2)
  let g : (A × (B × C)) → ((A × B) × C) := toProd (toProd π1 (π1 ∘ π2)) (π2 ∘ π2)
  let h : isomorphism f := by
    apply Exists.intro g
    apply And.intro
    -- g ∘ f = id
    funext e
    exact Prod.ext rfl rfl
    -- f ∘ g = id
    funext e
    exact Prod.ext rfl rfl
  apply Nonempty.intro
  exact Subtype.mk f h

-- Empty is a left zero
theorem TEmptyProdL {A : Type} : (Empty × A) ≅ Empty := by
  let f : (Empty × A) → Empty := π1
  let g : Empty → (Empty × A) := toProd id emptyToAny
  let h : isomorphism f := by
    apply Exists.intro g
    apply And.intro
    -- g ∘ f = id
    funext e
    exact Empty.elim e.fst
    -- f ∘ g = id
    exact toProdp1 id emptyToAny
  apply Nonempty.intro
  exact Subtype.mk f h

-- Empty is a right zero
theorem TEmptyProdR {A : Type} : (A × Empty) ≅ Empty := by
  let f : (A × Empty) → Empty := π2
  let g : Empty → (A × Empty) := toProd emptyToAny id
  let h : isomorphism f := by
    apply Exists.intro g
    apply And.intro
    -- g ∘ f = id
    funext e
    exact Empty.elim e.snd
    -- f ∘ g = id
    exact toProdp2 emptyToAny id
  apply Nonempty.intro
  exact Subtype.mk f h

-- Unit is a right unit
theorem TUnitProdR {A : Type} : (A × Unit) ≅ A := by
  let f : (A × Unit) → A := π1
  let g : A → (A × Unit) := toProd id anyToUnit
  let h : isomorphism f := by
    apply Exists.intro g
    apply And.intro
    -- g ∘ f = id
    funext e
    exact Prod.ext rfl rfl
    -- f ∘ g = id
    exact toProdp1 id anyToUnit
  apply Nonempty.intro
  exact Subtype.mk f h

-- Unit is a left unit
theorem TUnitProdL {A : Type} : (Unit × A) ≅ A := by
  let f : (Unit × A) → A := π2
  let g : A → (Unit × A) := toProd anyToUnit id
  let h : isomorphism f := by
    apply Exists.intro g
    apply And.intro
    -- g ∘ f = id
    funext e
    exact Prod.ext rfl rfl
    -- f ∘ g = id
    exact toProdp2 anyToUnit id
  apply Nonempty.intro
  exact Subtype.mk f h

end Product

namespace Sum
open Product
-- ## Sum type
-- The sum type is a type that has two values
-- It is denoted by `A ⊕ B` in Lean `oplus`
#check Sum
#print Sum

variable (A B : Type)
#check A ⊕ B

-- The `Sum` type has two injections, `ι1` and `ι2`,
-- that allow us to provide an element of type `A ⊕ B`
-- (using `Sum.inl` and `Sum.inr`, respectively)
def ι1 {A B : Type} : A → A ⊕ B := by
  intro a
  exact Sum.inl a

def ι2 {A B : Type} : B → A ⊕ B := by
  intro b
  exact Sum.inr b

-- Two values of type `A ⊕ B` are equal if and only if
-- they are both injections on the same element
theorem sumEq {A B : Type} (p1 p2 : A ⊕ B) : (p1 = p2) ↔ (∃ (a : A), (((ι1 a) = p1) ∧ ((ι1 a) = p2))) ∨ (∃ (b : B), (((ι2 b) = p1) ∧ ((ι2 b) = p2))) := by
  apply Iff.intro
  -- p1 = p2 → (∃ a, ι1 a = p1 ∧ ι1 a = p2) ∨ ∃ b, ι2 b = p1 ∧ ι2 b = p2
  intro h
  cases p1 with
  | inl a => cases p2 with
    | inl b =>
      injection h with h1
      apply Or.inl
      apply Exists.intro a
      apply And.intro rfl
      rw [h1]
      exact rfl
    | inr b =>
      exact Sum.noConfusion h
  | inr a => cases p2 with
    | inl b =>
      exact Sum.noConfusion h
    | inr b =>
      injection h with h1
      apply Or.inr
      apply Exists.intro a
      apply And.intro rfl
      rw [h1]
      exact rfl
  -- ((∃ a, ι1 a = p1 ∧ ι1 a = p2) ∨ ∃ b, ι2 b = p1 ∧ ι2 b = p2) → p1 = p2
  intro h
  cases h with
  | inl h =>
    apply Exists.elim h
    intro a ⟨h1, h2⟩
    exact h1.symm.trans h2
  | inr h =>
    apply Exists.elim h
    intro b ⟨h1, h2⟩
    exact h1.symm.trans h2

-- The universal property of the sum type is that
-- if we have a function `f : A → C` and a function `g : B → C`,
-- we can construct a function `h : A ⊕ B → C` such that
-- `h ∘ ι1 = f` and `h ∘ ι2 = g`
def fromSum {A B C : Type} (f : A → C) (g : B → C) : (A ⊕ B) → C := by
  intro o
  cases o with
  | inl a => exact f a
  | inr b => exact g b

-- The `fromSum` function satisfies that the corresponding
-- composition with the injections `ι1` and `ι2`
-- give us back the original functions `f` and `g`
theorem fromSumi1 {A B C : Type} (f : A → C) (g : B → C) : (fromSum f g) ∘ ι1 = f := by
  funext a
  exact rfl

theorem fromSumi2 {A B C : Type} (f : A → C) (g : B → C) : (fromSum f g) ∘ ι2 = g := by
  funext b
  exact rfl

-- The universal property also states that if we have
-- a function `h : A ⊕ B → C`, satisfying `h ∘ ι1 = f`
-- and `h ∘ ι2 = g`, then `h` must be equal to `fromSum f g`
theorem fromSumUnique {A B C : Type} {f : A → C} {g : B → C} {h : (A ⊕ B) → C} : (h ∘ ι1 = f) → (h ∘ ι2 = g) → (h = fromSum f g) := by
  intro h1 h2
  funext o
  cases o with
  | inl a => exact congrFun h1 a
  | inr b => exact congrFun h2 b

-- ## Sum type of a family of types
-- The sum type of a family of types is a type
-- that has a value for some type in the family
-- It is denoted by `(Σ (i : I), 𝔸 i)` in Lean
variable (I : Type)
variable (𝔸 : I → Type)
#check Σ i, 𝔸 i
#check (Σ (i : I), 𝔸 i)

#check Sigma 𝔸
#print Sigma

-- The `(Σ (i : I), 𝔸 i)` type has an injection
-- that allows us to insert the value for a given `i : I`
def ι {I : Type} {𝔸 : I → Type} (i : I) : 𝔸 i → (Σ (i : I), 𝔸 i) := by
  intro a
  exact ⟨i, a⟩

-- Two values of type `(Σ (i : I), 𝔸 i)` are equal if and
-- only if they are both `ι i` of some `a : 𝔸 i`
-- For this we will use `Sigma.ext`
theorem sumEqg {I : Type} {𝔸 : I → Type} (𝕒1 𝕒2 : (Σ (i : I), 𝔸 i)) : (𝕒1 = 𝕒2) ↔ ∃ (i : I), ∃ (a : 𝔸 i), (𝕒1 = ι i a) ∧ (𝕒2 = ι i a) := by
  apply Iff.intro
  -- 𝕒1 = 𝕒2 → ∃ i a, 𝕒1 = ι i a ∧ 𝕒2 = ι i a
  intro h
  cases 𝕒1 with
  | mk i a => cases 𝕒2 with
    | mk j b =>
      injection h with h1 h2
      apply Exists.intro i
      apply Exists.intro a
      apply And.intro rfl
      exact Sigma.ext h1.symm h2.symm
  -- ∃ i a, 𝕒1 = ι i a ∧ 𝕒2 = ι i a → 𝕒1 = 𝕒2
  intro ⟨i, ⟨a, ⟨h1, h2⟩⟩⟩
  exact  h1.trans h2.symm

-- The universal property of the sum type is that
-- if we have a function `𝕗 i : 𝔸 i → C` for every `i : I`
-- we can construct a function `h : (Σ (i : I), 𝔸 i) → C` such that
-- `h ∘ (ι i) = 𝕗 i` for every `i : I`
def fromSumg {I C : Type} {𝔸 : I → Type} (𝕗 : (i : I) → 𝔸 i → C) : (Σ (i : I), 𝔸 i) → C := by
  intro ⟨i, a⟩
  exact 𝕗 i a

-- The `fromSumg` function satisfies that the corresponding
-- composition with the injections `ι i`
-- give us back the original functions `𝕗 i`
theorem fromSumig {I C : Type} {𝔸 : I → Type} (𝕗 : (i : I) → 𝔸 i → C) (i : I) : (fromSumg 𝕗) ∘ (ι i) = 𝕗 i := by
  funext c
  exact rfl

-- The universal property also states that if we have
-- a function `h : (Σ (i : I), 𝔸 i) → C`, satisfying `h ∘ (ι i) = 𝕗 i`
-- for every `i : I` then `h` must be equal to `fromSumg 𝕗`
theorem fromSumgUnique {I C : Type} {𝔸 : I → Type} {𝕗 : (i : I) → 𝔸 i → C} {h : (Σ (i : I), 𝔸 i) → C} : (∀ (i : I), h ∘ (ι i) = (𝕗 i)) → (h = fromSumg 𝕗) := by
  intro hs
  funext ⟨i, a⟩
  exact congrFun (hs i) a

-- ## Exercises
-- The sum is commutative
theorem sumComm {A B : Type} : (A ⊕ B) ≅ (B ⊕ A) := by
  let f : (A ⊕ B) → (B ⊕ A) := fromSum (ι2) (ι1)
  let g : (B ⊕ A) → (A ⊕ B) := fromSum (ι2) (ι1)
  let h : isomorphism f := by
    apply Exists.intro g
    apply And.intro
    -- g ∘ f = id
    funext e
    match e with
      | inl a => rfl
      | inr b => rfl
    -- f ∘ g = id
    funext e
    match e with
      | inl a => rfl
      | inr b => rfl
  apply Nonempty.intro
  exact Subtype.mk f h

-- The sum is associative
theorem sumAssoc {A B C : Type} : ((A ⊕ B) ⊕ C) ≅ (A ⊕ (B ⊕ C)) := by
  let f : ((A ⊕ B) ⊕ C) → (A ⊕ (B ⊕ C)) := fromSum (fromSum (ι1) (ι2 ∘ ι1)) (ι2 ∘ ι2)
  let g : (A ⊕ (B ⊕ C)) → ((A ⊕ B) ⊕ C) := fromSum (ι1 ∘ ι1) (fromSum (ι1 ∘ ι2) (ι2))
  let h : isomorphism f := by
    apply Exists.intro g
    apply And.intro
    -- g ∘ f = id
    funext e
    match e with
      | inl ab => match ab with
        | inl a => rfl
        | inr b => rfl
      | inr c => rfl
    -- f ∘ g = id
    funext e
    match e with
      | inl a => rfl
      | inr bc => match bc with
        | inl b => rfl
        | inr c => rfl
  apply Nonempty.intro
  exact Subtype.mk f h

-- Empty is a left unit
theorem TEmptySumL {A : Type} : (Empty ⊕ A) ≅ A := by
  let f : (Empty ⊕ A) → A := fromSum emptyToAny id
  let g : A → (Empty ⊕ A) := ι2
  let h : isomorphism f := by
    apply Exists.intro g
    apply And.intro
    -- g ∘ f = id
    funext e
    match e with
      | inl z => exact Empty.elim z
      | inr a => rfl
    -- f ∘ g = id
    funext e
    exact rfl
  apply Nonempty.intro
  exact Subtype.mk f h

-- Empty is a right unit
theorem TEmptySumR {A : Type} : (A ⊕ Empty) ≅ A := by
  let f : (A ⊕ Empty) → A := fromSum id emptyToAny
  let g : A → (A ⊕ Empty) := ι1
  let h : isomorphism f := by
    apply Exists.intro g
    apply And.intro
    -- g ∘ f = id
    funext e
    match e with
      | inl a => rfl
      | inr z => exact Empty.elim z
    -- f ∘ g = id
    funext e
    exact rfl
  apply Nonempty.intro
  exact Subtype.mk f h

-- Product distributes over sum on the right
theorem TProdSumDistR {A B C : Type} : (A × (B ⊕ C)) ≅ ((A × B) ⊕ (A × C)) := by
  let f : (A × (B ⊕ C)) → ((A × B) ⊕ (A × C)) := by
    intro ⟨a, bc⟩
    match bc with
      | inl b => exact Sum.inl (⟨a, b⟩)
      | inr c => exact Sum.inr (⟨a, c⟩)
  let g : ((A × B) ⊕ (A × C)) → (A × (B ⊕ C)) := fromSum (toProd π1 (ι1 ∘ π2)) (toProd π1 (ι2 ∘ π2))
  let h : isomorphism f := by
    apply Exists.intro g
    apply And.intro
    -- g ∘ f = id
    funext ⟨a, bc⟩
    match bc with
      | inl b => rfl
      | inr c => rfl
    -- f ∘ g = id
    funext e
    match e with
      | inl ⟨a,b⟩ => rfl
      | inr ⟨a,c⟩ => rfl
  apply Nonempty.intro
  exact Subtype.mk f h

-- Product distributes over sum on the left
theorem TProdSumDistL {A B C : Type} : ((A ⊕ B) × C) ≅ ((A × C) ⊕ (B × C)) := by
  let f : ((A ⊕ B) × C) → ((A × C) ⊕ (B × C)) := by
    intro ⟨ab, c⟩
    match ab with
      | inl a => exact Sum.inl (⟨a, c⟩)
      | inr b => exact Sum.inr (⟨b, c⟩)
  let g : ((A × C) ⊕ (B × C)) → ((A ⊕ B) × C) := fromSum (toProd (ι1 ∘ π1) π2) (toProd (ι2 ∘ π1) π2)
  let h : isomorphism f := by
    apply Exists.intro g
    apply And.intro
    -- g ∘ f = id
    funext ⟨ab, c⟩
    match ab with
      | inl a => rfl
      | inr b => rfl
    -- f ∘ g = id
    funext e
    match e with
      | inl ⟨a,c⟩ => rfl
      | inr ⟨b,c⟩ => rfl
  apply Nonempty.intro
  exact Subtype.mk f h

end Sum
