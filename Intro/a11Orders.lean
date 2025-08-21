-- # Orders
import a03Quantifiers
import a06NaturalNumbers
import a09Relations
import a10Equivalence
open Operations
open N
open a06Exercises

-- Definition of a preorder
structure Preorder {A : Type} (R : A → A → Prop) : Prop where
  refl : ∀ (a : A), R a a
  trans : ∀ {a b c : A}, R a b → R b c → R a c

-- Definition of a partial order
structure PartialOrder {A : Type} (R : A → A → Prop) : Prop where
  toPreorder : Preorder R
  antisymm : ∀ {a b : A}, R a b → R b a → a = b

-- Definition of a poset
structure Poset where
  base : Type
  R    : base → base → Prop
  toPartialOrder : PartialOrder R

-- ## Inverse Partial Order
-- If `R` is a preorder, then `R^` is a preorder
theorem TPreorderInv {A : Type} (R : A → A → Prop) : Preorder R → Preorder (inverse R) := by
  intro h
  apply Preorder.mk
  -- Refl
  intro a
  rw [inverse]
  exact h.refl a
  -- Trans
  intro a b c h1 h2
  rw [inverse] at *
  exact h.trans h2 h1

-- If `R` is a partial ordre, then `R^` is a partial order
theorem TPartialOrderInv {A : Type} (R : A → A → Prop) : PartialOrder R → PartialOrder (inverse R) := by
  intro h
  apply PartialOrder.mk
  -- toPreoder
  exact TPreorderInv R (h.toPreorder)
  -- antisymm
  intro a b h1 h2
  exact h.antisymm h2 h1

-- ## Special Elements
-- `z` is a **least element** with respect to `R` if `R z a`, for every `a : A`
def Least {A : Type} (R : A → A → Prop) (z : A) : Prop := ∀ {a : A}, R z a

-- `z` is a **greatest element** with respect to `R` if `R a z`, for every `a : A`
def Greatest {A : Type} (R : A → A → Prop) (z : A) : Prop := ∀ {a : A}, R a z

-- `z` is a **minimal element** if no strictly smaller element exists
def Minimal {A : Type} (R : A → A → Prop) (z : A) : Prop := ∀ {a : A}, R a z → a = z

-- `z` is a **maximal element** if no strictly greater element exists
def Maximal {A : Type} (R : A → A → Prop) (z : A) : Prop :=  ∀ {a : A}, R z a → a = z

-- ### Bounded Posets
-- Posets with a least and greatest element
structure BoundedPoset extends Poset where
  l : base
  least : Least R l
  g : base
  greatest : Greatest R g

-- ### Exercises
-- If `R` is a partial order and `z1` and `z2` are least
-- elements, then they are equal
theorem LeastUnique {A : Type} (R : A → A → Prop) (z1 z2 : A) (h : PartialOrder R) (h1 : Least R z1) (h2 : Least R z2) : z1 = z2 := h.antisymm h1 h2

-- If `R` is a partial order and `z1` and `z2` are greatest
-- elements, then they are equal
theorem GreatestUnique {A : Type} (R : A → A → Prop) (z1 z2 : A) (h : PartialOrder R) (h1 : Greatest R z1) (h2 : Greatest R z2) : z1 = z2 := h.antisymm h2 h1

-- If `R` is a partial order and `z` is the least element,
-- then it is a minimal element
def LeasttoMinimal {A : Type} (R : A → A → Prop) (z : A) (h : PartialOrder R) : Least R z → Minimal R z := by
  intro h1 a h2
  exact h.antisymm h2 h1

-- If `R` is a partial order and `z` is the greatest element,
-- then it is a maximal element
def GreatesttoMaximal {A : Type} (R : A → A → Prop) (z : A) (h : PartialOrder R) : Greatest R z → Maximal R z := by
  intro h1 a h2
  exact h.antisymm h1 h2

-- A least element for `R` is a greatest element for `R^`
def LeasttoGreatestInv {A : Type} (R : A → A → Prop) (z : A) : Least R z → Greatest (inverse R) z := by
  intro h1 a
  exact h1

-- A greatest element for `R` is a least element for `R^`
def GreatesttoLeastInv {A : Type} (R : A → A → Prop) (z : A) : Greatest R z → Least (inverse R) z := by
  intro h1 a
  exact h1

-- A minimal element for `R` is a maximal element for `R^`
def MinimaltoMaximalInv {A : Type} (R : A → A → Prop) (z : A) : Minimal R z → Maximal (inverse R) z := by
  intro h1 a
  exact h1

-- A maximal element for `R` is a minimal element for `R^`
def MaximaltoMinimalInv {A : Type} (R : A → A → Prop) (z : A) : Maximal R z → Minimal (inverse R) z := by
  intro h1 a
  exact h1

-- ## Orders Relative to Subtypes
-- The `Restriction` of a relation to a Subtype
def Restriction {A : Type} (R : A → A → Prop) (P : A → Prop) : Subtype P → Subtype P → Prop := by
  intro a1 a2
  exact R a1.val a2.val

-- If `R` is a preorder then `Restriction R P`, for a
-- predicate `P`, is a preorder
theorem TPRestriction {A : Type} (R : A → A → Prop) (P : A → Prop) : Preorder R → Preorder (Restriction R P) := by
  intro h
  apply Preorder.mk
  --refl
  intro a
  exact h.refl a.val
  -- trans
  intro a b c h1 h2
  exact h.trans h1 h2

-- If `R` is a partial order then `Restriction R P`, for a
-- predicate `P`, is a partial ordre
theorem TPORestriction {A : Type} (R : A → A → Prop) (P : A → Prop) : PartialOrder R → PartialOrder (Restriction R P) := by
  intro h
  apply PartialOrder.mk
  -- toPreorder
  exact TPRestriction R P (h.toPreorder)
  -- antisymm
  intro a b h1 h2
  apply Subtype.eq
  exact h.antisymm h1 h2

-- ### Special Elements relative to a Subtype
-- `z` is an **upper bound** of a subtype `P` if it is above
-- all the elements of `Subtype P`
def UpperBound {A : Type} (R : A → A → Prop) (P : A → Prop) (z : A) : Prop := ∀ (a : A), P a → R a z

-- `z` is the **supremum** of a subtype `P` if it is an
-- upper bound, and any other upper bound is greater
-- or equal than `z`
structure Supremum {A : Type} (R : A → A → Prop) (P : A → Prop) (z : A) : Prop where
  -- Upper Bound
  UB : (UpperBound R P z)
  -- Least Upper Bound
  LUB : ∀ (x : A), (UpperBound R P x → R z x)

-- `z` is the **maximum** element of a subtype `P` if it
-- is the Greatest element of subtype `P`
structure Maximum {A : Type} (R : A → A → Prop) (P : A → Prop) (z : A) : Prop where
  -- Supremum
  toSupremum : (Supremum R P z)
  -- In Subtype P
  Sub : P z

-- `z` is a **lower bound** of a subtype `P` if it is below
-- all the elements of `Subtype P`
def LowerBound {A : Type} (R : A → A → Prop) (P : A → Prop) (z : A) : Prop := ∀ (a : A), P a → R z a

-- `z` is the **infimum** of a subtype `P` if it is a
-- lower bound, and any other lower bound is smaller
-- or equal than `z`
structure Infimum {A : Type} (R : A → A → Prop) (P : A → Prop) (z : A) : Prop where
  -- Lower Bound
  LB : (LowerBound R P z)
  -- Greatest Lower Bound
  GLB : ∀ (x : A), (LowerBound R P x → R x z)

-- `z` is the **minimum** element of a subtype `P` if it
-- is the Least element of subtype `P`
structure Minimum {A : Type} (R : A → A → Prop) (P : A → Prop) (z : A) : Prop where
  -- Infimum
  toInfimum : (Infimum R P z)
  -- In Subtype P
  Sub : P z

-- #### Exercises
-- The supremum of the False predicate is the least element
theorem TLeastSupPFalse {A : Type} (R : A → A → Prop) (z : A) : Least R z ↔ Supremum R PFalse z := by
  apply Iff.intro
  -- Least R z → Supremum R PFalse z
  intro h
  apply Supremum.mk
  -- UpperBound R PFalse z
  intro a ha
  exact False.elim ha
  -- ∀ (x : A), UpperBound R PFalse x → R z x
  intro x _
  exact h
  -- Supremum R PFalse z → Least R z
  intro ⟨_, h2⟩ a
  specialize h2 a
  apply h2
  intro x hx
  exact False.elim hx

-- The infimum of the False predicate is the greatest element
theorem TGreatestInfPFalse {A : Type} (R : A → A → Prop) (z : A) : Greatest R z ↔ Infimum R PFalse z := by
  apply Iff.intro
  -- Greatest R z → Infimum R PFalse z
  intro h
  apply Infimum.mk
  -- LowerBound R PFalse z
  intro a ha
  exact False.elim ha
  -- ∀ (x : A), LowerBound R PFalse x → R x z
  intro x _
  exact h
  -- Infimum R PFalse z → Greatest R z
  intro ⟨_, h2⟩ a
  specialize h2 a
  apply h2
  intro x hx
  exact False.elim hx

-- The infimum of the True predicate is the least element
theorem TLeastInfPTrue {A : Type} (R : A → A → Prop) (z : A) : Least R z ↔ Infimum R PTrue z := by
  apply Iff.intro
  -- Least R z → Infimum R PTrue z
  intro h1
  apply Infimum.mk
  -- LowerBound R PTrue z
  intro a _
  exact h1
  -- ∀ (x : A), LowerBound R PTrue x → R x z
  intro a h2
  apply h2
  exact trivial
  -- Infimum R PTrue z → Least R z
  intro ⟨h1, _⟩ a
  apply h1
  exact trivial

-- The supremum of the True predicate is the greatest element
theorem TGreatestSupPTrue {A : Type} (R : A → A → Prop) (z : A) : Greatest R z ↔ Supremum R PTrue z := by
  apply Iff.intro
  -- Greatest R z → Supremum R PTrue z
  intro h1
  apply Supremum.mk
  -- UpperBound R PTrue z
  intro a _
  exact h1
  -- ∀ (x : A), UpperBound R PTrue x → R z x
  intro a h2
  apply h2
  exact trivial
  -- Supremum R PTrue z → Greatest R z
  intro ⟨h1, _⟩ a
  apply h1
  exact trivial

-- ### Lattice
-- Posets with a infimum and supremum for every pair of elements
@[ext] structure Lattice extends Poset where
  meet : base → base → base
  infimum : ∀ {a b : base}, Infimum R (fun (x : base) => (x = a) ∨ (x = b)) (meet a b)
  join : base → base → base
  supremum : ∀ {a b : base}, Supremum R (fun (x : base) => (x = a) ∨ (x = b)) (join a b)

-- There is an alternative way to describe a lattice
-- as an algebra `(A, ∧, ∨)` with two binary, commutative
-- and associative operations satisfying the absorption laws
@[ext] structure LatticeAlg where
  base : Type
  meet : base → base → base
  join : base → base → base
  meetcomm : ∀ {a b : base}, meet a b = meet b a
  joincomm : ∀ {a b : base}, join a b = join b a
  meetass  : ∀ {a b c : base}, meet (meet a b) c = meet a (meet b c)
  joinass  : ∀ {a b c : base}, join (join a b) c = join a (join b c)
  abslaw1  : ∀ {a b : base}, join a (meet a b) = a
  abslaw2  : ∀ {a b : base}, meet a (join a b) = a

-- The opposite of a Lattice, intercharging meet and join
def LatticeAlgOp : LatticeAlg → LatticeAlg := by
  intro C
  refine {
    base := C.base,
    meet := C.join,
    join := C.meet,
    meetcomm := C.joincomm,
    joincomm := C.meetcomm,
    meetass := C.joinass,
    joinass := C.meetass,
    abslaw1 := C.abslaw2,
    abslaw2 := C.abslaw1
  }

-- The opposite of the opposite is the original Lattice
theorem TIdLatticeAlgOp : LatticeAlgOp ∘ LatticeAlgOp = id := by
  funext C
  apply LatticeAlg.ext
  -- Base
  exact rfl
  -- Meet
  exact HEq.refl ((LatticeAlgOp ∘ LatticeAlgOp) C).meet
  -- Join
  exact HEq.refl ((LatticeAlgOp ∘ LatticeAlgOp) C).join

-- There are usually 2 more laws regarding the idempotency
-- of the meet and join operations that can be derived
-- from the other axioms
theorem meetidpt {C : LatticeAlg} : ∀ (a : C.base), C.meet a a = a := by
  intro a
  calc
    C.meet a a = C.meet a (C.join a (C.meet a a)) := congrArg (C.meet a) C.abslaw1.symm
    _          = a                                := C.abslaw2

theorem joinidpt {C : LatticeAlg} : ∀ (a : C.base), C.join a a = a := by
  intro a
  calc
    C.join a a = C.join a (C.meet a (C.join a a)) := congrArg (C.join a) C.abslaw2.symm
    _          = a                                := C.abslaw1

-- The following result will be of interest later
theorem meetjoin {C : LatticeAlg} : ∀ {a b : C.base}, (C.meet a b = a) ↔ (C.join a b = b) := by
  intro a b
  apply Iff.intro
  -- C.meet a b = a → C.join a b = b
  intro h
  rw [C.meetcomm] at h
  rw [C.joincomm, h.symm]
  exact C.abslaw1
  -- C.join a b = b → C.meet a b = a
  intro h
  rw [h.symm]
  exact C.abslaw2

-- Any Lattice induces a LatticeAlg
def LatticetoLatticeAlg : Lattice → LatticeAlg := by
  intro C
  refine {
    base := C.base,
    meet := C.meet,
    join := C.join,
    meetcomm := by
      intro a b
      apply C.toPoset.toPartialOrder.antisymm
      -- C.R (C.meet a b) (C.meet b a)
      apply C.infimum.GLB
      intro z h
      cases h
      -- b
      rename_i hz
      apply C.infimum.LB
      exact Or.inr hz
      -- a
      rename_i hz
      apply C.infimum.LB
      exact Or.inl hz
      -- C.R (C.meet b a) (C.meet a b)
      apply C.infimum.GLB
      intro z h
      cases h
      -- a
      rename_i hz
      apply C.infimum.LB
      exact Or.inr hz
      -- b
      rename_i hz
      apply C.infimum.LB
      exact Or.inl hz
    joincomm := by
      intro a b
      apply C.toPoset.toPartialOrder.antisymm
      -- C.R (C.join a b) (C.join b a)
      apply C.supremum.LUB
      intro z h
      cases h
      -- a
      rename_i hz
      apply C.supremum.UB
      exact Or.inr hz
      -- b
      rename_i hz
      apply C.supremum.UB
      exact Or.inl hz
      -- C.R (C.join b a) (C.join a b)
      apply C.supremum.LUB
      intro z h
      cases h
      -- b
      rename_i hz
      apply C.supremum.UB
      exact Or.inr hz
      -- a
      rename_i hz
      apply C.supremum.UB
      exact Or.inl hz
    meetass := by
      intro a b c
      apply C.toPoset.toPartialOrder.antisymm
      -- C.R (C.meet (C.meet a b) c) (C.meet a (C.meet b c))
      apply C.infimum.GLB
      intro z h
      cases h
      -- a
      rename_i hz
      have h1 : C.R (C.meet (C.meet a b) c) (C.meet a b) := by
        apply C.infimum.LB
        exact Or.inl rfl
      have h2 : C.R (C.meet a b) z := by
        apply C.infimum.LB
        exact Or.inl hz
      exact C.toPoset.toPartialOrder.toPreorder.trans h1 h2
      -- C.meet b c
      rename_i hz
      rw [hz]
      apply C.infimum.GLB
      intro d hd
      cases hd
      -- b
      rename_i hd
      rw [hd]
      have h1 : C.R (C.meet (C.meet a b) c) (C.meet a b) := by
        apply C.infimum.LB
        exact Or.inl rfl
      have h2 : C.R (C.meet a b) b := by
        apply C.infimum.LB
        exact Or.inr rfl
      exact C.toPoset.toPartialOrder.toPreorder.trans h1 h2
      -- c
      rename_i hd
      apply C.infimum.LB
      exact Or.inr hd
      -- C.R (C.meet a (C.meet b c)) (C.meet (C.meet a b) c)
      apply C.infimum.GLB
      intro z h
      cases h
      -- C.meet a b
      rename_i hz
      rw [hz]
      apply C.infimum.GLB
      intro d hd
      cases hd
      -- a
      rename_i hd
      apply C.infimum.LB
      exact Or.inl hd
      -- b
      rename_i hd
      rw [hd]
      have h1 : C.R (C.meet a (C.meet b c)) (C.meet b c) := by
        apply C.infimum.LB
        exact Or.inr rfl
      have h2 : C.R (C.meet b c) b := by
        apply C.infimum.LB
        exact Or.inl rfl
      exact C.toPoset.toPartialOrder.toPreorder.trans h1 h2
      -- c
      rename_i hz
      have h1 : C.R (C.meet a (C.meet b c)) (C.meet b c) := by
        apply C.infimum.LB
        exact Or.inr rfl
      have h2 : C.R (C.meet b c) z := by
        apply C.infimum.LB
        exact Or.inr hz
      exact C.toPoset.toPartialOrder.toPreorder.trans h1 h2
    joinass := by
      intro a b c
      apply C.toPoset.toPartialOrder.antisymm
      -- C.R (C.join (C.join a b) c) (C.join a (C.join b c))
      apply C.supremum.LUB
      intro z h
      cases h
      -- C.join a b
      rename_i hz
      rw [hz]
      apply C.supremum.LUB
      intro d hd
      cases hd
      -- a
      rename_i hd
      apply C.supremum.UB
      exact Or.inl hd
      -- b
      rename_i hd
      have h1 : C.R d (C.join b c) := by
        apply C.supremum.UB
        exact Or.inl hd
      have h2 : C.R (C.join b c) (C.join a (C.join b c)) := by
        apply C.supremum.UB
        exact Or.inr rfl
      exact C.toPoset.toPartialOrder.toPreorder.trans h1 h2
      -- c
      rename_i hz
      have h1 : C.R z (C.join b c) := by
        apply C.supremum.UB
        exact Or.inr hz
      have h2 : C.R (C.join b c) (C.join a (C.join b c)) := by
        apply C.supremum.UB
        exact Or.inr rfl
      exact C.toPoset.toPartialOrder.toPreorder.trans h1 h2
      -- C.R (C.join a (C.join b c)) (C.join (C.join a b) c)
      apply C.supremum.LUB
      intro z h
      cases h
      -- a
      rename_i hz
      have h1 : C.R z (C.join a b) := by
        apply C.supremum.UB
        exact Or.inl hz
      have h2 : C.R (C.join a b) (C.join (C.join a b) c) := by
        apply C.supremum.UB
        exact Or.inl rfl
      exact C.toPoset.toPartialOrder.toPreorder.trans h1 h2
      -- C.join b c
      rename_i hz
      rw [hz]
      apply C.supremum.LUB
      intro d hd
      cases hd
      -- b
      rename_i hd
      have h1 : C.R d (C.join a b) := by
        apply C.supremum.UB
        exact Or.inr hd
      have h2 : C.R (C.join a b) (C.join (C.join a b) c) := by
        apply C.supremum.UB
        exact Or.inl rfl
      exact C.toPoset.toPartialOrder.toPreorder.trans h1 h2
      -- c
      rename_i hd
      apply C.supremum.UB
      exact Or.inr hd
    abslaw1 := by
      intro a b
      apply C.toPoset.toPartialOrder.antisymm
      -- C.R (C.join a (C.meet a b)) a
      apply C.supremum.LUB
      intro d hd
      cases hd
      -- a
      rename_i hd
      rw [hd]
      apply C.toPoset.toPartialOrder.toPreorder.refl
      -- C.meet a b
      rename_i hd
      rw [hd]
      apply C.infimum.LB
      exact Or.inl rfl
      -- C.R a (C.join a (C.meet a b))
      apply C.supremum.UB
      exact Or.inl rfl
    abslaw2 := by
      intro a b
      apply C.toPoset.toPartialOrder.antisymm
      -- C.R (C.meet a (C.join a b)) a
      apply C.infimum.LB
      exact Or.inl rfl
      -- C.R a (C.meet a (C.join a b))
      apply C.infimum.GLB
      intro d hd
      cases hd
      -- a
      rename_i hd
      rw [hd]
      apply C.toPoset.toPartialOrder.toPreorder.refl
      -- C.join a b
      rename_i hd
      rw [hd]
      apply C.supremum.UB
      exact Or.inl rfl
  }

-- Every LatticeAlg induces a relation on its base
def LAR {C : LatticeAlg} : C.base → C.base → Prop := by
  intro a b
  exact C.meet a b = a

-- `LAR` is a preorder
theorem TLARPreorder {C : LatticeAlg} : Preorder (@LAR C) := by
  apply Preorder.mk
  -- refl
  intro a
  rw [LAR]
  exact meetidpt a
  -- trans
  intro a b c h1 h2
  rw [LAR] at *
  rw [h1.symm, C.meetass, h2]

-- `LAR` is a partial order
theorem TLARPartialOrder {C : LatticeAlg} : PartialOrder (@LAR C) := by
  apply PartialOrder.mk
  -- toPreorder
  exact TLARPreorder
  -- antisymm
  intro a b h1 h2
  calc
    a = C.meet a b := h1.symm
    _ = C.meet b a := C.meetcomm
    _ = b          := h2

-- Every LatticeAlg induces a Poset
def LatticeAlgtoPoset : LatticeAlg → Poset := by
  intro C
  refine {
    base := C.base,
    R := @LAR C,
    toPartialOrder := TLARPartialOrder
  }

-- Every LatticeAlg induces a Lattice
def LatticeAlgtoLattice : LatticeAlg → Lattice := by
  intro C
  refine {
    toPoset := {
      base := C.base,
      R := @LAR C,
      toPartialOrder := TLARPartialOrder
    }
    meet := C.meet,
    infimum := by
      intro a b
      apply Infimum.mk
      -- LowerBound
      intro z hz
      cases hz
      -- a
      rename_i hz
      rw [hz]
      have h1 : C.meet (C.meet a b) a = (C.meet a b) := by
        calc
          C.meet (C.meet a b) a = C.meet a (C.meet a b) := C.meetcomm.symm
          _                     = C.meet (C.meet a a) b := C.meetass.symm
          _                     = C.meet a b            := congrArg (fun x => C.meet x b) (meetidpt a)
      exact h1
      -- b
      rename_i hz
      rw [hz]
      have h1 : C.meet (C.meet a b) b = (C.meet a b) := by
        calc
          C.meet (C.meet a b) b = C.meet a (C.meet b b) := C.meetass
          _                     = C.meet a b            := congrArg (fun x => C.meet a x) (meetidpt b)
      exact h1
      -- Greatest LowerBound
      intro x h
      have ha : C.meet x a = x := by
        apply h
        exact Or.inl rfl
      have hb : C.meet x b = x := by
        apply h
        exact Or.inr rfl
      have h1 : C.meet x (C.meet a b) = x := by
        calc
          C.meet x (C.meet a b) = C.meet (C.meet x a) b := C.meetass.symm
          _                     = C.meet x b            := congrArg (fun z => C.meet z b) ha
          _                     = x                     := hb
      exact h1
    join := C.join,
    supremum := by
      intro a b
      apply Supremum.mk
      -- UpperBound
      intro z hz
      cases hz
      -- a
      rename_i hz
      rw [hz]
      exact C.abslaw2
      -- b
      rename_i hz
      rw [hz, C.joincomm]
      exact C.abslaw2
      -- Least UpperBound
      intro x h
      have ha : C.meet a x = a := by
        apply h
        exact Or.inl rfl
      have hb : C.meet b x = b := by
        apply h
        exact Or.inr rfl
      have hax : C.join a x = x := meetjoin.mp ha
      have hbx : C.join b x = x := meetjoin.mp hb
      have h1 : C.join (C.join a b) x = x := by
        calc
          C.join (C.join a b) x = C.join a (C.join b x) := C.joinass
          _                     = C.join a x            := congrArg (fun z => C.join a z) hbx
          _                     = x                     := hax
      exact meetjoin.mpr h1
  }

--
theorem TIdLattice : LatticeAlgtoLattice ∘ LatticetoLatticeAlg = id := by
  funext C
  apply Lattice.ext
  -- base
  exact rfl
  -- R
  have hR : (LatticeAlgtoLattice (LatticetoLatticeAlg C)).R = C.R := by
    funext a b
    apply propext
    apply Iff.intro
    -- ((LatticeAlgtoLattice ∘ LatticetoLatticeAlg) C).R a b → C.R a b
    intro h
    have hs : C.meet a b = a := h
    rw [hs.symm]
    apply C.infimum.LB
    exact Or.inr rfl
    -- C.R a b → (LatticeAlgtoLattice (LatticetoLatticeAlg C)).R a b
    intro h
    have hs : C.meet a b = a := by
      apply C.toPoset.toPartialOrder.antisymm
      -- C.R (C.meet a b) a
      apply C.infimum.LB
      exact Or.inl rfl
      -- C.R a (C.meet a b)
      apply C.infimum.GLB
      intro z hz
      cases hz
      -- a
      rename_i hz
      rw [hz]
      exact C.toPoset.toPartialOrder.toPreorder.refl a
      -- b
      rename_i hz
      rw [hz]
      exact h
    exact hs
  exact heq_of_eq hR
  -- meet
  exact HEq.refl C.meet
  -- join
  exact HEq.refl C.join

--
theorem TIdLatticeAlg : LatticetoLatticeAlg ∘ LatticeAlgtoLattice = id := by
  funext C
  apply LatticeAlg.ext
  -- base
  exact rfl
  -- meet
  exact HEq.refl C.meet
  -- join
  exact HEq.refl C.join

-- ## Distributive Lattice
-- Distributive Lattice
@[ext] structure DistLatticeAlg extends LatticeAlg where
  dist : ∀ {a b c : base}, meet a (join b c) = join (meet a b) (meet a c)

def LatticeAlgtoDistLatticeAlg {C : LatticeAlg} : (∀ {a b c : C.base}, (@LAR C) (C.meet a (C.join b c)) (C.join (C.meet a b) (C.meet a c))) → DistLatticeAlg := by
  intro h
  refine {
    toLatticeAlg := C,
    dist := by
      intro a b c
      apply (@TLARPartialOrder C).antisymm
      -- (C.meet a (C.join b c)) ≤ (C.join (C.meet a b) (C.meet a c))
      exact h
      -- (C.join (C.meet a b) (C.meet a c)) ≤ (C.meet a (C.join b c))
      apply (@LatticeAlgtoLattice C).infimum.GLB
      intro z h1
      cases h1
      -- z = a
      rename_i h1
      rw [h1]
      apply (@LatticeAlgtoLattice C).supremum.LUB
      intro w h2
      cases h2
      rename_i h2
      rw [h2]
      apply (@LatticeAlgtoLattice C).infimum.LB
      exact Or.inl rfl
      rename_i h2
      rw [h2]
      apply (@LatticeAlgtoLattice C).infimum.LB
      exact Or.inl rfl
      -- z = b ∨ c
      rename_i h1
      rw [h1]
      apply (@LatticeAlgtoLattice C).supremum.LUB
      intro w h2
      cases h2
      rename_i h2
      rw [h2]
      have h3 : (LatticeAlgtoLattice C).R (C.meet a b) b := by
        apply (@LatticeAlgtoLattice C).infimum.LB
        exact Or.inr rfl
      have h4 : (LatticeAlgtoLattice C).R b (C.join b c) := by
        apply (@LatticeAlgtoLattice C).supremum.UB
        exact Or.inl rfl
      exact (@LatticeAlgtoLattice C).toPoset.toPartialOrder.toPreorder.trans h3 h4
      rename_i h2
      rw [h2]
      have h3 : (LatticeAlgtoLattice C).R (C.meet a c) c := by
        apply (@LatticeAlgtoLattice C).infimum.LB
        exact Or.inr rfl
      have h4 : (LatticeAlgtoLattice C).R c (C.join b c) := by
        apply (@LatticeAlgtoLattice C).supremum.UB
        exact Or.inr rfl
      exact (@LatticeAlgtoLattice C).toPoset.toPartialOrder.toPreorder.trans h3 h4
  }

-- ### Complete Lattice
-- Posets with a infimum and supremum for every subtype
structure CompleteLattice extends Poset where
  meet : (base → Prop) → base
  infimum : ∀ {P : base → Prop}, Infimum R P (meet P)
  join : (base → Prop) → base
  supremum : ∀ {P : base → Prop}, Supremum R P (join P)

-- Every CompleteLattice is a Bounded Poset
def CompleteLatticetoBoundedPoset : CompleteLattice → BoundedPoset := by
  intro C
  refine {
    toPoset := C.toPoset,
    l := C.join (PFalse),
    least := (TLeastSupPFalse C.R (C.join PFalse)).mpr (C.supremum)
    g := C.meet (PFalse),
    greatest := (TGreatestInfPFalse C.R (C.meet PFalse)).mpr (C.infimum)
  }

-- Every CompleteLattice is a Lattice
def CompleteLatticetoLattice : CompleteLattice → Lattice := by
  intro C
  refine {
    toPoset := C.toPoset,
    meet := (fun a b => C.meet (fun (x : C.base) => (x = a) ∨ (x = b))),
    infimum := fun {a b} => C.infimum
    join := (fun a b => C.join (fun (x : C.base) => (x = a) ∨ (x = b))),
    supremum := fun {a b} => C.supremum
  }


namespace NLeq
-- The `≤` relation for `N`
def NLeq : N → N → Prop := by
  intro n m
  exact ∃ (k : N), n + k = m

-- Notation for `≤`
notation : 65 lhs:65 " ≤ " rhs:66 => NLeq lhs rhs

-- `≤` is a preorder
theorem TPreorderNLeq : Preorder NLeq := by
  apply Preorder.mk
  -- refl
  intro n
  apply Exists.intro z
  exact TAdd0R
  -- trans
  intro n m p h1 h2
  apply Exists.elim h1
  intro a h3
  apply Exists.elim h2
  intro b h4
  apply Exists.intro (a + b)
  calc
    n + (a + b) = (n + a) + b := TAddAss.symm
    _           = m + b       := TAddCongL h3
    _           = p           := h4

-- `≤` is a partial order
theorem TPartialOrderNLeq : PartialOrder NLeq := by
  apply PartialOrder.mk
  -- toPreorder
  exact TPreorderNLeq
  -- antisymm
  intro n m h1 h2
  apply Exists.elim h1
  intro a h1
  apply Exists.elim h2
  intro b h2
  rw [h1.symm, TAddAss] at h2
  have h3 : (a + b) = z := TAddCancLZ h2
  have h4 : a = z := TAddZ h3
  rw [h4] at h1
  rw [h1.symm]
  exact TAdd0R.symm

-- `(N,≤)` is a partially ordered type
def instPosetNLeq : Poset := {
  base := N,
  R    := NLeq,
  toPartialOrder := TPartialOrderNLeq
}

-- `z` is the least element
theorem TNLeqzL : ∀ {n : N}, z ≤ n := by
  intro n
  apply Exists.intro n
  exact rfl

-- No `s n` is below `z`
theorem TNLeqzR : ∀ {n : N}, ¬ (s n ≤ z) := by
  intro n h1
  apply Exists.elim h1
  intro a h2
  cases h2

-- If `n ≤ m` then `s n ≤ s m`
theorem TNLeqSuccT : ∀ {n m : N}, (n ≤ m) → (s n ≤ s m) := by
  intro n m h1
  apply Exists.elim h1
  intro a h2
  apply Exists.intro a
  rw [h2.symm]
  exact rfl

-- If `n ≰ m` then `s n ≰ s m`
theorem TNLeqSuccF : ∀ {n m : N}, (¬ (n ≤ m)) → (¬ (s n ≤ s m)) := by
  intro n m h1 h2
  apply Exists.elim h2
  intro a h3
  injection h3 with h3
  have h4 : n ≤ m := by
    apply Exists.intro a
    exact h3
  exact h1 h4

-- `≤` is decidable
def instDecidableNLeq : ∀ {n m : N}, Decidable (n ≤ m) := by
  intro n m
  match n, m with
    | z, _          => exact isTrue TNLeqzL
    | s n', z       => exact isFalse TNLeqzR
    | s n', s m'    =>
      match @instDecidableNLeq n' m' with
      | isTrue h    => exact isTrue  (TNLeqSuccT h)
      | isFalse h   => exact isFalse (TNLeqSuccF h)

-- `min n m` is a lower bound of `n`
theorem TMinNLeqL : ∀ {n m : N}, (mini n m) ≤ n := by
  intro n m
  cases n
  -- z
  rw [TMinzL]
  exact TNLeqzL
  -- s n
  rename_i n
  cases m
  -- z
  rw [TMinzR]
  exact TNLeqzL
  -- s m
  rename_i m
  rw [mini]
  apply TNLeqSuccT
  exact TMinNLeqL

-- `min n m` is a lower bound of `m`
theorem TMinNLeqR : ∀ {n m : N}, (mini n m) ≤ m := by
  intro n m
  rw [TMinComm]
  exact TMinNLeqL

-- `min n m` is the infimum for `n` and `m`
theorem TInfNLeq : ∀ {n m : N}, Infimum NLeq (fun (x : N) => (x = n) ∨ (x = m)) (mini n m) := by
  intro n m
  apply Infimum.mk
  -- LowerBound
  intro a h
  cases h
  -- a = n
  rename_i h
  rw [h]
  exact TMinNLeqL
  -- a = m
  rename_i h
  rw [h]
  exact TMinNLeqR
  --
  intro p h
  apply h
  exact TMinOut

-- `max n m` is an upper bound of `n`
theorem TMaxNLeqL : ∀ {n m : N}, n ≤ (maxi n m) := by
  intro n m
  cases n
  -- z
  rw [TMaxzL]
  exact TNLeqzL
  -- s n
  rename_i n
  cases m
  -- z
  rw [TMaxzR]
  exact (TPreorderNLeq.refl (s n))
  -- s m
  rename_i m
  rw [maxi]
  apply TNLeqSuccT
  exact TMaxNLeqL

-- `max n m` is an upper bound of `m`
theorem TMaxNLeqR : ∀ {n m : N}, m ≤ (maxi n m) := by
  intro n m
  rw [TMaxComm]
  exact TMaxNLeqL

-- `max n m` is the supremum of `n` and `m`
theorem TSupNLeq : ∀ {n m : N}, Supremum NLeq (fun (x : N) => (x = n) ∨ (x = m)) (maxi n m) := by
  intro n m
  apply Supremum.mk
  -- LowerBound
  intro a h
  cases h
  -- a = n
  rename_i h
  rw [h]
  exact TMaxNLeqL
  -- a = m
  rename_i h
  rw [h]
  exact TMaxNLeqR
  --
  intro p h
  apply h
  exact TMaxOut

-- `(N,≤)` is a lattice
def instLatticeNLeq : Lattice := {
  toPoset := instPosetNLeq,
  meet := mini,
  infimum := TInfNLeq,
  join := maxi,
  supremum := TSupNLeq
}

-- `min n (max m p) = max (min n m) (min n p)`
theorem TDistNLeq : ∀ {n m p : N}, mini n (maxi m p) = maxi (mini n m) (mini n p) := by
  intro n m p
  apply TPartialOrderNLeq.antisymm
  -- mini n (maxi p q) ≤ maxi (mini n p) (mini n q)
  apply TSupNLeq.UB
  match (@TMaxOut m p) with
    | Or.inl h1 => exact Or.inl (congrArg (fun x => mini n x) h1)
    | Or.inr h1 => exact Or.inr (congrArg (fun x => mini n x) h1)
  -- maxi (mini n p) (mini n q) ≤ mini n (maxi p q)
  apply TInfNLeq.GLB
  intro x h1
  cases h1
  --
  rename_i h1
  rw [h1]
  apply TSupNLeq.LUB
  intro y h2
  cases h2
  --
  rename_i h2
  rw [h2]
  exact TMinNLeqL
  --
  rename_i h2
  rw [h2]
  exact TMinNLeqL
  --
  rename_i h1
  rw [h1]
  apply TSupNLeq.LUB
  intro y h2
  cases h2
  --
  rename_i h2
  rw [h2]
  have h2 : mini n m ≤ m := TMinNLeqR
  have h3 : m ≤ maxi m p := TMaxNLeqL
  exact TPreorderNLeq.trans h2 h3
  --
  rename_i h2
  rw [h2]
  have h2 : mini n p ≤ p := TMinNLeqR
  have h3 : p ≤ maxi m p := TMaxNLeqR
  exact TPreorderNLeq.trans h2 h3

-- `(N,≤)` is a distributive lattice
def instDistLatticeAlgNLeq : DistLatticeAlg := {
  toLatticeAlg := @LatticetoLatticeAlg instLatticeNLeq,
  dist := TDistNLeq
}

end NLeq
-----------

namespace NDiv
-- The `∣` (divisor) relation for `N`
def NDiv : N → N → Prop := by
  intro n m
  exact ∃ (k : N), n * k = m

-- Notation for divisor (`\mid`)
notation : 65 lhs:65 " ∣ " rhs:66 => NDiv lhs rhs

-- `∣` is a preorder
theorem TPreorderNDiv : Preorder NDiv := by
  apply Preorder.mk
  -- refl
  intro n
  apply Exists.intro one
  exact TMult1R
  -- trans
  intro n m p h1 h2
  apply Exists.elim h1
  intro a h3
  apply Exists.elim h2
  intro b h4
  apply Exists.intro (a * b)
  rw [TMultAss.symm, h3, h4]

-- `|` is a partial order
theorem TPartialOrderNDiv : PartialOrder NDiv := by
  apply PartialOrder.mk
  -- toPreorder
  exact TPreorderNDiv
  -- antisymm
  intro n m h1 h2
  apply Exists.elim h1
  intro a h3
  apply Exists.elim h2
  intro b h4
  rw [h3.symm, TMultAss] at h4
  cases (TMultFix h4)
  -- Left
  rename_i h5
  rw [h5, TMult0L, h5.symm] at h3
  exact h3
  -- Right
  rename_i h5
  have h6 : a = one := (TMultOne.mp h5).left
  rw [h6, TMult1R] at h3
  exact h3

-- `(N, ∣)` is a partially ordered type
def instPosetNDiv : Poset := {
  base := N,
  R    := NDiv,
  toPartialOrder := TPartialOrderNDiv
}

-- `one` is the `least` element for `∣`
theorem TNDivOne : Least NDiv one := by
  intro n
  apply Exists.intro n
  exact rfl

-- `z` is the `greatest` element for `∣`
theorem TNDivZ : Greatest NDiv z := by
  intro n
  apply Exists.intro z
  exact TMult0R

-- `(N, ∣)` is a bounded partially ordered type
def instBoundedPosetNDiv : BoundedPoset := {
  base := N,
  R := NDiv,
  toPartialOrder := TPartialOrderNDiv,
  l := one,
  least := TNDivOne,
  g := z,
  greatest := TNDivZ
}

-- `z` does not divide any successor
theorem TNDivzL : ∀ {n : N}, ¬ (z ∣ s n) := by
  intro n h1
  apply Exists.elim h1
  intro a h2
  rw [TMult0L] at h2
  cases h2

end NDiv

namespace PropLeq
-- The `→` relation for `Prop`
def PropLeq : Prop → Prop → Prop := by
  intro P Q
  exact P → Q

-- `→` is a preorder
theorem TPreorderPropLeq : Preorder PropLeq := by
  apply Preorder.mk
  -- refl
  intro P h
  exact h
  -- trans
  intro P Q R h1 h2 h3
  exact h2 (h1 h3)

-- `→` is a partial order
theorem TPartialOrderPropLeq : PartialOrder PropLeq := by
  apply PartialOrder.mk
  -- toPreorder
  exact TPreorderPropLeq
  -- antisymm
  intro P Q h1 h2
  apply propext
  exact Iff.intro h1 h2

-- `(Prop, →)` is a partially ordered type
def instPosetPropLeq : Poset := {
  base := Prop,
  R    := PropLeq,
  toPartialOrder := TPartialOrderPropLeq
}

-- `False` is the `least` element for `→`
theorem TPropLeqFalse : Least PropLeq False := by
  intro P h
  exact False.elim h

-- `True` is the `greatest` element for `→`
theorem TPropLeqTrue : Greatest PropLeq True := by
  intro P _
  exact trivial

-- `(Prop, →)` is a bounded partially ordered type
def instBoundedPropLeq : BoundedPoset := {
  base := Prop,
  R := PropLeq,
  toPartialOrder := TPartialOrderPropLeq,
  l := False,
  least := TPropLeqFalse,
  g := True,
  greatest := TPropLeqTrue
}

-- `(Prop, ∧, ∨)` is a lattice (as an algebra)
def instLatticeAlgProp : LatticeAlg := {
  base := Prop,
  meet := And,
  join := Or,
  meetcomm := by
    intro P Q
    apply propext
    apply Iff.intro
    -- P ∧ Q → Q ∧ P
    intro ⟨hP, hQ⟩
    exact ⟨hQ, hP⟩
    -- Q ∧ P → P ∧ Q
    intro ⟨hQ, hP⟩
    exact ⟨hP, hQ⟩
  joincomm := by
    intro P Q
    apply propext
    apply Iff.intro
    -- P ∨ Q → Q ∨ P
    intro h
    match h with
      | Or.inl h => exact Or.inr h
      | Or.inr h => exact Or.inl h
    -- Q ∨ P → P ∨ Q
    intro h
    match h with
      | Or.inl h => exact Or.inr h
      | Or.inr h => exact Or.inl h
  meetass := by
    intro P Q R
    apply propext
    apply Iff.intro
    -- (P ∧ Q) ∧ R → P ∧ Q ∧ R
    intro ⟨⟨hP, hQ⟩, hR⟩
    exact ⟨hP, ⟨hQ, hR⟩⟩
    -- P ∧ Q ∧ R → (P ∧ Q) ∧ R
    intro ⟨hP, ⟨hQ, hR⟩⟩
    exact ⟨⟨hP, hQ⟩, hR⟩
  joinass := by
    intro P Q R
    apply propext
    apply Iff.intro
    -- (P ∨ Q) ∨ R → P ∨ Q ∨ R
    intro h
    match h with
      | Or.inl h => match h with
        | Or.inl h => exact Or.inl h
        | Or.inr h => exact Or.inr (Or.inl h)
      | Or.inr h => exact Or.inr (Or.inr h)
    -- P ∨ Q ∨ R → (P ∨ Q) ∨ R
    intro h
    match h with
      | Or.inl h => exact Or.inl (Or.inl h)
      | Or.inr h => match h with
        | Or.inl h => exact Or.inl (Or.inr h)
        | Or.inr h => exact Or.inr h
  abslaw1 := by
    intro P Q
    apply propext
    apply Iff.intro
    -- P ∨ P ∧ Q → P
    intro h
    match h with
      | Or.inl h => exact h
      | Or.inr h => exact h.left
    -- P → P ∨ P ∧ Q
    intro h
    exact Or.inl h
  abslaw2 := by
    intro P Q
    apply propext
    apply Iff.intro
    -- P ∧ (P ∨ Q) → P
    intro ⟨hP, _⟩
    exact hP
    -- P → P ∧ (P ∨ Q)
    intro h
    exact And.intro h (Or.inl h)
}

-- `(Prop, →)` is a complete lattice
def instCompleteLatticeProp : CompleteLattice := {
  base := Prop,
  R := PropLeq,
  toPartialOrder := TPartialOrderPropLeq,
  meet := (fun ℙ => ∀ (Q : Prop), ℙ Q → Q),
  infimum := by
    intro ℙ
    apply Infimum.mk
    -- Lower Bound
    intro R hR hF
    exact (hF R) hR
    -- Least Lower Bound
    intro R hLBR hR Q hQ
    apply hLBR
    exact hQ
    exact hR
  join := (fun ℙ => ∃ (Q : Prop), ℙ Q ∧ Q),
  supremum := by
    intro ℙ
    apply Supremum.mk
    -- Upper Bound
    intro R hPR hR
    apply Exists.intro R
    exact ⟨hPR, hR⟩
    -- Greatest Upper Bound
    intro R hUBR hEQ
    apply Exists.elim hEQ
    intro Q ⟨hPQ, hQ⟩
    apply hUBR Q
    exact hPQ
    exact hQ
}

end PropLeq

namespace PredLeq
-- The `→` relation for predicates on `A`
def PredLeq {A : Type} : (A → Prop) → (A → Prop) → Prop := by
  intro P Q
  exact ∀ {a : A}, P a → Q a

-- Notation for `→` (`\subseteq`)
notation : 65 lhs:65 " ⊆ " rhs:66 => PredLeq lhs rhs

-- `⊆` is a preorder
theorem TPreorderPredLeq {A : Type} : Preorder (@PredLeq A) := by
  apply Preorder.mk
  -- refl
  intro P a h
  exact h
  -- trans
  intro P Q R h1 h2
  intro a h3
  exact h2 (h1 h3)

-- `⊆` is a partial order
theorem TPartialOrderPredLeq {A : Type} : PartialOrder (@PredLeq A) := by
  apply PartialOrder.mk
  -- toPreorder
  exact TPreorderPredLeq
  -- antisymm
  intro P Q h1 h2
  funext a
  apply propext
  exact Iff.intro h1 h2

-- `(A → Prop, →)` is a partially ordered type
def instPosetPredLeq {A : Type} : Poset := {
  base := A → Prop,
  R    := PredLeq,
  toPartialOrder := TPartialOrderPredLeq
}

-- `PFalse` is the `least` element for `⊆`
theorem TPredLeqPFalse {A : Type} : Least (@PredLeq A) PFalse := by
  intro P a h
  exact False.elim h

-- `PTrue` is the `greatest` element for `⊆`
theorem TPredLeqPTrue {A : Type} : Greatest (@PredLeq A) PTrue := by
  intro P a _
  exact trivial

-- `(A → Prop, →)` is a bounded partially ordered type
def instBoundedPosetPredLeq {A : Type} : BoundedPoset := {
  base := A → Prop,
  R := PredLeq,
  toPartialOrder := TPartialOrderPredLeq,
  l := PFalse,
  least := TPredLeqPFalse,
  g := PTrue,
  greatest := TPredLeqPTrue
}

-- `(A → Prop, ∧, ∨)` is a lattice (as an algebra)
def instLatticeAlgPredLeq {A : Type} : LatticeAlg := {
  base := A → Prop,
  meet := by
    intro P Q a
    exact P a ∧ Q a,
  join := by
    intro P Q a
    exact P a ∨ Q a,
  meetcomm := by
    intro P Q
    funext a
    apply propext
    apply Iff.intro
    -- P ∧ Q → Q ∧ P
    intro ⟨h1, h2⟩
    exact ⟨h2, h1⟩
    -- Q ∧ P → P ∧ Q
    intro ⟨h1, h2⟩
    exact ⟨h2, h1⟩,
  joincomm := by
    intro P Q
    funext a
    apply propext
    apply Iff.intro
    -- P ∨ Q → Q ∨ P
    intro h1
    cases h1 with
    | inl h2 => exact Or.inr h2
    | inr h2 => exact Or.inl h2
    -- Q ∨ P → P ∨ Q
    intro h1
    cases h1 with
    | inl h2 => exact Or.inr h2
    | inr h2 => exact Or.inl h2,
  meetass := by
    intro P Q R
    funext a
    apply propext
    apply Iff.intro
    -- (P ∧ Q) ∧ R → P ∧ (Q ∧ R)
    intro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, ⟨h2, h3⟩⟩
    -- P ∧ (Q ∧ R) → (P ∧ Q) ∧ R
    intro ⟨h1, ⟨h2, h3⟩⟩
    exact ⟨⟨h1, h2⟩, h3⟩,
  joinass := by
    intro P Q R
    funext a
    apply propext
    apply Iff.intro
    -- (P ∨ Q) ∨ R → P ∨ (Q ∨ R)
    intro h1
    cases h1 with
    | inl h2 => cases h2 with
      | inl h3 => exact Or.inl h3
      | inr h3 => exact Or.inr (Or.inl h3)
    | inr h2 => exact Or.inr (Or.inr h2)
    -- P ∨ (Q ∨ R) → (P ∨ Q) ∨ R
    intro h1
    cases h1 with
    | inl h2 => exact Or.inl (Or.inl h2)
    | inr h2 => cases h2 with
      | inl h3 => exact Or.inl (Or.inr h3)
      | inr h3 => exact Or.inr h3
  abslaw1 := by
    intro P Q
    funext a
    apply propext
    apply Iff.intro
    -- P ∨ (P ∧ Q) → P
    intro h1
    cases h1 with
    | inl h2 => exact h2
    | inr h2 => exact h2.1
    -- P → P ∨ (P ∧ Q)
    intro h1
    exact Or.inl h1
  abslaw2 := by
    intro P Q
    funext a
    apply propext
    apply Iff.intro
    -- P ∧ (P ∨ Q) → P
    intro ⟨h1, _⟩
    exact h1
    -- P → P ∧ (P ∨ Q)
    intro h1
    exact ⟨h1, Or.inl h1⟩
}

-- `(A → Prop, →)` is a complete lattice
def instCompleteLatticePredLeq {A : Type} : CompleteLattice := {
  base := A → Prop,
  R := PredLeq,
  toPartialOrder := TPartialOrderPredLeq,
  meet := (fun ℙ => (fun a => ∀ (P: A → Prop), ℙ P → P a)),
  infimum := by
    intro ℙ
    apply Infimum.mk
    -- Lower Bound
    intro P hP a h
    exact (h P) hP
    -- Least Lower Bound
    intro P hLBP a hPa Q hQ
    apply hLBP
    exact hQ
    exact hPa
  join := (fun ℙ => (fun a => ∃ (P: A → Prop), ℙ P ∧ P a)),
  supremum := by
    intro ℙ
    apply Supremum.mk
    -- Upper Bound
    intro P hP a h
    apply Exists.intro P
    exact ⟨hP, h⟩
    -- Greatest Upper Bound
    intro P hLBP a hPa
    apply Exists.elim hPa
    intro Q ⟨hQ, hPQ⟩
    apply hLBP Q
    exact hQ
    exact hPQ
}

end PredLeq

namespace RelLeq
-- The `→` relation for relations on `A`
def RelLeq {A : Type} : (A → A → Prop) → (A → A → Prop) → Prop := by
  intro R S
  exact ∀ {a b : A}, R a b → S a b

-- Notation for `→` (`\subseteq`)
notation : 65 lhs:65 " ⊆ " rhs:66 => RelLeq lhs rhs

-- `⊆` is a preorder
theorem TPreorderRelLeq {A : Type} : Preorder (@RelLeq A) := by
  apply Preorder.mk
  -- refl
  intro R a b h
  exact h
  -- trans
  intro R S T h1 h2
  intro a b h3
  exact h2 (h1 h3)

-- `⊆` is a partial order
theorem TPartialOrderRelLeq {A : Type} : PartialOrder (@RelLeq A) := by
  apply PartialOrder.mk
  -- toPreorder
  exact TPreorderRelLeq
  -- antisymm
  intro R S h1 h2
  funext a b
  apply propext
  exact Iff.intro h1 h2

-- `(A → A → Prop, →)` is a partially ordered type
def instPosetRelLeq {A : Type} : Poset := {
  base := A →  A → Prop,
  R    := RelLeq,
  toPartialOrder := TPartialOrderRelLeq
}

-- `empty` is the `least` element for `⊆`
theorem TRelLeqEmpty {A : Type} : Least (@RelLeq A) empty := by
  intro R a b h
  apply False.elim h

-- `total` is the `greatest` element for `⊆`
theorem TRelLeqPTrue {A : Type} : Greatest (@RelLeq A) total := by
  intro R a b _
  exact trivial

-- `(A → A → Prop, →)` is a bounded partially ordered type
def instBoundedPosetRelLeq {A : Type} : BoundedPoset := {
  base := A → A → Prop,
  R := RelLeq,
  toPartialOrder := TPartialOrderRelLeq,
  l := empty,
  least := TRelLeqEmpty,
  g := total,
  greatest := TRelLeqPTrue
}

-- `(A → A → Prop, ∧, ∨)` is a lattice (as an algebra)
def instLatticeAlgRelLeq {A : Type} : LatticeAlg := {
  base := A → A → Prop,
  meet := by
    intro R S a b
    exact R a b ∧ S a b,
  join := by
    intro R S a b
    exact R a b ∨ S a b,
  meetcomm := by
    intro R S
    funext a b
    apply propext
    apply Iff.intro
    -- R ∧ S → S ∧ R
    intro ⟨h1, h2⟩
    exact ⟨h2, h1⟩
    -- S ∧ R → R ∧ S
    intro ⟨h1, h2⟩
    exact ⟨h2, h1⟩,
  joincomm := by
    intro R S
    funext a b
    apply propext
    apply Iff.intro
    -- R ∨ S → S ∨ R
    intro h1
    cases h1 with
    | inl h2 => exact Or.inr h2
    | inr h2 => exact Or.inl h2
    -- S ∨ R → R ∨ S
    intro h1
    cases h1 with
    | inl h2 => exact Or.inr h2
    | inr h2 => exact Or.inl h2,
  meetass := by
    intro R S T
    funext a b
    apply propext
    apply Iff.intro
    -- (R ∧ S) ∧ T → R ∧ (S ∧ T)
    intro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, ⟨h2, h3⟩⟩
    -- R ∧ (S ∧ T) → (R ∧ S) ∧ T
    intro ⟨h1, ⟨h2, h3⟩⟩
    exact ⟨⟨h1, h2⟩, h3⟩,
  joinass := by
    intro R S T
    funext a b
    apply propext
    apply Iff.intro
    -- (R ∨ S) ∨ T → R ∨ (S ∨ T)
    intro h1
    cases h1 with
    | inl h2 => cases h2 with
      | inl h3 => exact Or.inl h3
      | inr h3 => exact Or.inr (Or.inl h3)
    | inr h2 => exact Or.inr (Or.inr h2)
    -- R ∨ (S ∨ T) → (R ∨ S) ∨ T
    intro h1
    cases h1 with
    | inl h2 => exact Or.inl (Or.inl h2)
    | inr h2 => cases h2 with
      | inl h3 => exact Or.inl (Or.inr h3)
      | inr h3 => exact Or.inr h3
  abslaw1 := by
    intro R S
    funext a b
    apply propext
    apply Iff.intro
    -- R ∨ (R ∧ S) → R
    intro h1
    cases h1 with
    | inl h2 => exact h2
    | inr h2 => exact h2.1
    -- R → R ∨ (R ∧ S)
    intro h1
    exact Or.inl h1
  abslaw2 := by
    intro R S
    funext a b
    apply propext
    apply Iff.intro
    -- R ∧ (R ∨ S) → R
    intro ⟨h1, _⟩
    exact h1
    -- R → R ∧ (R ∨ S)
    intro h1
    exact ⟨h1, Or.inl h1⟩
}

-- `(A → A → Prop, →)` is a complete lattice
def instCompleteLatticeRelLeq {A : Type} : CompleteLattice := {
  base := A → A → Prop,
  R := RelLeq,
  toPartialOrder := TPartialOrderRelLeq,
  meet := (fun ℝ => (fun a b => ∀ (R : A → A → Prop), ℝ R → R a b)),
  infimum := by
    intro ℙ
    apply Infimum.mk
    -- Lower Bound
    intro R hR a b h
    exact (h R) hR
    -- Least Lower Bound
    intro R hLB a b hRab Q hQ
    apply hLB
    exact hQ
    exact hRab
  join := (fun ℝ => (fun a b => ∃ (R : A → A → Prop), ℝ R ∧ R a b)),
  supremum := by
    intro ℙ
    apply Supremum.mk
    -- Upper Bound
    intro R hR a b h
    apply Exists.intro R
    exact ⟨hR, h⟩
    -- Greatest Upper Bound
    intro R hLB a b hPab
    apply Exists.elim hPab
    intro Q ⟨hQ, hPQ⟩
    apply hLB Q
    exact hQ
    exact hPQ
}

end RelLeq
