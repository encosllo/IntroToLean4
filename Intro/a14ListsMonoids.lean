-- Lists and Monoids
import a05Functions
import a06NaturalNumbers
open Bij
open N
open a10Exercises

-- ## Definition
-- A list is a sequence of elements of a given type
-- A list can be empty or it can have one or more elements
-- A nonempty list is defined by its head and tail
-- The head is the first element of the list
-- The tail is the rest of the list
-- The empty list is denoted by `[]`
-- The list constructor is denoted by `::`
-- The list constructor takes an element and a list and returns a new list
#print List
#print List.nil
#print List.cons
#print List.append
-- ## Notation
-- `[]` is the empty list
-- `::` is the list constructor


-- ## Examples
#check []
#check z::[]
-- `[]` is the empty list
-- `1::[]` is a list with one element
-- `1::2::[]` is a list with two elements

namespace Monoids
-- ## Definition
-- A monoid is a set with an associative binary operation and an identity element
@[ext] structure Monoid.{u} where
  base : Type u
  mul : base → base → base
  one : base
  assoc : ∀ {a b c : base}, mul a (mul b c) = mul (mul a b) c
  idl : ∀ {a : base}, mul one a = a
  idr : ∀ {a : base}, mul a one = a

@[ext] structure MonoidHom (M N : Monoid) where
  map : M.base → N.base
  map_mul : ∀ {a b : M.base}, map (M.mul a b) = N.mul (map a) (map b)
  map_one : map M.one = N.one

-- (N, +, 0) is a monoid
def instMonoidNAdd : Monoid where
  base  := N
  mul   := Addition
  one   := z
  -- associativity
  assoc := TAddAss.symm
  -- id is the identity element on the left
  idl   := TAdd0L
  idr   := TAdd0R

-- (N, *, 1) is a monoid
def instMonoidNMul : Monoid where
  base  := N
  mul   := Multiplication
  one   := one
  -- associativity
  assoc := TMultAss.symm
  -- id is the identity element on the left
  idl   := TMult1L
  idr   := TMult1R

-- (List α, ++, []) is a monoid for any type α
def FreeMonoid {α : Type u} : Monoid where
  base := List α
  mul := List.append
  one := []
  -- associativity
  assoc := by
    intro a b c
    induction a with
      | nil => simp [List.append]
      | cons x xs ih => simp [List.append, ih]
  -- id is the identity element on the left
  idl := by
    intro a
    induction a with
      | nil => simp [List.append]
      | cons x xs ih => simp [List.append, ih]
  -- id is the identity element on the right
  idr := by
    intro a
    induction a with
      | nil => simp [List.append]
      | cons x xs ih => simp [List.append, ih]

-- ## Universal Property
-- Insertion of generators
def η {α : Type u} : α → (@FreeMonoid α).base := by
  intro a
  exact List.cons a []

-- The universal property of the `FreeMonoid α` is that every function `f` from
-- the base `α` to the base of any other monoid `M` can be
-- extended to a unique monoid homomorphism `Lift f` from `FreeMonoid α` to `M` satisfying that
-- `Lift f ∘ η = f` where `η` is the insertion of generators
def Lift {α : Type u} {M : Monoid} (f : α → M.base) : (@FreeMonoid α).base → M.base := by
  intro xs
  cases xs with
    | nil => exact M.one
    | cons x xs => exact M.mul (f x) (Lift f xs)

-- The function `Lift f` is a monoid homomorphism from the free monoid to the monoid `M`
def LiftMonoidHom {α : Type u} {M : Monoid} (f : α → M.base) : MonoidHom (@FreeMonoid α) M where
  map := Lift f
  map_mul := by
    intro a b
    induction a with
      | nil => calc
        Lift f (FreeMonoid.mul [] b) = Lift f b                     := rfl
        _                            = M.mul (M.one) (Lift f b)     := M.idl.symm
        _                            = M.mul (Lift f []) (Lift f b) := congrArg (fun x => M.mul x (Lift f b)) rfl
      | cons x xs ih => calc
        Lift f (FreeMonoid.mul (x::xs) b) = Lift f (x :: (FreeMonoid.mul xs b))         := rfl
        _                                 = M.mul (f x) (Lift f (FreeMonoid.mul xs b))  := rfl
        _                                 = M.mul (f x) (M.mul (Lift f xs) (Lift f b))  := congrArg (fun y => M.mul (f x) y) ih
        _                                 = M.mul (M.mul (f x) (Lift f xs)) (Lift f b)  := M.assoc
        _                                 = M.mul (Lift f (x::xs)) (Lift f b)           := congrArg (fun y => M.mul y (Lift f b)) rfl
  map_one := rfl

-- The function `Lift f` satsifies the property that `Lift f ∘ η = f`
theorem LiftEta {α : Type u} {M : Monoid} (f : α → M.base) : Lift f ∘ η = f := by
  funext a
  calc
    Lift f (η a) = Lift f (a::[])           := rfl
    _            = M.mul (f a) (Lift f [])  := rfl
    _            = M.mul (f a) M.one        := congrArg (fun x => M.mul (f a) x) rfl
    _            = f a                      := M.idr

-- The function `Lift f` is the unique monoid homomorphism from the free monoid to the monoid `M`
-- satisfying the property that `Lift f ∘ η = f`
theorem LiftUnique {α : Type u} {M : Monoid} (f : α → M.base) (g : MonoidHom (@FreeMonoid α) M) : g.map ∘ η = f → g = LiftMonoidHom f := by
  intro h
  apply MonoidHom.ext
  funext a
  induction a with
    | nil => calc
      g.map []  = M.one := g.map_one
      _         = (LiftMonoidHom f).map [] := (LiftMonoidHom f).map_one
    | cons x xs ih => calc
      g.map (x::xs) = g.map (FreeMonoid.mul (η x) xs)                                := rfl
      _             = M.mul (g.map (η x)) (g.map xs)                                 := g.map_mul
      _             = M.mul (f x) (g.map xs)                                         := congrArg (fun y => M.mul y (g.map xs)) (congrFun h x)
      _             = M.mul ((LiftMonoidHom f).map (η x)) (g.map xs)                 := congrArg (fun y => M.mul y (g.map xs)) (congrFun (LiftEta f).symm x)
      _             = M.mul ((LiftMonoidHom f).map (η x)) ((LiftMonoidHom f).map xs) := congrArg (fun y => M.mul ((LiftMonoidHom f).map (η x)) y) ih
      _             = (LiftMonoidHom f).map (FreeMonoid.mul (η x) xs)                := (LiftMonoidHom f).map_mul.symm
      _             = (LiftMonoidHom f).map (x::xs)                                  := rfl

-- The definition of the length of a list is the number of elements in the list
-- It can be defined as a monoid homomorphism from the free monoid to the monoid of
-- natural numbers
def Len : α → N := by
  intro _
  exact one

-- The length of a list is a monoid homomorphism from the free monoid
-- to the monoid of natural numbers
def Length {α : Type u} : (@FreeMonoid α).base → instMonoidNAdd.base := Lift Len

end Monoids

namespace a14Exercises
open Monoids

-- ## Exercises
@[ext] structure MonoidIso (M N : Monoid) extends (MonoidHom M N) where
  iso : isomorphism map

def g : N → (List Unit) := by
  intro n
  match n with
    | z   => exact []
    | s n => exact ()::(g n)

-- Prove that the monoids `instMonoidNAdd` and `@FreeMonoid Unit` are isomorphic
def NFreeMonoidIso : MonoidIso (@FreeMonoid Unit) instMonoidNAdd where
  map := @Length Unit
  map_mul := (@LiftMonoidHom Unit instMonoidNAdd Len).map_mul
  map_one := (@LiftMonoidHom Unit instMonoidNAdd Len).map_one
  iso := by
    apply Exists.intro g
    apply And.intro
    --
    funext l
    induction l with
      | nil => exact rfl
      | cons x xs ih => calc
        g (Length (x::xs)) = g (s (Length xs))   := rfl
        _                  = ()::(g (Length xs)) := rfl
        _                  = ()::xs              := congrArg (fun y => ()::y) ih
        _                  = (x::xs)             := rfl
    --
    funext n
    induction n with
      | z => exact rfl
      | s n ih => calc
        Length (g (s n)) = Length (()::(g n))   := rfl
        _                = one + (Length (g n)) := rfl
        _                = one + n              := congrArg (fun y => one + y) ih
        _                = s n                  := rfl

end a14Exercises
