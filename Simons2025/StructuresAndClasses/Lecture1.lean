/-
Copyright (c) 2025 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio
-/
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Config.Environment
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Nat.Lattice
import Mathlib.Topology.Defs.Basic

namespace Structures

-- # Defining Structures

whatsnew in
@[ext]
structure QuadraticAlgebra (a b : R) where
  /-- Component of the integer not multiplied by `ω` -/
  x : R
  /-- Component of the integer multiplied by `ω` -/
  y : R
  deriving DecidableEq

structure HasZero (X : Type*) where
  zero' : X

export HasZero (zero')

scoped notation "𝟘" => zero' -- type `𝟘` as `\b0`.

structure Magma (X : Type*) where
  sum : X → X → X

export Magma (sum)

#check Magma.sum
#print Magma

structure Monoid (X : Type*) extends HasZero X, Magma X where
  sum_zero (x : X) : sum zero' x = x
  zero_sum (x : X) : sum x zero' = x
  sum_assoc (x y z : X) : sum (sum x y) z = sum x (sum y z)

-- *⌘*


-- ## Producing terms

-- ### In explicit types

def α : QuadraticAlgebra (37 : ℤ) 42 where
  x := -1
  y := 1

def β : QuadraticAlgebra (37 : ℤ) 42 := {x := -1, y := 1}
def β' : QuadraticAlgebra (37 : ℤ) 42 := {y := 1, x := -1}

def γ : QuadraticAlgebra (37 : ℤ) 42 := ⟨-1, 1⟩

def δ : QuadraticAlgebra (37 : ℤ) 42 := by
  constructor
  use -1
  use 1

example : α = β := rfl
example : α = β' := rfl
example : α = γ := rfl
example : α = δ := rfl

-- ### Showing that some explicit type has a structure
def NatHasZero : HasZero ℕ where
  zero' := sorry

def BoolHasZero : HasZero Bool := by
  use sorry

#check (𝟘 NatHasZero)

#check (𝟘 BoolHasZero)

def NatMagma : Magma ℕ := ⟨fun n m ↦ n + m⟩

def BoolMagma : Magma Bool where
 sum p q := match p, q with
 | _, _ => true

/-- ### Exercise
 Put a `Magma` structure on `Prop` using `⋀` as sum. -/
def PropMagma : Magma Prop := sorry

infix:70 " † " => Magma.sum

#eval NatMagma.sum 3 2
#eval (NatMagma † 3) 2

def NatMonoid : Monoid ℕ where
  zero' := 0
  sum := sorry
  sum_zero := sorry
  zero_sum := sorry
  sum_assoc := by sorry

-- ### Exercise
/- Define the same `Monoid` structure on `ℕ` using different syntaxes. -/
def NatMonoid' : Monoid ℕ where
__ := sorry
__ := sorry
sum_zero := sorry
zero_sum := sorry
sum_assoc n m l := sorry

def NatMonoid'' : Monoid ℕ :=
{ NatHasZero, NatMagma with
  sum_assoc n m l := sorry
  sum_zero := sorry
  zero_sum := sorry
  }

-- ### Exercise
/- Put a `Monoid` structure on `Prop` using the above sum. -/
def PropMonoid : Monoid Prop where
  zero' := True
  sum_zero := sorry
  zero_sum := sorry
  __ := sorry
  sum_assoc p q r := sorry

-- ### Exercise
/- Can you put a `Monoid` structure on `Bool` generalising what we did before?-/
def BoolMonoid : Monoid Bool := sorry

-- ### Exercise
/- As an exercise, define a `Semigroup` to be an associative `Magma`, and a
`Monoid₁` as a Semigroup with `0`.-/
structure Semigroup (X : Type*) extends Magma X where --add something!

structure Monoid₁ (X : Type*) extends Semigroup X, HasZero X

def NatMonoid₁ : Monoid₁ ℕ where
  sum := sorry
  zero' := sorry
  sum_assoc m n k := sorry

-- ### Exercise
-- Why will this always fail?
example : NatMonoid = NatMonoid₁ := sorry

-- # Some metric/topology


whatsnew in
structure SpaceWithMetric (X : Type*) where
  d : X → X → ℝ
  dist_eq_zero (x : X) : d x x = 0
  dist_pos (x y : X) : x ≠ y → 0 < d x y
  symm (x y : X) : d x y = d y x
  triangle (x y z : X) : d x z ≤ d x y + d y z

def RealMetric : SpaceWithMetric ℝ where
  d := sorry
  dist_eq_zero _ := sorry
  dist_pos _ _ h := sorry
  symm _ _ := sorry
  -- symm _ _ := abs_sub_comm ..
  -- triangle x y z := abs_sub_le x y z
  triangle := sorry

-- ### Exercise
-- Define a `SpaceWithMetric` structure on `ℕ`.
def NatMetric : SpaceWithMetric ℕ := sorry

def RealMagma: Magma ℝ := by --{sum := @Add.add ℝ _}
  constructor
  intro x y
  exact x + y

-- ### Exercise
-- What is a `Magma` homomorphism? Define it so that the next `def` compiles.
-- structure MagmaHom (X Y : Type*) (hX : Magma X) (hY : Magma Y) where

-- def coeMagmaHom : MagmaHom ℕ ℝ (NatMagma) (RealMagma) where

-- A `wrong` approach to "every metric induces a topology"

def metricToTopology (X : Type*) (hX : SpaceWithMetric X) : (TopologicalSpace X) where
  IsOpen := by
    intro S
    exact ∀ x ∈ S, ∃ ρ : ℝ, 0 < ρ ∧ {y | hX.d x y < ρ} ⊆ S
  isOpen_univ := by
    by_cases hX : Nonempty X
    · rintro x -
      use 1
      simp
    · tauto
  isOpen_inter := by
    intro S T hS hT x ⟨hxS, hxT⟩
    let ρS := (hS x hxS).choose
    let ρT := (hT x hxT).choose
    use min ρS ρT
    constructor
    · apply lt_min
      exact (hS x hxS).choose_spec.1
      exact (hT x hxT).choose_spec.1
    apply Set.subset_inter
    · apply subset_trans _ (hS x hxS).choose_spec.2
      intro _ hy
      simp only [lt_min_iff, Set.mem_setOf_eq] at hy
      exact hy.1
    · apply subset_trans _ (hT x hxT).choose_spec.2
      intro _ hy
      simp only [lt_min_iff, Set.mem_setOf_eq] at hy
      exact hy.2
  isOpen_sUnion := by
    intro Ω hΩ x ⟨T, hT, hx⟩
    use (hΩ T hT x hx).choose
    constructor
    · exact (hΩ T hT x hx).choose_spec.1
    apply subset_trans (hΩ T hT x hx).choose_spec.2
    exact Set.subset_sUnion_of_subset Ω T (by rfl) hT

end Structures

namespace Classes

class HasZero (X : Type*) where
  zero' : X

export HasZero (zero')

scoped notation "𝟘" => zero'

instance : HasZero ℕ where
  zero' := 0

instance : HasZero Bool := by
  use true

#check (𝟘 : ℕ)

#check (𝟘 : Bool)

class Magma (X : Type*) where
  sum : X → X → X

infix:70 " † " => Magma.sum

instance : Magma ℕ := ⟨fun n m ↦ n + m⟩

#eval (3 † 2) † 𝟘

class SpaceWithMetric (X : Type*) where
  d : X → X → ℝ
  dist_eq_zero (x : X) : d x x = 0
  dist_pos (x y : X) : x ≠ y → 0 < d x y
  symm (x y : X) : d x y = d y x
  triangle (x y z : X) : d x z ≤ d x y + d y z

export SpaceWithMetric (d)

instance TopOnMetric (X : Type*) [HX : SpaceWithMetric X] : TopologicalSpace X := by
  have hX : Structures.SpaceWithMetric X := by
    constructor
    · exact SpaceWithMetric.dist_eq_zero
    · exact SpaceWithMetric.dist_pos
    · exact SpaceWithMetric.symm
    · exact SpaceWithMetric.triangle
  exact (Structures.metricToTopology X hX)

-- ### Some problems

example : Continuous (fun (x : ℝ) ↦ x + 1) := continuous_add_right ..

example : Continuous (fun n : ℝ × ℝ ↦ (⟨n.2, n.1⟩ : (ℝ × ℝ))) := by
  rw [continuous_prodMk]
  apply And.intro
  · apply continuous_snd
  · apply continuous_fst

#synth TopologicalSpace ℝ

instance MetricOnProd (X Y : Type*) [SpaceWithMetric X] [SpaceWithMetric Y] :
    SpaceWithMetric (X × Y) where
  d := by
    rintro ⟨p₁, p₂⟩ ⟨q₁, q₂⟩
    exact max (d p₁ q₁) (d p₂ q₂)
  dist_eq_zero := by simp [SpaceWithMetric.dist_eq_zero]
  dist_pos := by
    rintro ⟨p₁, p₂⟩ ⟨q₁, q₂⟩ H
    simp
    simp at H
    by_cases h : p₁ = q₁
    · right
      apply SpaceWithMetric.dist_pos
      exact H h
    · left
      apply SpaceWithMetric.dist_pos
      exact h
  symm := by simp [SpaceWithMetric.symm]
  triangle := by
    intro p q r
    simp
    constructor
    · calc
        d p.1 r.1 ≤ (d p.1 q.1) + (d q.1 r.1) := by apply SpaceWithMetric.triangle
        _ ≤ max (d p.1 q.1) (d p.2 q.2) + (d q.1 r.1) := by
          gcongr
          apply le_max_left
        _ ≤ max (d p.1 q.1) (d p.2 q.2) + max (d q.1 r.1) (d q.2 r.2) := by
          gcongr
          apply le_max_left
    · calc
        d p.2 r.2 ≤ (d p.2 q.2) + (d q.2 r.2) := by apply SpaceWithMetric.triangle
        _ ≤ max (d p.1 q.1) (d p.2 q.2) + (d q.2 r.2) := by
          gcongr
          apply le_max_right
        _ ≤ max (d p.1 q.1) (d p.2 q.2) + max (d q.1 r.1) (d q.2 r.2) := by
          gcongr
          apply le_max_right


instance : SpaceWithMetric ℝ where
__ := Structures.RealMetric

#synth TopologicalSpace ℝ

example : Continuous (fun (x : ℝ) ↦ x + 1) := continuous_add_right ..

#synth SpaceWithMetric (ℝ × ℝ)

instance : TopologicalSpace (ℝ × ℝ) := @TopOnMetric _ (MetricOnProd ℝ ℝ)

#synth TopologicalSpace (ℝ × ℝ)


example : Continuous (fun n : ℝ × ℝ ↦ (⟨n.2, n.1⟩ : (ℝ × ℝ))) := by
  rw [continuous_prodMk]
  apply And.intro
  · apply continuous_snd
  · apply continuous_fst

end Classes
