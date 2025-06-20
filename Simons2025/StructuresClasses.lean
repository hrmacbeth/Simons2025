/-
Copyright (c) 2025 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio
-/
import Mathlib.Algebra.Notation.Defs
import Mathlib.Data.Int.Notation
import Mathlib.Data.Nat.BinaryRec
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Logic.Function.Defs
import Mathlib.Tactic.Simps.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Config.Environment

namespace Structures

structure HasZero (X : Type*) where
  zero' : X

export HasZero (zero')

scoped notation "𝟘" => zero' -- type `𝟘` as `\b0`.

def NatHasZero : HasZero ℕ where
  zero' := 0

def BoolHasZero : HasZero Bool := by
  use true

#check (𝟘 NatHasZero)

#check (𝟘 BoolHasZero)

structure Magma (X : Type*) where
  sum : X → X → X

#check Magma.sum
#print Magma

export Magma (sum)

infix:70 " † " => Magma.sum

def NatMagma : Magma ℕ := ⟨fun n m ↦ n + m⟩

def BoolMagma : Magma Bool where
 sum p q := match p, q with
 | _, _ => true

def PropMagma : Magma Prop := { sum := And }

#eval NatMagma.sum 3 2
#eval (NatMagma † 3) 2

structure Monoid (X : Type*) extends HasZero X, Magma X where
  sum_zero (x : X) : sum zero' x = x
  zero_sum (x : X) : sum x zero' = x
  sum_assoc (x y z : X) : sum (sum x y) z = sum x (sum y z)

def NatMonoid : Monoid ℕ where
  zero' := 0
  sum := Nat.add
  sum_zero := zero_add
  zero_sum := add_zero
  sum_assoc := by
    intro n m l
    rw [Nat.add_eq]
    exact Nat.add_assoc n m l

def NatMonoid' : Monoid ℕ where
__ := NatHasZero
__ := NatMagma
sum_zero := zero_add
zero_sum := add_zero
sum_assoc n m l := by simpa [Nat.add_eq] using Nat.add_assoc ..

def NatMonoid'' : Monoid ℕ :=
{ NatHasZero, NatMagma with
  sum_assoc n m l := by simpa [Nat.add_eq] using Nat.add_assoc ..
  sum_zero := zero_add
  zero_sum := add_zero
  }

def PropMonoid : Monoid Prop where
  zero' := True
  sum_zero := true_and
  zero_sum := and_true
  __ := PropMagma
  sum_assoc p q r := by
    simp only [eq_iff_iff]
    exact and_assoc

def BoolMonoid : Monoid Bool :=
{ BoolHasZero, BoolMagma with
  sum_assoc p q r := by
    dsimp only [BoolMagma]
  sum_zero p := by
    have := Bool.or_true p
    --error!
    sorry
  zero_sum := sorry
  }

structure Semigroup (X : Type*) extends Magma X where
  sum_assoc (x y z : X) : sum (sum x y) z = sum x (sum y z)

structure Monoid₁ (X : Type*) extends Semigroup X, HasZero X

def NatMonoid₁ : Monoid₁ ℕ where
  sum := Nat.add
  zero' := 0
  sum_assoc m n k := by
    simp only [Nat.add_eq]
    exact Nat.add_assoc m n k

example : NatMonoid = NatMonoid₁ := sorry

whatsnew in
structure SpaceWithMetric (X : Type*) where
  d : X → X → ℝ
  dist_eq_zero (x : X) : d x x = 0
  dist_pos (x y : X) : x ≠ y → 0 < d x y
  symm (x y : X) : d x y = d y x
  triangle (x y z : X) : d x z ≤ d x y + d y z

def RealMetric : SpaceWithMetric ℝ where
  d := fun x y ↦ |x - y|
  dist_eq_zero _ := by rw [sub_self, abs_zero]
  dist_pos _ _ h := abs_sub_pos.mpr h
  symm _ _ := abs_sub_comm _ _
  -- symm _ _ := abs_sub_comm ..
  -- triangle x y z := abs_sub_le x y z
  triangle := abs_sub_le

def NatMetric : SpaceWithMetric ℕ where
  d n m := |max n m - min n m|
  dist_eq_zero n := by simp only [max_self, min_self, sub_self, abs_zero]
  dist_pos n m h := by
    simp only [Nat.cast_max, Nat.cast_min, abs_pos, ne_eq]
    rw [← min_lt_max] at h
    intro H
    rw [sub_eq_zero] at H
    norm_cast at H
    linarith
  symm _ _ := by rw [max_comm, min_comm]
  triangle n m k := by
    by_cases hmn : m ≤ n
    · by_cases hkm : k ≤ m
      · have hkn : k ≤ n := hkm.trans hmn
        simp only [hkn, sup_of_le_left, inf_of_le_right, hmn, hkm, ge_iff_le]
        apply abs_sub_le
      · by_cases hkn : k ≤ n
        · simp only [not_le] at hkm
          replace hkm := le_of_lt hkm
          simp [hkm, hmn, hkn]
          rw [abs_sub_comm (k : ℝ) m]
          apply abs_sub_le
        · simp only [not_le] at hkm hkn
          replace hkm := le_of_lt hkm
          replace hkn := le_of_lt hkn
          simp [hkm, hmn, hkn]
          rw [abs_sub_comm (k : ℝ) n]
          rw [abs_sub_comm (k : ℝ) m]
          apply abs_sub_le
    · simp at hmn
      replace hmn := le_of_lt hmn
      simp [hmn]
      by_cases hkm : m ≤ k
      · simp [hkm, hmn.trans hkm]
        rw [abs_sub_comm (k : ℝ) _]
        rw [abs_sub_comm (m : ℝ) _]
        rw [abs_sub_comm (k : ℝ) _]
        apply abs_sub_le
      · simp at hkm
        replace hkm := le_of_lt hkm
        by_cases hnk : n ≤ k
        · simp [hmn, hkm, hnk]
          rw [abs_sub_comm (k : ℝ) _]
          rw [abs_sub_comm (m : ℝ) _]
          apply abs_sub_le
        · simp at hnk
          replace hnk := le_of_lt hnk
          simp [hnk, hkm, hmn]
          rw [abs_sub_comm (m : ℝ) _]
          apply abs_sub_le

structure MagmaHom (X Y : Type*) (hX : Magma X) (hY : Magma Y) where
  toFun : X → Y
  addFun (x y : X) : toFun (sum hX x y) = sum hY (toFun x) (toFun y)

def RealMagma: Magma ℝ := by --{sum := @Add.add ℝ _}
  constructor
  intro x y
  exact x + y

def coeMagmaHom : MagmaHom ℕ ℝ (NatMagma) (RealMagma) where
  toFun := (↑)
  addFun a b := Nat.cast_add a b

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

/- Although this "seems to work" there are some points that are blatantly unsatisfactory:
1. We don't have a notation `†` that works nicely, we need to write `(NatMagma †) 3 2`
2. Although it is ok to be able to define arbitrary crazy additive structures on `ℕ`, we'd
like to record that there is a prefered one, whose name we can forget and that Lean remembers.
3. We would like things to chain automatically: we've defined a topological space on every space
  with metric, and we could define a metric on every product of metric spaces: but we don't get
  *automatically* a topology on `X × Y`...

**Type classes** are the solution (in `Lean`, other proof assistants, like `Rocq`, take a different\
approach). The idea is to build a database of terms of structures (like `NatMonoid : Monoid ℕ` or
`RealMetric : SpaceWithMetric ℝ`) that can be searched by `Lean` each time that it looks for some
property or some operation on a type

This will also enable more flexible notation: if Lean will see `3 † 2` it will
(i) Understand `†` as the function `?α → ?α → ?α` coming from a term `?t : Magma ?α` (where both
`?a` and `?t` are still to be determined)
(ii) Realise that `2` and `3` are terms of type `ℕ`, so `?α = ℕ`
(iii) It follows that `?t` must be a term of type `Magma ℕ`
(iv) Looking in the database, it will find the term `NatMagma : Magma ℕ` and it will understand
what `†` in this context mean.

Before moving to the examples, observe that with all good news there are also drawbacks: if we've
not been careful enough and we've recorded both `NatMagma` and `NatMagma'` as terms in `Magma ℕ`,
`Lean` will find both of them in the database and will (basically) randomly pick one or the other.
-/


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

instance TopOnMetric (X : Type*) [SpaceWithMetric X] : TopologicalSpace X := by
  have hX : Structures.SpaceWithMetric X := by
    fconstructor
    · exact d
    · exact SpaceWithMetric.dist_eq_zero
    · exact SpaceWithMetric.dist_pos
    · exact SpaceWithMetric.symm
    · exact SpaceWithMetric.triangle
  exact (Structures.metricToTopology X hX)

example : Continuous (fun (x : ℝ) ↦ x + 1) := continuous_add_right ..

example : Continuous (fun (⟨x, y⟩ : ℝ × ℝ) ↦ x + y) := continuous_add

example : Continuous (fun n : ℝ × ℝ ↦ (⟨n.2, n.1⟩ : (ℝ × ℝ))) := by
  simp_all only [continuous_prodMk]
  apply And.intro
  · apply continuous_snd
  · apply continuous_fst

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
    simp-- [SpaceWithMetric.triangle]
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

example (X Y : Type*) [SpaceWithMetric X] [SpaceWithMetric Y] : TopologicalSpace (X × Y) :=
  inferInstance

example : Continuous (fun n : ℝ × ℝ ↦ (⟨n.2, n.1⟩ : (ℝ × ℝ))) := by
  rw [continuous_prodMk]
  apply And.intro
  · apply continuous_snd
  · apply continuous_fst

#synth TopologicalSpace ℝ

instance : SpaceWithMetric ℝ where
__ := Structures.RealMetric

#synth TopologicalSpace ℝ

example : Continuous (fun (x : ℝ) ↦ x + 1) := continuous_add_right ..


#synth SpaceWithMetric (ℝ × ℝ)
instance ProdRealTop : TopologicalSpace (ℝ × ℝ) := @TopOnMetric _ (MetricOnProd ℝ ℝ)
#synth TopologicalSpace (ℝ × ℝ)

example : Continuous (fun n : ℝ × ℝ ↦ (⟨n.2, n.1⟩ : (ℝ × ℝ))) := by
  rw [continuous_prodMk]
  apply And.intro
  · apply continuous_snd
  · apply continuous_fst

end Classes
