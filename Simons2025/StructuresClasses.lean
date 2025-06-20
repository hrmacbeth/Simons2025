/-
Copyright (c) 2025 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio
-/
import Mathlib.Algebra.Notation.Defs
import Mathlib.Data.Int.Notation
import Mathlib.Data.Nat.BinaryRec
import Mathlib.Logic.Function.Defs
import Mathlib.Tactic.Simps.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Config.Environment

namespace Simons

section Structures

structure HasZero (X : Type*) where
  zero' : X

export HasZero (zero')

notation "𝟘" => zero' -- type `𝟘` as `\b0`.

def NatHasZero : HasZero ℕ where
  zero' := 0

def BoolHasZero : HasZero Bool := by
  use true

#check (𝟘 NatHasZero)

#check (𝟘 BoolHasZero)

structure Magma (X : Type*) where
  sum : X → X → X

export Magma (sum)

-- infixl:70 " † " => Magma.sum

def NatMagma : Magma ℕ := ⟨fun n m ↦ n + m⟩

def BoolMagma : Magma Bool where
 sum p q :=
  match p, q with
  | _, _ => false

def PropMagma : Magma Prop := { sum := And }

#eval NatMagma.sum 3 2

structure Monoid (X : Type*) extends HasZero X, Magma X where
  sum_assoc (x y z : X) : sum (sum x y) z = sum x (sum y z)

def NatMonoid : Monoid ℕ where
  zero' := 0
  sum := Nat.add
  sum_assoc := by
    intro n m l
    rw [Nat.add_eq]
    exact Nat.add_assoc n m l

def NatMonoid' : Monoid ℕ where
__ := NatHasZero
__ := NatMagma
sum_assoc n m l := by simpa [Nat.add_eq] using Nat.add_assoc ..

def NatMonoid'' : Monoid ℕ :=
{ NatHasZero, NatMagma with sum_assoc n m l := by simpa [Nat.add_eq] using Nat.add_assoc .. }

def PropMonoid : Monoid Prop where
  zero' := True
  __ := PropMagma
  sum_assoc p q r := by
    simp only [eq_iff_iff]
    exact and_assoc

def BoolMonoid : Monoid Bool :=
{ BoolHasZero, BoolMagma with
  sum_assoc p q r := by
    dsimp only [BoolMagma] }

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

structure SpaceWithMetric (X : Type) where
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

structure MagmaHom (X Y : Type) (hX : Magma X) (hY : Magma Y) where
  toFun : X → Y
  addFun (x y : X) : toFun (sum hX x y) = sum hY (toFun x) (toFun y)

def RealMagma: Magma ℝ := by --{sum := @Add.add ℝ _}
  constructor
  intro x y
  exact x + y

def coeMagmaHom : MagmaHom ℕ ℝ (NatMagma) (RealMagma) where
  toFun := (↑)
  addFun a b := Nat.cast_add a b

end Structures


section Classes

end Classes


end Simons
