/-
Copyright (c) 2025 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Analysis.Complex.Circle
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Config.Environment

/-!
*Groups: A Path to Geometry*, by R. P. Burn

Chapter 3, problems 13-38: Groups of permutations of `ℂ`
-/

lftcm_init
noncomputable section

open Equiv
open Complex (I exp exp_add exp_zero re im)
open MulAction hiding toSMul

/-! ## Problem 13 -/

/-- Any distance-preserving transformation is called an *isometry*. -/
def IsIsometry (α : ℂ → ℂ) : Prop :=
  ∀ z w, ‖α z - α w‖ = ‖z - w‖

/-- Let `α` denote the function `z ↦ z + 2 * I` as a transformation of `ℂ`. For any two points of
the plane `z` and `w`, compare the values of `z - w` and `α z - w z`. -/
example :
    let α := fun (z : ℂ) ↦ z + 2 * I
    ∀ z w, z - w = α z - α w := by
  -- sorry --
  dsimp
  intro z w
  ring
  -- sorry --

/-- Let `α` denote the function `z ↦ z + 2 * I` as a transformation of `ℂ`. Show that `α` is an
isometry. -/
example :
    let α := fun (z : ℂ) ↦ z + 2 * I
    IsIsometry α := by
  -- sorry --
  dsimp
  intro z w
  dsimp
  ring_nf
  -- sorry --

/-! ## Problem 14 -/

abbrev translation (c : ℂ) : Perm ℂ where
  toFun := fun x ↦ x + c
  invFun := fun x ↦ x - c
  left_inv := by
    -- sorry --
    intro y
    dsimp
    ring
    -- sorry --
  right_inv := by
    -- sorry --
    intro y
    dsimp
    ring
    -- sorry --

/-- If, for some given complex number `c`, `α` is the element `z ↦ z + c` of `Perm ℂ`, prove that,
for any two complex numbers `z` and `w`, `z - w = α z - α w`. Such an element of `Perm ℂ` is called
a *translation* of `ℂ`. -/
example (c : ℂ) :
    let α := translation c
    ∀ z w, z - w = α z - α w := by
  -- sorry --
  intro α z w
  dsimp [α]
  ring
  -- sorry --

abbrev tSubgroup : Subgroup (Perm ℂ) where
  carrier := { α | ∀ z w : ℂ, α z - α w = z - w }
  mul_mem' := by
    -- sorry --
    intro α β hα hβ
    dsimp at *
    intro z w
    rw [hα]
    rw [hβ]
    -- sorry --
  one_mem' := by
    -- sorry --
    dsimp at *
    intro z w
    rfl
    -- sorry --
  inv_mem' := by
    -- sorry --
    intro α hα
    dsimp at *
    intro z w
    rw [← hα]
    -- rw?
    rw [@Perm.apply_inv_self]
    rw [@Perm.apply_inv_self]
    -- sorry --

notation "T" => tSubgroup

/-- If `a ∈ T` and `α 0 = c`, prove that `α z = z + c`. -/
theorem eq_translation_of_mem_tSubgroup {α : Perm ℂ} (hα : α ∈ T) {c : ℂ} (hα0 : α 0 = c) :
    α = translation c := by
  -- sorry --
  ext z
  dsimp at *
  specialize hα z 0
  rw [hα0] at hα
  linear_combination hα
  -- sorry --

/-- `T` consists entirely of translations of `ℂ`. -/
example (α : Perm ℂ) : α ∈ T ↔ ∃ c, α = translation c := by
  -- sorry --
  constructor
  · intro h
    apply eq_translation_of_mem_tSubgroup at h
    use α 0
    specialize @h (α 0) rfl
    exact h
  · intro h
    obtain ⟨c, hc⟩ := h
    rw [hc]
    dsimp
    intro z w
    ring
  -- sorry --

/-! ## Problem 15 -/

/-- rotation through an angle `θ` about the centre `0`. -/
abbrev rotation (θ : ℝ) : Perm ℂ where
  toFun := fun z ↦ exp (I * θ) * z
  invFun := fun z ↦ exp (-I * θ) * z
  left_inv := by
    -- sorry --
    intro z
    dsimp
    calc
      exp (-I * θ) * (exp (I * θ) * z) = (exp (-I * θ) * exp (I * θ)) * z := by ring
      _ = exp (-I * θ + I * θ) * z := by rw [exp_add]
      _ = exp 0 * z := by ring_nf
      _ = z := by
          rw [exp_zero]
          ring
    -- sorry --
  right_inv := by
    -- sorry --
    intro z
    dsimp
    calc
      exp (I * θ) * (exp (-I * θ) * z) = (exp (-I * θ) * exp (I * θ)) * z := by ring
      _ = exp (-I * θ + I * θ) * z := by rw [exp_add]
      _ = exp 0 * z := by ring_nf
      _ = z := by
          rw [exp_zero]
          ring
    -- sorry --

/-- rotations about `0` are isometries of the plane. -/
example (θ : ℝ) : IsIsometry (rotation θ) := by
  -- sorry --
  intro z w
  dsimp
  calc
    ‖exp (I * θ) * z - exp (I * θ) * w‖ = ‖exp (θ * I) * (z - w)‖ := by ring_nf
    _ = ‖z - w‖ := by
        rw [norm_mul]
        rw [Complex.norm_exp_ofReal_mul_I]
        ring
  -- sorry --

/-! ## Problem 16 -/

/-- Show that the isometries form a subgroup of `Perm ℂ`. -/
abbrev isometrySubgroup : Subgroup (Perm ℂ) where
  carrier := { α | IsIsometry α }
  mul_mem' := by
    -- sorry --
    intro α β hα hβ
    dsimp [IsIsometry] at *
    intro x y
    rw [hα]
    rw [hβ]
    -- sorry --
  one_mem' := by
    -- sorry --
    dsimp [IsIsometry] at *
    intro x y
    rfl
    -- sorry --
  inv_mem' := by
    -- sorry --
    intro α hα
    dsimp [IsIsometry] at *
    intro x y
    rw [← hα]
    -- rw?
    rw [@Perm.apply_inv_self]
    rw [@Perm.apply_inv_self]
    -- sorry --

notation "E" => isometrySubgroup

/-- Show that `E` contains the translation group. -/
example : T ≤ E := by
  -- sorry --
  dsimp
  intro α hα
  dsimp [IsIsometry]
  intro z w
  rw [hα]
  -- sorry --

/-! ## Problem 17 -/
section

/-- Complex conjugation is an isometry. -/
abbrev reflectReal : Perm ℂ where
  toFun := conj
  invFun := conj
  left_inv := by
    -- sorry --
    intro z
    rw [@Complex.conj_conj]
    -- sorry --
  right_inv := by
    -- sorry --
    intro z
    rw [@Complex.conj_conj]
    -- sorry --

/-- Let `α` denote complex conjugation. -/
local notation "α" => reflectReal

/-- Identify the line of fixed points of complex conjugation. -/
example : { z | α z = z } = { z : ℂ | z.im = 0 } := by
  -- sorry --
  ext z
  dsimp
  suffices _ ↔ (z.im : ℂ) = 0 from mod_cast this -- FIXME `cify`?
  rw [Complex.im_eq_sub_conj]
  constructor
  · intro h
    linear_combination - h / 2 / I
  · intro h
    linear_combination (norm := skip) -2 * I * h
    field_simp
    ring
  -- sorry --

/-- For a point `p`, the line of fixed points of `α` is the perpendicular bisector of `p` and its
image under `α`. -/
example (p w : ℂ) (hw : w ∈ { z | α z = z }) : ‖p - w‖ = ‖α p - w‖ := by
  -- sorry --
  dsimp at hw
  calc
    ‖p - w‖ = ‖α (p - w)‖ := by
        dsimp
        rw [Complex.norm_conj]
    _ = ‖α p - w‖ := by
        dsimp
        rw [map_sub, hw]
  -- sorry --

/-- `α` is an isometry fixing the points 0 and 1. -/
example : IsIsometry α ∧ α 0 = 0 ∧ α 1 = 1 := by
  -- sorry --
  dsimp [IsIsometry]
  constructor
  · intro z w
    calc
      ‖conj z - conj w‖ = ‖α (z - w)‖ := by
          dsimp
          rw [map_sub]
      _ = ‖z - w‖ := by
          dsimp
          rw [Complex.norm_conj]
  constructor
  · norm_num
  · norm_num
  -- sorry --

end
