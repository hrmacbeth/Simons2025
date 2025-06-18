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

Chapter 3, problems 13-17: Groups of permutations of `ℂ`, part 1
-/

lftcm_init
noncomputable section

open Equiv
open Complex (I exp exp_add exp_zero re im)

/-! ## Problem 13 -/

/-- Any distance-preserving transformation is called an *isometry*. -/
def IsIsometry (α : ℂ → ℂ) : Prop :=
  ∀ z w, ‖α z - α w‖ = ‖z - w‖

/-- Let `α` denote the function `z ↦ z + 2 * I` as a transformation of `ℂ`. For any two points of
the plane `z` and `w`, compare the values of `z - w` and `α z - w z`. -/
example :
    let α := fun (z : ℂ) ↦ z + 2 * I
    ∀ z w, z - w = α z - α w := by
  sorry

/-- Let `α` denote the function `z ↦ z + 2 * I` as a transformation of `ℂ`. Show that `α` is an
isometry. -/
example :
    let α := fun (z : ℂ) ↦ z + 2 * I
    IsIsometry α := by
  sorry

/-! ## Problem 14 -/

abbrev translation (c : ℂ) : Perm ℂ where
  toFun := fun x ↦ x + c
  invFun := fun x ↦ x - c
  left_inv := by
    sorry
  right_inv := by
    sorry

/-- If, for some given complex number `c`, `α` is the element `z ↦ z + c` of `Perm ℂ`, prove that,
for any two complex numbers `z` and `w`, `z - w = α z - α w`. Such an element of `Perm ℂ` is called
a *translation* of `ℂ`. -/
example (c : ℂ) :
    let α := translation c
    ∀ z w, z - w = α z - α w := by
  sorry

abbrev tSubgroup : Subgroup (Perm ℂ) where
  carrier := { α | ∀ z w : ℂ, α z - α w = z - w }
  mul_mem' := by
    sorry
  one_mem' := by
    sorry
  inv_mem' := by
    sorry

notation "T" => tSubgroup

/-- If `a ∈ T` and `α 0 = c`, prove that `α z = z + c`. -/
theorem eq_translation_of_mem_tSubgroup {α : Perm ℂ} (hα : α ∈ T) {c : ℂ} (hα0 : α 0 = c) :
    α = translation c := by
  sorry

/-- `T` consists entirely of translations of `ℂ`. -/
example (α : Perm ℂ) : α ∈ T ↔ ∃ c, α = translation c := by
  sorry

/-! ## Problem 15 -/

/-- rotation through an angle `θ` about the centre `0`. -/
abbrev rotation (θ : ℝ) : Perm ℂ where
  toFun := fun z ↦ exp (I * θ) * z
  invFun := fun z ↦ exp (-I * θ) * z
  left_inv := by
    sorry
  right_inv := by
    sorry

/-- rotations about `0` are isometries of the plane. -/
theorem isIsometry_rotation (θ : ℝ) : IsIsometry (rotation θ) := by
  sorry

/-! ## Problem 16 -/

/-- Show that the isometries form a subgroup of `Perm ℂ`. -/
abbrev isometrySubgroup : Subgroup (Perm ℂ) where
  carrier := { α | IsIsometry α }
  mul_mem' := by
    sorry
  one_mem' := by
    sorry
  inv_mem' := by
    sorry

notation "E" => isometrySubgroup

/-- Show that `E` contains the translation group. -/
example : T ≤ E := by
  sorry

/-! ## Problem 17 -/
section

/-- Complex conjugation is an isometry. -/
abbrev reflectReal : Perm ℂ where
  toFun := conj
  invFun := conj
  left_inv := by
    sorry
  right_inv := by
    sorry

/-- Let `α` denote complex conjugation. -/
local notation "α" => reflectReal

/-- Identify the line of fixed points of complex conjugation. -/
example : { z | α z = z } = { z : ℂ | z.im = 0 } := by
  sorry

/-- For a point `p`, the line of fixed points of `α` is the perpendicular bisector of `p` and its
image under `α`. -/
example (p w : ℂ) (hw : w ∈ { z | α z = z }) : ‖p - w‖ = ‖α p - w‖ := by
  sorry

/-- `α` is an isometry. -/
theorem isIsometry_reflectReal : IsIsometry α := by
  sorry

/-- `α` fixes the points 0 and 1. -/
example : α 0 = 0 ∧ α 1 = 1 := by
  sorry

end

