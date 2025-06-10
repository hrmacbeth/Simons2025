/-
Copyright (c) 2025 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Analysis.Complex.Circle
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

/-!
*Groups: A Path to Geometry*, by R. P. Burn

Chapter 3, problems 13-38: Groups of permutations of `ℂ`
-/

noncomputable section

-- FIXME
attribute [-simp] ne_eq

-- FIXME
attribute [-simp] add_sub_cancel_right add_tsub_cancel_right sub_add_cancel add_sub_add_right_eq_sub
  sub_add_cancel_right

set_option linter.style.multiGoal false

open Equiv
open ComplexConjugate
open Complex (I exp exp_add exp_zero re im)
open MulAction hiding toSMul

/-! ## Problem 13 -/

/-- Any distance-preserving transformation is called an isometry. -/
def IsIsometry (α : ℂ → ℂ) : Prop :=
  ∀ z w, ‖α z - α w‖ = ‖z - w‖

/-- Let `α` denote the function `z ↦ z + 2 * I` as a transformation of `ℂ`. For any two points of
the plane `z` and `w`, compare the values of `z - w` and `α z - w z`. -/
theorem aux1 :
    let α := fun (z : ℂ) ↦ z + 2 * I
    ∀ z w, z - w = α z - α w := by
  intro α z w
  dsimp [α]
  ring

/-- Let `α` denote the function `z ↦ z + 2 * I` as a transformation of `ℂ`. Show that `α` is an
isometry. -/
example :
    let α := fun (z : ℂ) ↦ z + 2 * I
    IsIsometry α := by
  intro α z w
  rw [aux1 z w]

/-! ## Problem 14 -/

abbrev translation (c : ℂ) : Perm ℂ where
  toFun := fun x ↦ x + c
  invFun := fun x ↦ x - c
  left_inv := by
    intro y
    dsimp
    ring
  right_inv := by
    intro y
    dsimp
    ring

/-- If, for some given complex number `c`, `α` is the element `z ↦ z + c` of `Perm ℂ`, prove that,
for any two complex numbers `z` and `w`, `z - w = α z - α w`. Such an element of `Perm ℂ` is called
a *translation* of `ℂ`. -/
theorem aux2 (c : ℂ) :
    let α := translation c
    ∀ z w, z - w = α z - α w := by
  intro α z w
  dsimp [α]
  ring

abbrev tSubgroup : Subgroup (Perm ℂ) where
  carrier := { α | ∀ z w : ℂ, α z - α w = z - w }
  mul_mem' := by
    intro α β hα hβ
    dsimp at *
    intro z w
    rw [hα]
    rw [hβ]
  one_mem' := by
    dsimp at *
    intro z w
    rfl
  inv_mem' := by
    intro α hα
    dsimp at *
    intro z w
    rw [← hα]
    -- rw?
    rw [@Perm.apply_inv_self]
    rw [@Perm.apply_inv_self]

notation "T" => tSubgroup

/-- If `a ∈ T` and `α 0 = c`, prove that `α z = z + c`. -/
theorem aux3 {α : Perm ℂ} (hα : α ∈ T) {c : ℂ} (hα0 : α 0 = c) : α = translation c := by
  change ∀ _, _ at hα
  ext z
  dsimp
  specialize hα z 0
  rw [hα0] at hα
  linear_combination hα

/-- `T` consists entirely of translations of `ℂ`. -/
example (α : Perm ℂ) : α ∈ T ↔ ∃ c, α = translation c := by
  constructor
  · intro h
    apply aux3 at h
    use α 0
    specialize @h (α 0) rfl
    exact h
  · intro h
    obtain ⟨c, hc⟩ := h
    rw [hc]
    change ∀ _, _ -- FIXME
    intro z w
    rw [← aux2]

/-! ## Problem 15 -/

/-- rotation through an angle `θ` about the centre `0`. -/
abbrev rotation (θ : ℝ) : Perm ℂ where
  toFun := fun z ↦ exp (I * θ) * z
  invFun := fun z ↦ exp (-I * θ) * z
  left_inv := by
    intro z
    dsimp
    trans (exp (-I * θ) * exp (I * θ)) * z
    · ring
    rw [← exp_add]
    trans exp 0 * z
    · ring_nf
    rw [exp_zero]
    ring
  right_inv := by
    intro z
    dsimp
    trans (exp (I * θ) * exp (-I * θ)) * z
    · ring
    rw [← exp_add]
    trans exp 0 * z
    · ring_nf
    rw [exp_zero]
    ring

/-- rotations about `0` are isometries of the plane. -/
example (θ : ℝ) : IsIsometry (rotation θ) := by
  intro z w
  dsimp
  trans ‖exp (θ * I) * (z - w)‖
  · ring_nf
  · rw [norm_mul]
    rw [Complex.norm_exp_ofReal_mul_I] -- FIXME need a comm version?
    ring

/-! ## Problem 16 -/

/-- Show that the isometries form a subgroup of `Perm ℂ`. -/
abbrev isometrySubgroup : Subgroup (Perm ℂ) where
  carrier := { α | IsIsometry α }
  mul_mem' := by
    intro α β hα hβ
    unfold IsIsometry at *
    dsimp at *
    intro x y
    rw [hα]
    rw [hβ]
  one_mem' := by
    unfold IsIsometry at *
    dsimp at *
    intro x y
    rfl
  inv_mem' := by
    intro α hα
    unfold IsIsometry at *
    dsimp at *
    intro x y
    rw [← hα]
    -- rw?
    rw [@Perm.apply_inv_self]
    rw [@Perm.apply_inv_self]

notation "E" => isometrySubgroup

/-- Show that `E` contains the translation group. -/
example : T ≤ E := by
  intro α hα
  change ∀ _, _ at hα -- FIXME
  change IsIsometry _ -- FIXME
  dsimp [IsIsometry]
  intro z w
  rw [hα]

/-! ## Problem 17 -/
section

/-- Complex conjugation is an isometry. -/
abbrev reflectReal : Perm ℂ where
  toFun := conj -- FIXME display
  invFun := conj
  left_inv := by
    intro z
    rw [@Complex.conj_conj]
  right_inv := by
    intro z
    rw [@Complex.conj_conj]

/-- Let `α` denote complex conjugation. -/
notation "α" => reflectReal

/-- Identify the line of fixed points of complex conjugation. -/
example : { z | α z = z } = { z : ℂ | z.im = 0 } := by
  ext z
  dsimp
  constructor
  · intro h
    -- `cify`
    suffices (z.im : ℂ) = 0 from mod_cast this
    rw [Complex.im_eq_sub_conj]
    linear_combination - h / 2 / I
  · intro h
    -- `cify` at `h`
    have h : (z.im : ℂ) = 0 := mod_cast h
    rw [Complex.im_eq_sub_conj] at h
    linear_combination (norm := skip) -2 * I * h
    have : 2 * I ≠ 0 := sorry
    field_simp
    ring

/-- For a point `p`, the line of fixed points of `α` is the perpendicular bisector of `p` and its
image under `α`. -/
example (p w : ℂ) (hw : w ∈ { z | α z = z }) : ‖p - w‖ = ‖α p - w‖ := by
  dsimp at hw
  trans ‖α (p - w)‖
  · dsimp
    rw [Complex.norm_conj]
  · dsimp
    rw [map_sub, hw]

/-- `α` is an isometry fixing the points 0 and 1. -/
example : IsIsometry α ∧ α 0 = 0 ∧ α 1 = 1 := by
  dsimp [IsIsometry]
  constructor
  · intro z w
    trans ‖α (z - w)‖
    · dsimp
      rw [map_sub]
    · dsimp
      rw [Complex.norm_conj]
  constructor
  · rw [map_zero]
  · rw [map_one]

end
