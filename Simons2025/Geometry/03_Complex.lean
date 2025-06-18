/-
Copyright (c) 2025 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Simons2025.Geometry.«02_Complex»

/-!
*Groups: A Path to Geometry*, by R. P. Burn

Chapter 3, problems 18-20: Groups of permutations of `ℂ`, part 2
-/

lftcm_init
noncomputable section

open Equiv
open Complex (I re im im_eq_sub_conj re_add_im mul_conj' conj_I conj_im conj_conj conj_ofReal
  exp_conj exp exp_add exp_zero log)

/-! ## Problem 18 -/

#check mul_conj'

/--
Let `α` be an isometry which stabilises both `0` and `1`. Let `z` be any point of the plane distinct
from both `0` and `1`. Where are the possible images of `z`? -/
theorem IsIsometry.eq_self_or_conj {α : Perm ℂ} (hα : α ∈ E) (hα0 : α 0 = 0) (hα1 : α 1 = 1) (z : ℂ)
    (hz0 : z ≠ 0) (hz1 : z ≠ 1) : α z = z ∨ α z = conj z := by
  sorry

/-- Deduce that every point on the real axis is fixed by `α`. -/
example {α : Perm ℂ} (hα : α ∈ E) (hα0 : α 0 = 0) (hα1 : α 1 = 1) {z : ℂ} (hz0 : z ≠ 0)
    (hz1 : z ≠ 1) (hz : z.im = 0) : α z = z := by
  sorry

/-- If `α z = conj z ≠ z`, and `α w = w`, deduce that `w` is real. -/
theorem IsIsometry.aux {α : Perm ℂ} (hα : α ∈ E) {z w : ℂ} (hz : α z = conj z) (hz' : conj z ≠ z)
    (hw : α w = w) : w.im = 0 := by
  -- `‖z - w‖ = ‖conj z - w‖`, so that `w` lies on the perpendicular bisector of `z` and `conj z`
  have H : ‖conj z - w‖ = ‖z - w‖ := by
    sorry
  -- now finish off
  sorry

/-- Deduce that either `α z = z` for all `z`, or `α z = conj z` for all `z`. -/
theorem IsIsometry.eq_id_or_conj {α : Perm ℂ} (hα : α ∈ E) (hα0 : α 0 = 0) (hα1 : α 1 = 1) :
    (∀ z, α z = z) ∨ (∀ z, α z = conj z) := by
  sorry

theorem IsIsometry.eq_one_or_reflectReal {α : Perm ℂ} (hα : α ∈ E) (hα0 : α 0 = 0) (hα1 : α 1 = 1) :
    α = 1 ∨ α = reflectReal := by
  sorry

/-! ## Problem 19 -/

/-- Let `α` be an isometry stabilizing `0`. Show that for some `θ` either `α` is
`z ↦ exp (I * θ) * z` or `α` is `z ↦ exp (I * θ) * conj z`.-/
example {α : Perm ℂ} (hα : α ∈ E) (hα0 : α 0 = 0) :
    ∃ θ : ℝ, α = rotation θ ∨ α = rotation θ * reflectReal := by
  -- Prove that `‖α 1‖ = 1`.
  have H : ‖α 1‖ = 1 := by
    sorry
  -- Deduce that `α 1 = exp (I * θ)` for some `θ`.
  have H2 : ∃ θ : ℝ, α 1 = exp (I * θ) := by
    sorry
  obtain ⟨θ, hθ⟩ := H2
  use θ
  -- If `β` is the transformation `z ↦ exp (I * θ) * z`, show that `β⁻¹ ∘ α` fixes both `0` and `1`.
  let β := rotation θ
  have hβ0 : (β⁻¹ * α) 0 = 0 := by
    sorry
  have hβ1 : (β⁻¹ * α) 1 = 1 := by
    sorry
  -- now finish off
  sorry

/-! ## Problem 20 -/

/-- For any real number `r` find the image of the complex number `r * exp (I * θ / 2)` under the
isometry `α` defined to be `z ↦ exp (I * θ) * conj z`, and identify a line of fixed points of `α`.
-/
theorem apply_rotation_mul_reflectReal_eq_self (θ r : ℝ) :
    let α := rotation θ * reflectReal
    α (r * exp (I * θ / 2)) = r * exp (I * θ / 2) := by
  sorry

/- Find the image of the complex number `r * exp (I * φ)` under the isometry `α` defined to be
`z ↦ exp (I * θ) * conj z`. -/
example (θ r φ : ℝ) :
    let α := rotation θ * reflectReal
    α (r * exp (I * φ)) = r * exp (I * (θ - φ)) := by
  sorry

/- Describe a point and its image under `α` in relation to the line of fixed points of the isometry
`α` defined to be  `z ↦ exp (I * θ) * conj z`. -/
example (θ : ℝ) (z : ℂ) :
    let α := rotation θ * reflectReal
    ∀ r : ℝ, ‖α z - r * exp (I * θ / 2)‖ = ‖z - r * exp (I * θ / 2)‖ := by
  sorry

/- Consider the isometry `α` defined to be  `z ↦ exp (I * θ) * conj z`. What is `α ^ 2`? -/
example (θ : ℝ) :
    let α := rotation θ * reflectReal
    α ^ 2 = 1 := by
  sorry

