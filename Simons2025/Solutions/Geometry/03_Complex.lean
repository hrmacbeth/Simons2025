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
  -- sorry --
  dsimp [IsIsometry] at hα
  have hz0' := hα z 0
  rw [hα0] at hz0'
  have hz1' := hα z 1
  rw [hα1] at hz1'
  ring_nf at hz0' -- optional
  apply_fun (· ^ 2) at hz0' hz1'
  cify at hz0' hz1'
  rw [← mul_conj', ← mul_conj'] at *
  rw [map_sub, map_sub, map_one] at hz1'
  have H : (α z - z) * (α z - conj z) = 0 := by
    linear_combination (α z - 1) * hz0' - α z * hz1'
  rw [mul_eq_zero] at H
  obtain H | H := H
  · left
    linear_combination H
  · right
    linear_combination H
  -- sorry --

/-- Deduce that every point on the real axis is fixed by `α`. -/
example {α : Perm ℂ} (hα : α ∈ E) (hα0 : α 0 = 0) (hα1 : α 1 = 1) {z : ℂ} (hz0 : z ≠ 0)
    (hz1 : z ≠ 1) (hz : z.im = 0) : α z = z := by
  -- sorry --
  have H := IsIsometry.eq_self_or_conj hα hα0 hα1 z hz0 hz1
  obtain H | H := H
  · rw [H]
  · rw [H]
    cify at hz
    rw [im_eq_sub_conj] at hz
    linear_combination (norm := skip) -2 * I * hz
    field_simp
    ring
  -- sorry --

/-- If `α z = conj z ≠ z`, and `α w = w`, deduce that `w` is real. -/
theorem IsIsometry.aux {α : Perm ℂ} (hα : α ∈ E) {z w : ℂ} (hz : α z = conj z) (hz' : conj z ≠ z)
    (hw : α w = w) : w.im = 0 := by
  -- `‖z - w‖ = ‖conj z - w‖`, so that `w` lies on the perpendicular bisector of `z` and `conj z`
  have H : ‖conj z - w‖ = ‖z - w‖ := by
    -- sorry --
    have H := hα z w
    rw [hz] at H
    rw [hw] at H
    exact H
    -- sorry --
  -- now finish off
  -- sorry --
  apply_fun (· ^ 2) at H
  cify at H
  rw [← mul_conj', ← mul_conj'] at H
  rw [map_sub, map_sub, conj_conj] at H
  have H' : - (z - conj z) * (w - conj w) = 0 := by linear_combination H
  rw [mul_eq_zero] at H'
  obtain H1 | H2 := H'
  · have : conj z = z := by linear_combination H1
    rw [this] at hz'
    contradiction
  · have : conj w = w := by linear_combination -H2
    cify
    rw [im_eq_sub_conj, this]
    ring
  -- sorry --

/-- Deduce that either `α z = z` for all `z`, or `α z = conj z` for all `z`. -/
theorem IsIsometry.eq_id_or_conj {α : Perm ℂ} (hα : α ∈ E) (hα0 : α 0 = 0) (hα1 : α 1 = 1) :
    (∀ z, α z = z) ∨ (∀ z, α z = conj z) := by
  -- sorry --
  by_cases h : ∀ z, conj z = z ∨ α z = z
  · left
    intro z
    specialize h z
    -- adjust your earlier proofs so these sorries not needed!
    have h' := IsIsometry.eq_self_or_conj hα hα0 hα1 z sorry sorry
    by_cases hz' : α z = z
    · exact hz'
    · have h1 : α z = conj z := by tauto
      have h2 : conj z = z := by tauto
      rw [h1, h2]
  · right
    push_neg at h
    obtain ⟨z, hz, hz'⟩ := h
    have h' := IsIsometry.eq_self_or_conj hα hα0 hα1 z sorry sorry -- ditto
    have h'' : α z = conj z := by tauto
    intro w
    obtain H1 | H2 := IsIsometry.eq_self_or_conj hα hα0 hα1 w sorry sorry -- ditto
    · rw [H1]
      have := IsIsometry.aux hα h'' hz H1
      cify at this
      rw [im_eq_sub_conj] at this
      linear_combination (norm := skip) 2 * I * this
      field_simp
    · exact H2
  -- sorry --

theorem IsIsometry.eq_one_or_reflectReal {α : Perm ℂ} (hα : α ∈ E) (hα0 : α 0 = 0) (hα1 : α 1 = 1) :
    α = 1 ∨ α = reflectReal := by
  -- sorry --
  obtain h1 | h2 := IsIsometry.eq_id_or_conj hα hα0 hα1
  · left
    ext z
    exact h1 z
  · right
    ext z
    exact h2 z
  -- sorry --

/-! ## Problem 19 -/

/-- Let `α` be an isometry stabilizing `0`. Show that for some `θ` either `α` is
`z ↦ exp (I * θ) * z` or `α` is `z ↦ exp (I * θ) * conj z`.-/
example {α : Perm ℂ} (hα : α ∈ E) (hα0 : α 0 = 0) :
    ∃ θ : ℝ, α = rotation θ ∨ α = rotation θ * reflectReal := by
  -- Prove that `‖α 1‖ = 1`.
  have H : ‖α 1‖ = 1 := by
  -- sorry --
    dsimp [IsIsometry] at hα
    specialize hα 1 0
    rw [hα0] at hα
    convert hα using 2
    · ring
    · norm_num
    -- sorry --
  -- Deduce that `α 1 = exp (I * θ)` for some `θ`.
  have H2 : ∃ θ : ℝ, α 1 = exp (I * θ) := by
    -- sorry --
    use (log (α 1)).im
    calc
      α 1 = exp (log (α 1)) := by
          rw [Complex.exp_log]
          rw [← norm_ne_zero_iff, H]
          norm_num
      _ = exp ((log (α 1)).re + (log (α 1)).im * I) := by rw [re_add_im]
      _ = exp (I * (log (α 1)).im) := by
          congr
          rw [Complex.log_re, H, Real.log_one]
          push_cast
          ring
    -- sorry --
  obtain ⟨θ, hθ⟩ := H2
  use θ
  -- If `β` is the transformation `z ↦ exp (I * θ) * z`, show that `β⁻¹ ∘ α` fixes both `0` and `1`.
  let β := rotation θ
  have hβ0 : (β⁻¹ * α) 0 = 0 := by
    -- sorry --
    dsimp [β]
    rw [@Perm.inv_def]
    dsimp
    rw [hα0]
    ring
    -- sorry --
  have hβ1 : (β⁻¹ * α) 1 = 1 := by
    -- sorry --
    dsimp [β]
    rw [@Perm.inv_def]
    dsimp
    rw [hθ, ← exp_add]
    ring_nf
    rw [exp_zero]
    -- sorry --
  -- now finish off
  -- sorry --
  have : β⁻¹ * α ∈ E := by
    apply mul_mem
    · apply inv_mem
      dsimp [β]
      apply isIsometry_rotation
    apply hα
  obtain H1 | H2 := IsIsometry.eq_one_or_reflectReal (α := β⁻¹ * α) this hβ0 hβ1
  · left
    have H1' := congr(β * $H1)
    convert H1'
    group
  · right
    have H2' := congr(β * $H2)
    convert H2'
    group
  -- sorry --

/-! ## Problem 20 -/

/-- For any real number `r` find the image of the complex number `r * exp (I * θ / 2)` under the
isometry `α` defined to be `z ↦ exp (I * θ) * conj z`, and identify a line of fixed points of `α`.
-/
theorem apply_rotation_mul_reflectReal_eq_self (θ r : ℝ) :
    let α := rotation θ * reflectReal
    α (r * exp (I * θ / 2)) = r * exp (I * θ / 2) := by
  -- sorry --
  dsimp
  rw [map_mul, conj_ofReal, ← exp_conj, map_div₀, map_mul, conj_I, conj_ofReal, Complex.conj_ofNat]
  calc exp (I * θ) * (r * exp (-I * θ / 2)) = r * (exp (I * θ) * exp (-I * θ / 2)) := by ring
    _ = r * exp (I * θ + -I * θ / 2) := by rw [exp_add]
    _ = r * exp (I * θ / 2) := by ring_nf
  -- sorry --

/- Find the image of the complex number `r * exp (I * φ)` under the isometry `α` defined to be
`z ↦ exp (I * θ) * conj z`. -/
example (θ r φ : ℝ) :
    let α := rotation θ * reflectReal
    α (r * exp (I * φ)) = r * exp (I * (θ - φ)) := by
  -- sorry --
  dsimp
  rw [map_mul, conj_ofReal, ← exp_conj, map_mul, conj_I, conj_ofReal]
  calc exp (I * θ) * (r * exp (-I * φ)) = r * (exp (I * θ) * exp (-I * φ)) := by ring
    _ = r * exp (I * θ + -I * φ) := by rw [exp_add]
    _ = r * exp (I * (θ - φ)) := by ring_nf
  -- sorry --

/- Describe a point and its image under the isometry `α` (defined to be `z ↦ exp (I * θ) * conj z`)
in relation to the line of fixed points of `α`. -/
example (θ : ℝ) (z : ℂ) :
    let α := rotation θ * reflectReal
    ∀ r : ℝ, ‖α z - r * exp (I * θ / 2)‖ = ‖z - r * exp (I * θ / 2)‖ := by
  -- sorry --
  intro α
  have hα : α ∈ E := by
    apply mul_mem
    · apply isIsometry_rotation
    · apply isIsometry_reflectReal
  intro r
  have := hα z (r * exp (I * θ / 2))
  rw [apply_rotation_mul_reflectReal_eq_self θ r] at this
  exact this
  -- sorry --

/- Consider the isometry `α` defined to be  `z ↦ exp (I * θ) * conj z`. What is `α ^ 2`? -/
example (θ : ℝ) :
    let α := rotation θ * reflectReal
    α ^ 2 = 1 := by
  -- sorry --
  dsimp
  ext z
  rw [sq]
  dsimp [rotation, reflectReal]
  rw [map_mul, ← exp_conj, conj_conj, map_mul, conj_I, conj_ofReal]
  calc
    exp (I * θ) * (exp (-I * θ) * z) = (exp (I * θ) * exp (-I * θ)) * z := by ring
    _ = exp (I * θ + -I * θ) * z := by rw [exp_add]
    _ = exp 0 * z := by ring_nf
    _ = 1 * z := by rw [exp_zero]
    _ = z := by ring
  -- sorry --
