/-
Copyright (c) 2025 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib
import Config.Environment

/-!
*Groups: A Path to Geometry*, by R. P. Burn

Chapter 3, problems 1-5: Groups of permutations of `ℝ`
-/

lftcm_init
noncomputable section

open Equiv
open MulAction hiding toSMul

/-! ## Problem 1 -/

abbrev addRight (a : ℝ) : Perm ℝ where
  toFun := fun x ↦ x + a
  invFun := fun x ↦ x - a
  left_inv := by
    -- sorry --
    dsimp [Function.LeftInverse]
    intro y
    ring
    -- sorry --
  right_inv := by
    -- sorry --
    dsimp [Function.RightInverse, Function.LeftInverse]
    intro y
    ring
    -- sorry --

/-- If, for some given real number `a`, `α` is the element `x ↦ x + a` of `Perm ℝ`, prove that, for
any two real numbers `x` and `y`, `x - y = α x - α y`. -/
example (a : ℝ) :
    let α := addRight a
    ∀ x y, x - y = α x - α y := by
  -- sorry --
  dsimp
  intro x y
  ring
  -- sorry --

/-- An element `α` of `Perm ℝ` such that, for any two real numbers `x` and `y`, `x - y = α x - α y`,
is called a *translation* of `ℝ`. -/
def IsTranslation (α : Perm ℝ) : Prop :=
  ∀ x y : ℝ, α x - α y = x - y

/-- Show that the translations form a subgroup of `Perm ℝ`. -/
abbrev translationSubgroup : Subgroup (Perm ℝ) where
  carrier := { α | IsTranslation α }
  mul_mem' := by
    -- sorry --
    intro α β hα hβ
    dsimp [IsTranslation] at hα hβ ⊢
    intro x y
    rw [hα]
    rw [hβ]
    -- sorry --
  one_mem' := by
    -- sorry --
    dsimp [IsTranslation]
    intro x y
    rfl
    -- sorry --
  inv_mem' := by
    -- sorry --
    intro α hα
    dsimp [IsTranslation] at hα ⊢
    intro x y
    rw [← hα]
    -- rw?
    rw [@Perm.apply_inv_self]
    rw [@Perm.apply_inv_self]
    -- sorry --

notation "T" => translationSubgroup

/-- If `α ∈ T` and `α 0 = 0`, prove that `α x = x + a`. -/
example {α : Perm ℝ} (hα : α ∈ T) {a : ℝ} (h : α 0 = a) : α = addRight a := by
  -- sorry --
  ext x
  dsimp
  dsimp [IsTranslation] at hα
  specialize hα x 0
  rw [h] at hα
  linear_combination hα
  -- sorry --

/-! ## Problem 2 -/

abbrev halfTurn (a : ℝ) : Perm ℝ where
  toFun := fun x ↦ -x + a
  invFun := fun x ↦ -x + a
  left_inv := by
    -- sorry --
    intro x
    dsimp
    ring
    -- sorry --
  right_inv := by
    -- sorry --
    intro x
    dsimp
    ring
    -- sorry --

/-- If for some real number `a`, `α` is the element `x ↦ - x + a` of `Perm ℝ`, prove that for any
two real numbers `x`, `-(x - y) = α x - α y`. -/
example (a : ℝ) :
    let α := halfTurn a
    ∀ x y, -(x - y) = α x - α y := by
  -- sorry --
  dsimp
  intro x y
  ring
  -- sorry --

/-- Find the fixed point of `α`. -/
example (a : ℝ) :
    let α := halfTurn a
    { x | α x = x } = {a / 2} := by
  -- sorry --
  dsimp
  ext x
  dsimp
  constructor
  · intro h
    linear_combination -h/2
  · intro h
    linear_combination -2*h
  -- sorry --

/-- An element `α` of `Perm ℝ` which preserves absolute values of lengths is an *isometry* of `ℝ`.
-/
def IsIsometry (α : Perm ℝ) : Prop :=
  ∀ x y : ℝ, |α x - α y| = |x - y|

/-- Show that the isometries form a subgroup of `Perm ℝ`. -/
abbrev isometrySubgroup : Subgroup (Perm ℝ) where
  carrier := { α | IsIsometry α }
  mul_mem' := by
    -- sorry --
    intro α β hα hβ
    dsimp [IsIsometry] at hα hβ ⊢
    intro x y
    rw [hα]
    rw [hβ]
    -- sorry --
  one_mem' := by
    -- sorry --
    dsimp [IsIsometry]
    intro x y
    rfl
    -- sorry --
  inv_mem' := by
    -- sorry --
    intro α hα
    dsimp [IsIsometry] at hα ⊢
    intro x y
    rw [← hα]
    -- rw?
    rw [@Perm.apply_inv_self]
    rw [@Perm.apply_inv_self]
    -- sorry --

notation "M" => isometrySubgroup

/-- Does `M` contain the translation group of `ℝ`? -/
example : T ≤ M := by
  -- sorry --
  dsimp
  intro α hα
  dsimp [IsIsometry]
  dsimp [IsTranslation] at hα
  intro x y
  rw [hα]
  -- sorry --

/-- Does `M` contain the half-turns of `ℝ`? -/
example (a : ℝ) : halfTurn a ∈ M := by
  -- sorry --
  intro x y
  dsimp
  trans |-(x - y)|
  · ring_nf
  · rw [abs_neg]
  -- sorry --

/-- If `α ∈ M` and `α 0 = 5`, what can `α 2` be? -/
example {α : Perm ℝ} (hα : α ∈ M) (h : α 0 = 5) : α 2 ∈ {3, 7} := by
  -- sorry --
  dsimp
  dsimp [IsIsometry] at hα
  specialize hα 2 0
  rw [h] at hα
  norm_num at hα
  apply eq_or_eq_neg_of_abs_eq at hα
  obtain hα | hα := hα
  · right
    linear_combination hα
  · left
    linear_combination hα
  -- sorry --

/-- If `α ∈ M` and `α 0 = 5`, what can `α x` be? -/
example {α : Perm ℝ} (hα : α ∈ M) (h : α 0 = 5) (x : ℝ) : α x ∈ {5 - x, 5 + x} := by
  -- sorry --
  dsimp
  dsimp [IsIsometry] at hα
  specialize hα x 0
  rw [h] at hα
  norm_num at hα
  rw [abs_eq_abs] at hα
  obtain hα | hα := hα
  · right
    linear_combination hα
  · left
    linear_combination hα
  -- sorry --

/-- If `α ∈ M` and `α 0 = a`, prove that for all `x`, `α x = ± x + a`. -/
theorem IsIsometry.eval_of_eval_zero {α : Perm ℝ} (hα : α ∈ M) {a : ℝ} (h : α 0 = a) (x : ℝ) :
    α x ∈ {- x + a, x + a} := by
  -- sorry --
  dsimp
  dsimp [IsIsometry] at hα
  specialize hα x 0
  rw [h] at hα
  norm_num at hα
  rw [abs_eq_abs] at hα
  obtain hα | hα := hα
  · right
    linear_combination hα
  · left
    linear_combination hα
  -- sorry --

/- If, for given `α`, `α x = x + a` and `α y = - y + a`, prove that `|x - y| = |x + y|` and
deduce that `x` or `y` is zero. -/
theorem IsIsometry.aux {α : Perm ℝ} (hα : α ∈ M) {a x : ℝ} (hx : α x = x + a) {y : ℝ}
    (hy : α y = -y + a) :
    x = 0 ∨ y = 0 := by
  -- sorry --
  dsimp [IsIsometry] at hα
  specialize hα x y
  rw [hx, hy] at hα
  have H : |x - y| = |x + y| := by
    rw [← hα]
    ring_nf
  rw [abs_eq_abs] at H
  obtain H | H := H
  · right
    linear_combination -H/2
  · left
    linear_combination H/2
  -- sorry --

/-- If `α ∈ M` and `α 0 = a`, prove that `α` is either a half-turn or a translation. -/
theorem IsIsometry.eq_addRight_or_eq_halfTurn {α : Perm ℝ} (hα : α ∈ M) {a : ℝ} (h : α 0 = a) :
    α = addRight a ∨ α = halfTurn a := by
  -- sorry --
  have H := IsIsometry.eval_of_eval_zero hα h
  dsimp at H
  by_cases h1 : ∀ x ≠ 0, α x = halfTurn a x
  · right
    ext x
    by_cases hx : x = 0
    · dsimp
      rw [hx, h]
      ring
    apply h1 at hx
    exact hx
  push_neg at h1
  obtain ⟨x, hx₀, hx⟩ := h1
  have hx : α x = x + a := by
    specialize H x
    tauto
  apply IsIsometry.aux hα at hx
  left
  ext y
  specialize H y
  obtain H | H := H
  · apply hx at H
    obtain hx | hy := H
    · contradiction
    · dsimp
      rw [hy, h]
      ring
  · rw [H]
    dsimp
  -- sorry --

/-- If `α ∈ M`, prove that `α` is either a half-turn or a translation. -/
example {α : Perm ℝ} (hα : α ∈ M) : ∃ a, α = addRight a ∨ α = halfTurn a := by
  -- sorry --
  use α 0
  apply IsIsometry.eq_addRight_or_eq_halfTurn hα
  rfl
  -- sorry --

/-! ## Problem 3 -/

/-- Find the fixed point of `x ↦ 2 * x - 1`. -/
example :
    let α := fun (x:ℝ) ↦ 2 * x - 1
    { x | α x = x } = {1} := by
  -- sorry --
  dsimp
  ext x
  dsimp
  constructor
  · intro H
    linear_combination H
  · intro H
    linear_combination H
  -- sorry --

/-- If `α` is `x ↦ a * x + b` and `a ≠ 0, 1`, find the fixed point of `α`. -/
example (a b : ℝ) (ha : a ≠ 0) (ha' : a ≠ 1) :
    let α := fun x ↦ a * x + b
    { x | α x = x } = {- b / (a - 1)} := by
  -- sorry --
  dsimp
  ext x
  dsimp
  have ha'' : a - 1 ≠ 0 := by
    contrapose! ha'
    linear_combination ha'
  field_simp
  constructor
  · intro H
    linear_combination H
  · intro H
    linear_combination H
  -- sorry --

/-- If `α` is the element `x ↦ a * x + b` of `Perm ℝ` and `a ≠ 0`, compare the ratio
`(x - y) / (x - z)` with the ratio `(α x - α y) / (α x - α z)` for any three distinct real numbers
`x`, `y` and `z`. -/
example (a b : ℝ) (ha : a ≠ 0) {x y z : ℝ} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    let α := fun x ↦ a * x + b
    (x - y) / (x - z) = (α x - α y) / (α x - α z) := by
  -- sorry --
  dsimp
  have : x - z ≠ 0 := by
    contrapose! hxz
    linear_combination hxz
  have : (a * x + b) - (a * z + b) ≠ 0 := by
    contrapose! hxz
    linear_combination (norm := skip) hxz / a
    field_simp
    ring
  field_simp
  ring
  -- sorry --

/-- A transformation which preserves ratios of lengths on the real line is called a *similarity* of
the real line. -/
def IsSimilarity (α : Perm ℝ) : Prop :=
  ∀ {x y z : ℝ} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z),
    (x - y) / (x - z) = (α x - α y) / (α x - α z)

/-- Show that the similarities form a subgroup of `Perm ℝ`. -/
abbrev similaritySubgroup : Subgroup (Perm ℝ) where
  carrier := { α | IsSimilarity α }
  mul_mem' := by
    -- sorry --
    intro α β hα hβ
    dsimp [IsSimilarity] at hα hβ ⊢
    intro x y z hxy hxz hyz
    have hxy' : β x ≠ β y := β.injective.ne hxy
    have hxz' : β x ≠ β z := β.injective.ne hxz
    have hyz' : β y ≠ β z := β.injective.ne hyz
    rw [← hα, ← hβ]
    · assumption
    · assumption
    · assumption
    · apply β.injective.ne
      assumption
    · apply β.injective.ne
      assumption
    · apply β.injective.ne
      assumption
    -- sorry --
  one_mem' := by
    -- sorry --
    dsimp
    intro x y z hxy hxz hyz
    dsimp
    -- sorry --
  inv_mem' := by
    -- sorry --
    intro α hα
    dsimp [IsSimilarity] at hα ⊢
    intro x y z hxy hxz hyz
    nth_rewrite 2 [hα]
    rw [@Perm.apply_inv_self]
    rw [@Perm.apply_inv_self]
    rw [@Perm.apply_inv_self]
    · apply α⁻¹.injective.ne
      assumption
    · apply α⁻¹.injective.ne
      assumption
    · apply α⁻¹.injective.ne
      assumption
    -- sorry --

notation "A" => similaritySubgroup

/-- Does `A` contain all the translations of `ℝ`? -/
example : T ≤ A := by
  -- sorry --
  dsimp
  intro α hα
  dsimp [IsTranslation] at hα
  dsimp [IsSimilarity]
  intro x y z hxy hxz hyz
  rw [hα, hα]
  -- sorry --

/-- Does `A` contain all the half-turns of `ℝ`? -/
example {a : ℝ} : halfTurn a ∈ A := by
  -- sorry --
  dsimp [IsSimilarity]
  intro x y z hxy hxz hyz
  have : x - z ≠ 0 := by
    contrapose! hxz
    linear_combination hxz
  have : (-x + a) - (-z + a) ≠ 0 := by
    contrapose! hxz
    linear_combination -hxz
  field_simp
  ring
  -- sorry --

/-- If `α ∈ A`, `α 0 = 5` and `α 1 = 7`, find `α y`. -/
example {α : Perm ℝ} (h : α ∈ A) (h0 : α 0 = 5) (h1 : α 1 = 7) (y : ℝ) :
    α y = 2 * y + 5 := by
  -- sorry --
  dsimp [IsSimilarity] at h
  specialize @h 0 y 1
  by_cases h0y : 0 = y
  · rw [← h0y, h0]
    norm_num
  by_cases hy1 : y = 1
  · rw [hy1, h1]
    norm_num
  have h01 : (0:ℝ) ≠ 1 := by norm_num
  specialize h h0y h01 hy1
  rw [h0, h1] at h
  linear_combination -2 * h
  -- sorry --

/-- If `a ∈ A`, `α O = b` and `α 1 = a + b` with `a ≠ 0`, prove that `α y = a * y + b`. -/
theorem IsSimilarity.eq_mul_left_add_right {α : Perm ℝ} (h : α ∈ A) {a b : ℝ} (ha : a ≠ 0)
    (h0 : α 0 = b) (h1 : α 1 = a + b) (y : ℝ) : α y = a * y + b := by
  -- sorry --
  dsimp [IsSimilarity] at h
  specialize @h 0 y 1
  by_cases h0y : 0 = y
  · rw [← h0y, h0]
    norm_num
  by_cases hy1 : y = 1
  · rw [hy1, h1]
    norm_num
  have h01 : (0:ℝ) ≠ 1 := by norm_num
  specialize h h0y h01 hy1
  rw [h0, h1] at h
  have : b - (a + b) ≠ 0 := by
    contrapose! ha
    linear_combination -ha
  field_simp at h
  linear_combination h
  -- sorry --

/-- Prove that all similarities of the real line take the form `x ↦ a * x + b` for some `a`, `b`
with `a ≠ 0`. -/
theorem IsSimilarity.exists_eq_mul_left_add_right {α : Perm ℝ} (h : IsSimilarity α) :
    ∃ (a b : ℝ) (ha : a ≠ 0), α = fun x ↦ a * x + b := by
  -- sorry --
  have H : α 1 - α 0 ≠ 0 := by
    have : (1:ℝ) ≠ 0 := by norm_num
    have := α.injective.ne this
    contrapose! this
    linear_combination this
  use α 1 - α 0, α 0, H
  ext x
  dsimp
  apply IsSimilarity.eq_mul_left_add_right h H
  · rfl
  · ring
  -- sorry --

/-! ## Problem 4 -/

abbrev mulLeftaddRight (a b : ℝ) (ha : a ≠ 0) : Perm ℝ where
  toFun := fun x ↦ a * x + b
  /- If `x' = a * x + b` and `a ≠ 0`, find `x` in terms of `x'` and deduce the inverse of the
  mapping `x ↦ a * x + b`. -/
  invFun := fun x ↦ (x - b) / a
  left_inv := by
    -- sorry --
    intro x
    dsimp
    field_simp
    ring
    -- sorry --
  right_inv := by
    -- sorry --
    intro x
    dsimp
    field_simp
    ring
    -- sorry --

theorem IsSimilarity.exists_eq_mulLeftAddRight {α : Perm ℝ} (h : IsSimilarity α) :
    ∃ (a b : ℝ) (ha : a ≠ 0), α = mulLeftaddRight a b ha := by
  -- sorry --
  obtain ⟨a, b, ha, H⟩ := IsSimilarity.exists_eq_mul_left_add_right h
  use a, b, ha
  ext x
  rw [H]
  dsimp
  -- sorry --

/-! ## Problem 5 -/

/-- Give the algebraic form of the elements in the stabiliser of 0 in the subgroup of similiarites
of R. -/
example (α : A) : α ∈ stabilizer A (0:ℝ) ↔ ∃ (a : ℝ) (ha : a ≠ 0), α = mulLeftaddRight a 0 ha := by
  -- sorry --
  obtain ⟨α, hα⟩ := α
  dsimp at hα ⊢
  constructor
  · apply IsSimilarity.exists_eq_mulLeftAddRight at hα
    obtain ⟨a, b, ha, H⟩ := hα
    rw [H]
    dsimp
    intro h
    use a, ha
    ext x
    dsimp
    linear_combination h
  · intro h
    dsimp
    obtain ⟨a, ha, h⟩ := h
    rw [h]
    dsimp
    ring
  -- sorry --
