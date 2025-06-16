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
    sorry
  right_inv := by
    sorry

/-- If, for some given real number `a`, `α` is the element `x ↦ x + a` of `Perm ℝ`, prove that, for
any two real numbers `x` and `y`, `x - y = α x - α y`. -/
example (a : ℝ) :
    let α := addRight a
    ∀ x y, x - y = α x - α y := by
  sorry

/-- An element `α` of `Perm ℝ` such that, for any two real numbers `x` and `y`, `x - y = α x - α y`,
is called a *translation* of `ℝ`. -/
def IsTranslation (α : Perm ℝ) : Prop :=
  ∀ x y : ℝ, α x - α y = x - y

/-- Show that the translations form a subgroup of `Perm ℝ`. -/
abbrev translationSubgroup : Subgroup (Perm ℝ) where
  carrier := { α | IsTranslation α }
  mul_mem' := by
    sorry
  one_mem' := by
    sorry
  inv_mem' := by
    sorry

notation "T" => translationSubgroup

/-- If `α ∈ T` and `α 0 = 0`, prove that `α x = x + a`. -/
example {α : Perm ℝ} (hα : α ∈ T) {a : ℝ} (h : α 0 = a) : α = addRight a := by
  sorry

/-! ## Problem 2 -/

abbrev halfTurn (a : ℝ) : Perm ℝ where
  toFun := fun x ↦ -x + a
  invFun := fun x ↦ -x + a
  left_inv := by
    sorry
  right_inv := by
    sorry

/-- If for some real number `a`, `α` is the element `x ↦ - x + a` of `Perm ℝ`, prove that for any
two real numbers `x`, `-(x - y) = α x - α y`. -/
example (a : ℝ) :
    let α := halfTurn a
    ∀ x y, -(x - y) = α x - α y := by
  sorry

/-- Find the fixed point of `α`. -/
example (a : ℝ) :
    let α := halfTurn a
    { x | α x = x } = {a / 2} := by
  sorry

/-- An element `α` of `Perm ℝ` which preserves absolute values of lengths is an *isometry* of `ℝ`.
-/
def IsIsometry (α : Perm ℝ) : Prop :=
  ∀ x y : ℝ, |α x - α y| = |x - y|

/-- Show that the isometries form a subgroup of `Perm ℝ`. -/
abbrev isometrySubgroup : Subgroup (Perm ℝ) where
  carrier := { α | IsIsometry α }
  mul_mem' := by
    sorry
  one_mem' := by
    sorry
  inv_mem' := by
    sorry

notation "M" => isometrySubgroup

/-- Does `M` contain the translation group of `ℝ`? -/
example : T ≤ M := by
  sorry

/-- Does `M` contain the half-turns of `ℝ`? -/
example (a : ℝ) : halfTurn a ∈ M := by
  sorry

#check abs_eq_abs
#check eq_or_eq_neg_of_abs_eq

/-- If `α ∈ M` and `α 0 = 5`, what can `α 2` be? -/
example {α : Perm ℝ} (hα : α ∈ M) (h : α 0 = 5) : α 2 ∈ {3, 7} := by
  sorry

/-- If `α ∈ M` and `α 0 = 5`, what can `α x` be? -/
example {α : Perm ℝ} (hα : α ∈ M) (h : α 0 = 5) (x : ℝ) : α x ∈ {5 - x, 5 + x} := by
  sorry

/-- If `α ∈ M` and `α 0 = a`, prove that for all `x`, `α x = ± x + a`. -/
theorem IsIsometry.eval_of_eval_zero {α : Perm ℝ} (hα : α ∈ M) {a : ℝ} (h : α 0 = a) (x : ℝ) :
    α x ∈ {- x + a, x + a} := by
  sorry

/- If, for given `α`, `α x = x + a` and `α y = - y + a`, prove that `|x - y| = |x + y|` and
deduce that `x` or `y` is zero. -/
theorem IsIsometry.aux {α : Perm ℝ} (hα : α ∈ M) {a x : ℝ} (hx : α x = x + a) {y : ℝ}
    (hy : α y = -y + a) :
    x = 0 ∨ y = 0 := by
  sorry

/-- If `α ∈ M` and `α 0 = a`, prove that `α` is either a half-turn or a translation. -/
theorem IsIsometry.eq_addRight_or_eq_halfTurn {α : Perm ℝ} (hα : α ∈ M) {a : ℝ} (h : α 0 = a) :
    α = addRight a ∨ α = halfTurn a := by
  sorry

/-- If `α ∈ M`, prove that `α` is either a half-turn or a translation. -/
example {α : Perm ℝ} (hα : α ∈ M) : ∃ a, α = addRight a ∨ α = halfTurn a := by
  sorry

/-! ## Problem 3 -/

/-- Find the fixed point of `x ↦ 2 * x - 1`. -/
example :
    let α := fun (x:ℝ) ↦ 2 * x - 1
    { x | α x = x } = {1} := by
  sorry

/-- If `α` is `x ↦ a * x + b` and `a ≠ 0, 1`, find the fixed point of `α`. -/
example (a b : ℝ) (ha : a ≠ 0) (ha' : a ≠ 1) :
    let α := fun x ↦ a * x + b
    { x | α x = x } = {- b / (a - 1)} := by
  sorry

/-- If `α` is the element `x ↦ a * x + b` of `Perm ℝ` and `a ≠ 0`, compare the ratio
`(x - y) / (x - z)` with the ratio `(α x - α y) / (α x - α z)` for any three distinct real numbers
`x`, `y` and `z`. -/
example (a b : ℝ) (ha : a ≠ 0) {x y z : ℝ} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    let α := fun x ↦ a * x + b
    (x - y) / (x - z) = (α x - α y) / (α x - α z) := by
  sorry

/-- A transformation which preserves ratios of lengths on the real line is called a *similarity* of
the real line. -/
def IsSimilarity (α : Perm ℝ) : Prop :=
  ∀ {x y z : ℝ} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z),
    (x - y) / (x - z) = (α x - α y) / (α x - α z)

#check Equiv.injective
#check Function.Injective.ne

/-- Show that the similarities form a subgroup of `Perm ℝ`. -/
abbrev similaritySubgroup : Subgroup (Perm ℝ) where
  carrier := { α | IsSimilarity α }
  mul_mem' := by
    sorry
  one_mem' := by
    sorry
  inv_mem' := by
    sorry

notation "A" => similaritySubgroup

/-- Does `A` contain all the translations of `ℝ`? -/
example : T ≤ A := by
  sorry

/-- Does `A` contain all the half-turns of `ℝ`? -/
example {a : ℝ} : halfTurn a ∈ A := by
  sorry

/-- If `α ∈ A`, `α 0 = 5` and `α 1 = 7`, find `α y`. -/
example {α : Perm ℝ} (h : α ∈ A) (h0 : α 0 = 5) (h1 : α 1 = 7) (y : ℝ) :
    α y = 2 * y + 5 := by
  sorry

/-- If `a ∈ A`, `α O = b` and `α 1 = a + b` with `a ≠ 0`, prove that `α y = a * y + b`. -/
theorem IsSimilarity.eq_mul_left_add_right {α : Perm ℝ} (h : α ∈ A) {a b : ℝ} (ha : a ≠ 0)
    (h0 : α 0 = b) (h1 : α 1 = a + b) (y : ℝ) : α y = a * y + b := by
  sorry

/-- Prove that all similarities of the real line take the form `x ↦ a * x + b` for some `a`, `b`
with `a ≠ 0`. -/
theorem IsSimilarity.exists_eq_mul_left_add_right {α : Perm ℝ} (h : IsSimilarity α) :
    ∃ (a b : ℝ) (ha : a ≠ 0), α = fun x ↦ a * x + b := by
  sorry

/-! ## Problem 4 -/

abbrev mulLeftaddRight (a b : ℝ) (ha : a ≠ 0) : Perm ℝ where
  toFun := fun x ↦ a * x + b
  /- If `x' = a * x + b` and `a ≠ 0`, find `x` in terms of `x'` and deduce the inverse of the
  mapping `x ↦ a * x + b`. -/
  invFun := fun x ↦ (x - b) / a
  left_inv := by
    sorry
  right_inv := by
    sorry

theorem IsSimilarity.exists_eq_mulLeftAddRight {α : Perm ℝ} (h : IsSimilarity α) :
    ∃ (a b : ℝ) (ha : a ≠ 0), α = mulLeftaddRight a b ha := by
  sorry

/-! ## Problem 5 -/

/-- Give the algebraic form of the elements in the stabiliser of 0 in the subgroup of similiarites
of R. -/
example (α : A) : α ∈ stabilizer A (0:ℝ) ↔ ∃ (a : ℝ) (ha : a ≠ 0), α = mulLeftaddRight a 0 ha := by
  sorry

