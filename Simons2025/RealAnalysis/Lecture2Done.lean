import Mathlib

theorem liftProd {x y N : ℤ} (h : x * y = N) (Npos : 0 < N) :
    ∃ (p q : ℕ), p * q = N ∧
    ((p = x ∧ q = y) ∨ (p = -x ∧ q = -y)) := by
  have h_pos : 0 < x * y := by rwa [h]
  by_cases h_x : 0 ≤ x
  · have h_y : 0 < y := by
      by_contra h_neg
      push_neg at h_neg
      have : x * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h_x h_neg
      linarith
    have h_x_pos : 0 < x := by
      by_contra h_zero
      push_neg at h_zero
      have h_x_zero : x = 0 := le_antisymm h_zero h_x
      rw [h_x_zero, zero_mul] at h
      linarith
    lift x to ℕ using h_x
    lift y to ℕ using h_y.le
    use x, y
    simp [h]
  · push_neg at h_x
    have h_y : y < 0 := by
      by_contra h_nonneg
      push_neg at h_nonneg
      have : x * y ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_lt h_x) h_nonneg
      linarith [h_pos]
    let p : ℕ := x.natAbs
    let q : ℕ := y.natAbs
    have p_eq : p = -x := Int.ofNat_natAbs_of_nonpos h_x.le
    have q_eq : q = -y := Int.ofNat_natAbs_of_nonpos h_y.le
    refine ⟨p, q, ?_, ?_⟩
    · rw [p_eq, q_eq]
      simp [h]
    · right
      exact ⟨p_eq, q_eq⟩


class topologicalSpace (X : Type*) where
  isOpen : Set X → Prop
  isOpen_univ : isOpen (Set.univ : Set X)
  finiteInter : ∀ s t : Set X, isOpen s → isOpen t → isOpen (s ∩ t)
  arbUnion : ∀ (ι : Set (Set X)), (∀ s ∈ ι, isOpen s) → isOpen (⋃ s ∈ ι, s)

-- why don't we need to assume that the empty set is open?
theorem isOpen_emp (X : Type*) [topologicalSpace X] :
    topologicalSpace.isOpen (∅ : Set X) := by
  -- hint:
  let ι : Set (Set X) := ∅
  sorry

-- For the "correct" version of this, click through to the definition of:
--#check TopologicalSpace

class filter (X : Type*) where
  sets : Set (Set X)
  univ_is : Set.univ ∈ sets
  finiteInter : ∀ s t : Set X, s ∈ sets → t ∈ sets → (s ∩ t) ∈ sets
  inclusion : ∀ s t : Set X, s ∈ sets → s ⊆ t → t ∈ sets

-- Exercise: if the empty set is in the filter, then the filter is trivial
example (X : Type*) (f : filter X) (h_empty : ∅ ∈ f.sets) :
  ∀ (S : Set X), S ∈ f.sets := by
  sorry

-- For the "correct" version, click through to:
--#check Filter

def tendsto (X Y : Type*) (f : X → Y) (Nhdx : filter X) (Nhdy : filter Y) :
    Prop := ∀ V ∈ Nhdy.sets, f ⁻¹' V ∈ Nhdx.sets

--#check Filter.Tendsto

def nhdsFilter (X : Type*) [topologicalSpace X] (x : X) : filter X where
  sets := {(T : Set X) | ∃ (S : Set X),
    topologicalSpace.isOpen S ∧ S ⊆ T ∧ x ∈ S}
  univ_is := by
    sorry
  finiteInter := by
    sorry
  inclusion := by
    sorry

-- constant function `tendsto` along any filter
example (X Y : Type*) [topologicalSpace Y]
    (Nhdx : filter X) (y : Y) :
    tendsto X Y (fun _ ↦ y) Nhdx (nhdsFilter Y y) := by
  unfold tendsto
  intro V VinFilter
  sorry

def cocompactFilter (X : Type*) [TopologicalSpace X] : filter X where
  sets := {(T : Set X) | ∃ (S : Set X), IsCompact S ∧ Sᶜ ⊆ T}
  univ_is := sorry
  finiteInter := sorry
  inclusion := sorry

-- make a filter of sets that are complements of finite sets
def cofiniteFilter (X : Type*) : filter X where
  sets := sorry
  univ_is := sorry
  finiteInter := sorry
  inclusion := sorry

def atTopFilter (X : Type*) [Preorder X] : filter X where
  sets := {(T : Set X) | ∃ b : X, Set.Ioi b ⊆ T}
  univ_is := sorry
  finiteInter := sorry
  inclusion := sorry


example [topologicalSpace ℝ] : tendsto ℝ ℝ (fun x ↦ 1 / x) (atTopFilter ℝ) (nhdsFilter ℝ 0) := by
  sorry

open Topology Filter

example : Tendsto (fun (x : ℝ) ↦ (1 : ℝ) / x) atTop (𝓝 0) := by
  refine NormedAddCommGroup.tendsto_atTop'.mpr ?_
  intro ε εpos
  simp only [one_div, sub_zero, norm_inv, Real.norm_eq_abs]
  use ε⁻¹
  intro n hn
  have n_pos : 0 < n := lt_trans (inv_pos.mpr εpos) hn
  rw [abs_of_pos n_pos]
  exact inv_lt_of_inv_lt₀ εpos hn

  -- refine inv_lt_of_inv_lt₀ εpos ?_
  -- convert hn
  -- rw [@abs_eq_self]
  -- have : 0 < ε⁻¹ := by positivity
  -- order

  -- intro U UinN
  -- rw [mem_nhds_iff] at UinN
  -- obtain ⟨t, tSubU, tOpen, zeroInt⟩ := UinN
  -- simp only [one_div, Filter.map_inv, inv_atTop₀]


--   sorry

-- #exit
--   intro U
--   convert tendsto_inv_atTop_zero using 1
--   · simp only [one_div]
--   · exact Real.instIsStrictOrderedRing
--   · infer_instance


def seqLimIs (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - L| < ε

theorem seqLimIs_iff_TendsTo (a : ℕ → ℝ) (L : ℝ) :
    seqLimIs a L ↔ Tendsto a atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop]
  rfl
  constructor
  · intro h
    rwa [Metric.tendsto_atTop]
    intro ε εpos
    obtain ⟨N, hN⟩ := h ε εpos
    use N
    intro n hn
    exact hN n hn
    --exact Metric.tendsto_atTop.mpr h
    sorry
  · intro h
    unfold seqLimIs
    intro ε ε_pos
    -- apply Metric.tendsto_atTop.mp h
    -- exact ε_pos
    sorry

/-
A property `p` occurs "eventually" in a filter `f` if the set for which the property holds
is in the filter
-/
def eventually (X : Type*) (p : X → Prop) (f : Filter X) : Prop :=
  {x | p x} ∈ f

--#check Filter.Eventually

example : ∀ᶠ x in (𝓝 (0 : ℝ)), 1 / x > 100 := by
  sorry


example : ∀ᶠ x in (𝓝[>] (0 : ℝ)), x⁻¹ > 100 := by
  rw [Filter.eventually_iff]
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]

  sorry
