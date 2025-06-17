import Mathlib

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
def cofiniteFilter (X : Type*) : filter X := sorry

def atTopFilter (X : Type*) [TopologicalSpace X] [Preorder X] [OrderTopology X] : filter X where
  sets := {(T : Set X) | ∃ b : X, Set.Ioi b ⊆ T}
  univ_is := sorry
  finiteInter := sorry
  inclusion := sorry


example [topologicalSpace ℝ] : tendsto ℝ ℝ (fun x ↦ 1 / x) (atTopFilter ℝ) (nhdsFilter ℝ 0) := by
  sorry

open Topology Filter

example : Tendsto (fun (x : ℝ) ↦ (1 : ℝ) / x) atTop (𝓝 0) := by
  sorry

def seqLimIs (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - L| < ε

theorem seqLimIs_iff_TendsTo (a : ℕ → ℝ) (L : ℝ) :
    seqLimIs a L ↔ Tendsto a atTop (𝓝 L) := by
  constructor
  · intro h
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

-- #check Filter.Eventually

example : ∀ᶠ x in (𝓝 (0 : ℝ)), 1 / x > 100 := by
  sorry


example : ∀ᶠ x in (𝓝[>] (0 : ℝ)), x⁻¹ > 100 := by
  rw [Filter.eventually_iff]
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
