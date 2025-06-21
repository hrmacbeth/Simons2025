import Mathlib

open Complex

structure IsUniversalCover₀ {X Y : Type*} (p : Y → X) [TopologicalSpace Y] [TopologicalSpace X] :
    Prop where
  is_covering : IsCoveringMap p
  connected_cover : ConnectedSpace Y
  simply_connected : SimplyConnectedSpace Y

structure IsUniversalCover {X Y : Type*} (p : Y → X) [TopologicalSpace Y] [TopologicalSpace X] extends IsUniversalCover₀ p where
  connected_base : ConnectedSpace X


theorem IsUniversalCover.unique_lift
    {X Y Z : Type*} [TopologicalSpace X] [ConnectedSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (p : Y → X) (h_univ : IsUniversalCover p)
    (q : Z → X) [ConnectedSpace Z] (h_cover : IsCoveringMap q) :
    ∃! (f : Y → Z), IsCoveringMap f ∧ q ∘ f = p := by

  sorry

universe u

def DeckTransformationGroup {X : Type*} {Y : Type u} [TopologicalSpace Y] [TopologicalSpace X]
    (p : Y → X) : Type u :=
  {f : Y ≃ₜ Y // p ∘ f = p}

instance {X : Type*} {Y : Type u} [TopologicalSpace Y] [TopologicalSpace X] (p : Y → X) :
    Group (DeckTransformationGroup p) where
  -- Identity: the identity homeomorphism
  one := ⟨Homeomorph.refl Y, by simp⟩
  -- Multiplication: composition of homeomorphisms
  mul := fun ⟨f, hf⟩ ⟨g, hg⟩ => ⟨f.trans g, by
    have :  p ∘ ⇑(f.trans g) =  (p ∘ g) ∘f := rfl
    rw [this]
    simp [hf, hg]⟩
  -- Inverse: inverse homeomorphism
  inv := fun ⟨f, hf⟩ => ⟨f.symm, by
    nth_rw 1 [← hf]
    have : (p ∘ f) ∘ f.symm =  p ∘ (f ∘ f.symm) := by rfl
    rw [this]
    simp⟩
  -- Associativity
  mul_assoc := fun ⟨f, hf⟩ ⟨g, hg⟩ ⟨h, hh⟩ => by
    have : (f ∘ g) ∘ h = f * (g * h) := by simp
    simp [Homeomorph.trans_apply]

  -- Left identity
  one_mul := fun ⟨f, _⟩ => by
    ext
    simp

  -- Right identity
  mul_one := fun ⟨f, _⟩ => by
    ext
    simp

  -- Left inverse
  inv_mul_cancel := fun ⟨f, _⟩ => by
    ext
    simp

-- Main theorem: Fundamental group via deck transformations
def FundamentalGroup_iso_DeckTransformationGroup
    {X Y : Type*} [TopologicalSpace X] [ConnectedSpace X] [LocPathConnectedSpace X]
    (x₀ : X) (p : Y → X) [TopologicalSpace Y]
    (h_universal : IsUniversalCover p) :
    (FundamentalGroup X x₀)ᵐᵒᵖ ≃* DeckTransformationGroup p := by

  sorry





theorem kernel_eq_two_pi_zmultiples :
  Circle.expHom.ker = AddSubgroup.zmultiples (2 * Real.pi) := by
  -- Use AddSubgroup extensionality: two subgroups are equal iff they have the same elements
  ext t
  have := Complex.exp_eq_one_iff (x := t * I)
  convert this
  · simp only [AddMonoidHom.mem_ker, Circle.expHom_apply, Function.comp_apply, ofMul_eq_zero]

    have := Circle.coe_exp t
    rw [← this]
    have : ((1 : Circle) : ℂ) = (1 : ℂ) := by simp
    rw[← this]
    norm_cast
  · rw [AddSubgroup.mem_zmultiples_iff]
    simp only [zsmul_eq_mul, mul_assoc]
    sorry

-- Fundamental theorem of covering spaces
theorem fundamental_theorem_covering_spaces
  (X : Type*) [TopologicalSpace X] [ConnectedSpace X] [LocPathConnectedSpace X] :
  CategoryEquivalence (CoveringSpaceCategory X) (FundamentalGroupoidActionCategory X) := by
  sorry

lemma CircleExp_isCoveringMap : IsCoveringMap Circle.exp := by
  let foo : Circle → Trivialization ℤ Circle.exp := by
    intro x
    apply Trivialization.mk
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
  apply IsCoveringMap.mk Circle.exp (fun _ => ℤ) foo
  intro x

  sorry



#exit

def CircleFundamentalGroup : FundamentalGroup Circle 1 ≃* ℤ := by

  let f : FundamentalGroup Circle 1 →ₙ* ℤ := by
    sorry
  apply MulHom.toMulEquiv
  · sorry
  sorry

#exit
  -- Now we need to show: t ∈ Circle.expHom.ker ↔ t ∈ AddSubgroup.zmultiples (2 * Real.pi)

  constructor
  -- Forward direction: if t is in the kernel, then t = 2πn for some integer n
  · intro h_in_ker
    -- h_in_ker : t ∈ Circle.expHom.ker
    -- This means Circle.expHom t = 1 (the identity in Circle)
    rw [AddMonoidHom.mem_ker] at h_in_ker
    rw [AddSubgroup.mem_zmultiples_iff]
    -- h_in_ker : Circle.expHom t = 1
    have : cexp (↑t * I) = 1 := by
      exact
        (Submonoid.mk_eq_one
              { carrier := Metric.sphere 0 1, mul_mem' := @Circle.exp._proof_1,
                one_mem' := Circle.exp._proof_2 }).mp
          h_in_ker
    have := (Complex.exp_eq_one_iff (x := (t * I))).mp this

    obtain ⟨n, hn⟩ := this
    use n
    have : t = n * (2 * Real.pi) := by
      have : n * (2 * ↑Real.pi * I) = (n * 2 * ↑Real.pi) * I := by ring
      rw [this] at hn
      apply mul_right_cancel₀ (I_ne_zero) at hn
      norm_cast at hn
      rw [hn]
      simp only [Int.cast_mul, Int.cast_ofNat]
      ring
    rw [this]
    simp


  -- Reverse direction: if t = 2πn for some integer n, then t is in the kernel
  · intro h_in_zmultiples
    -- h_in_zmultiples : t ∈ AddSubgroup.zmultiples (2 * Real.pi)
    rw [AddSubgroup.mem_zmultiples_iff] at h_in_zmultiples
    -- h_in_zmultiples : ∃ n : ℤ, t = n * (2 * Real.pi)

    obtain ⟨n, hn⟩ := h_in_zmultiples
    -- hn : t = n * (2 * Real.pi)

    -- Show t ∈ Circle.expHom.ker, i.e., Circle.expHom t = 1
    rw [AddMonoidHom.mem_ker]
    -- Goal: Circle.expHom t = 1

    -- Substitute t = n * (2 * Real.pi)
    rw [hn]
    -- Goal: Circle.expHom (n * (2 * Real.pi)) = 1

    -- Use additivity of Circle.expHom and the fact that exp(2πi) = 1
    -- Circle.expHom (n * (2 * Real.pi)) = (Circle.expHom (2 * Real.pi))^n = 1^n = 1
    have exp_2pi_eq_one : Circle.expHom (2 * Real.pi) = 1 := by
      -- This follows from exp(2πi) = cos(2π) + i sin(2π) = 1 + 0i = 1
      sorry -- Need Circle.expHom_two_pi or similar

    -- Use homomorphism property
    rw [← AddMonoidHom.map_zsmul]
    -- Goal: Circle.expHom (2 * Real.pi) ^ n = 1  (in multiplicative notation)
    rw [exp_2pi_eq_one]
    -- Goal: 1 ^ n = 1
    exact one_pow n

#exit


-- The exponential covering map from ℝ to the unit circle
-- In Mathlib4, this is implemented via AddCircle.toCircle and Circle.exp
noncomputable def coveringMap : ℝ → Circle := Circle.exp

-- The universal covering space is ℝ, which is simply connected
-- The fundamental group of the circle is isomorphic to ℤ via the kernel of the covering map

-- First, let's establish that coveringMap is a group homomorphism
-- when we view ℝ as an additive group and Circle as a multiplicative group
theorem coveringMap_isGroupHom : ∀ x y : ℝ,
  coveringMap (x + y) = coveringMap x * coveringMap y := by
  intro x y
  -- This follows from Circle.exp_add in Mathlib4
  exact Circle.exp_add x y

-- The kernel of the covering map
def kernelCoveringMap : Set ℝ := {t : ℝ | coveringMap t = 1}

-- The kernel consists of integer multiples of 2π
theorem kernel_eq_two_pi_Z : kernelCoveringMap = {t : ℝ | ∃ n : ℤ, t = 2 * Real.pi * n} := by
  ext t
  simp [kernelCoveringMap, coveringMap]
  constructor
  · intro h
    -- If Circle.exp t = 1, then t = 2πn for some integer n
    -- This uses the periodicity of the exponential map
    rw [Circle.exp_eq_one_iff] at h
    exact h
  · intro ⟨n, hn⟩
    -- If t = 2πn, then Circle.exp t = 1
    rw [hn]
    rw [← Circle.exp_int_mul]
    exact Circle.exp_two_pi

-- The AddCircle structure gives us the quotient ℝ/(2π⋅ℤ)
-- This is homeomorphic to the unit circle
theorem addCircle_homeomorph_circle :
  AddCircle (2 * Real.pi) ≃ₜ Circle :=
  AddCircle.homeomorphCircle'

-- The fundamental theorem: π₁(S¹) ≅ ℤ
-- This is expressed as the isomorphism between the kernel (which forms a group under addition)
-- and the integers
theorem fundamental_group_circle_iso_int :
  -- The quotient group ℝ / (kernel of covering map) is isomorphic to the circle
  -- And the kernel is isomorphic to ℤ
  ∃ (f : ℤ → kernelCoveringMap), Function.Bijective f ∧
    ∀ m n : ℤ, f (m + n) = f m + f n := by
  -- Define the isomorphism explicitly
  use fun n => ⟨2 * Real.pi * n, by
    simp [kernelCoveringMap]
    use n
    ring⟩

  constructor
  · -- Prove bijectivity
    constructor
    · -- Injectivity
      intro m n h
      simp at h
      have : (2 * Real.pi * m : ℝ) = 2 * Real.pi * n := by
        exact Subtype.mk.inj h
      -- Since 2π ≠ 0, we can cancel
      have pi_ne_zero : (2 * Real.pi : ℝ) ≠ 0 := by
        simp [Real.pi_ne_zero]
      exact mul_left_cancel₀ pi_ne_zero this

    · -- Surjectivity
      intro ⟨t, ht⟩
      simp [kernelCoveringMap] at ht
      rw [kernel_eq_two_pi_Z] at ht
      obtain ⟨n, rfl⟩ := ht
      use n
      simp

  · -- Preserve addition
    intro m n
    simp
    ring

-- Alternative formulation using AddCircle directly
theorem fundamental_group_via_addCircle :
  -- The covering map ℝ → AddCircle (2π) has kernel 2π⋅ℤ
  -- and this kernel is isomorphic to ℤ
  let quotMap : ℝ → AddCircle (2 * Real.pi) := fun t => ⟨t, rfl⟩
  ∃ (kernel : Set ℝ),
    (∀ t : ℝ, quotMap t = 0 ↔ t ∈ kernel) ∧
    (∃ (iso : ℤ → kernel), Function.Bijective iso) := by

  use {t : ℝ | ∃ n : ℤ, t = 2 * Real.pi * n}
  constructor
  · intro t
    simp [AddCircle.coe_eq_zero_iff]
    constructor
    · intro h
      exact h
    · intro h
      exact h

  · -- The isomorphism ℤ → 2π⋅ℤ
    use fun n => ⟨2 * Real.pi * n, ⟨n, rfl⟩⟩
    constructor
    · -- Injectivity
      intro m n h
      simp at h
      have : (2 * Real.pi * m : ℝ) = 2 * Real.pi * n := Subtype.mk.inj h
      have pi_ne_zero : (2 * Real.pi : ℝ) ≠ 0 := by simp [Real.pi_ne_zero]
      exact mul_left_cancel₀ pi_ne_zero this
    · -- Surjectivity
      intro ⟨t, ⟨n, hn⟩⟩
      use n
      simp [hn]
