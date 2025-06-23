/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
import Mathlib.Algebra.Star.Unitary
import Mathlib.Tactic.Module
/-! # Quadratic algebras

Given a commutative ring `R`, this is the ring obtained by adjoining
root of a quadratic equation `X ^ 2 + a * X + b = 0`.

After defining the norm, we show that it is a linearly ordered commutative ring,
as well as an integral domain.

We provide the universal property, that ring homomorphisms `QuadraticAlgebra a b →+* R` correspond
to choices of square roots of `d` in `R`.

-/

lemma add_add_add_comm' {A : Type*} [AddCommSemigroup A] (x y z t : A) :
    x + y + z + t = x + z + y + t := by
  -- sorry
  simp only [add_assoc, add_comm y]
  -- sorry

variable {R : Type*}

/-- The quadratic algebras obtained by adjoining with
  a root of `X ^2 + a * X + b`.
  These have the form `x + b y` where `x y : R`. The components
  are called `x` and `y`. -/
@[ext]
structure QuadraticAlgebra (a b : R) where
  /-- Component of the integer not multiplied by `ω` -/
  x : R
  /-- Component of the integer multiplied by `ω` -/
  y : R
  deriving DecidableEq

-- invent a good notation
-- @[inherit_doc]
-- notation:25  "((" a:25 " | " b:25 "))" => QuadraticAlgebra a b

namespace QuadraticAlgebra

variable [CommRing R] {a b : R}

/-- Convert an element of `R` to a quadratic algebra -/
@[coe]
def coe (n : R) : QuadraticAlgebra a b :=
  ⟨n, 0⟩

instance : Coe R (QuadraticAlgebra a b) := ⟨coe⟩

@[simp]
theorem coe_x (n : R) : (n : QuadraticAlgebra a b).x = n :=
  -- sorry
  rfl
  -- sorry

@[simp]
theorem coe_y (n : R) : (n : QuadraticAlgebra a b).y = 0 :=
  -- sorry
  rfl
  -- sorry

/-- The zero of the ring -/
instance : Zero (QuadraticAlgebra a b) :=
  ⟨(0 : R)⟩

@[simp]
theorem zero_x : (0 : QuadraticAlgebra a b).x = 0 :=
  -- sorry
  rfl
  -- sorry

@[simp]
theorem zero_y : (0 : QuadraticAlgebra a b).y = 0 :=
  -- sorry
  rfl
  -- sorry

@[simp]
theorem coe_zero : ((0 : R) : QuadraticAlgebra a b) = 0 := rfl

instance : Inhabited (QuadraticAlgebra a b) :=
  ⟨0⟩

/-- The one of the ring -/
instance : One (QuadraticAlgebra a b) :=
  ⟨(1 : R)⟩

@[simp]
theorem one_x : (1 : QuadraticAlgebra a b).x = 1 :=
  -- sorry
  rfl
  -- sorry

@[simp]
theorem one_y : (1 : QuadraticAlgebra a b).y = 0 :=
  -- sorry
  rfl
  -- sorry

@[simp]
theorem coe_one : ((1 : R) : QuadraticAlgebra a b) = 1 := rfl

theorem coe_injective :
    Function.Injective (coe : R → QuadraticAlgebra a b) := fun m n h ↦ by
  -- sorry
  rw [← coe_x m, ← coe_x n, h]
  -- sorry

theorem coe_inj {m n : R} :
    (m : QuadraticAlgebra a b) = n ↔ m = n :=
  coe_injective.eq_iff

theorem coe_eq_zero_iff {r : R} :
    (r : QuadraticAlgebra a b) = 0 ↔ r = 0 := by
  -- sorry
  rw [← coe_zero, coe_inj]
  -- sorry

theorem coe_eq_one_iff {r : R} : (r : QuadraticAlgebra a b) = 1 ↔ r = 1 := by
  -- sorry
  rw [← coe_one, coe_inj]
  -- sorry

/-- The representative of the root in the quadratic algebra -/
def omega : QuadraticAlgebra a b :=
  ⟨0, 1⟩

notation:25 "ω" => omega

@[simp]
theorem omega_x : (ω : QuadraticAlgebra a b).x = 0 :=
  rfl

@[simp]
theorem omega_y : (ω : QuadraticAlgebra a b).y = 1 :=
  rfl

/-- The representative of the “other” root in the quadratic algebra.

One has omega + omega' = -a -/
def omega' : QuadraticAlgebra a b :=
  ⟨-a, -1⟩

notation:25 "ω'" => omega'

@[simp]
theorem omega'_x : (ω' : QuadraticAlgebra a b).x = -a :=
  rfl

@[simp]
theorem omega'_y : (ω' : QuadraticAlgebra a b).y = -1 :=
  rfl

/-- Addition of elements of `QuadraticAlgebra a b` -/
instance : Add (QuadraticAlgebra a b) :=
  ⟨fun z w ↦ ⟨z.1 + w.1, z.2 + w.2⟩⟩

@[simp]
theorem add_def (x y x' y' : R) :
    (⟨x, y⟩ + ⟨x', y'⟩ : QuadraticAlgebra a b) = ⟨x + x', y + y'⟩ :=
  rfl

@[simp]
theorem add_x (z w : QuadraticAlgebra a b) : (z + w).x = z.x + w.x :=
  -- sorry
  rfl
  -- sorry

@[simp]
theorem add_y (z w : QuadraticAlgebra a b) : (z + w).y = z.y + w.y :=
  -- sorry
  rfl
  -- sorry

theorem coe_add (u v : R) :
    ((u + v : R) : QuadraticAlgebra a b) = u + v := by
  ext <;> simp

/-- Negation in `QuadraticAlgebra a b` -/
instance : Neg (QuadraticAlgebra a b) :=
  ⟨fun z ↦ ⟨-z.1, -z.2⟩⟩

@[simp]
theorem neg_x (z : QuadraticAlgebra a b) : (-z).x = -z.x :=
  rfl

@[simp]
theorem neg_y (z : QuadraticAlgebra a b) : (-z).y = -z.y :=
  rfl

theorem coe_neg (r : R) :
    ((- r : R) : QuadraticAlgebra a b) = -r := by
  ext <;> simp

/-- The structure of an additive commutative group on `QuadraticAlgebra a b` -/
instance addCommGroup : AddCommGroup (QuadraticAlgebra a b) := by
  refine
  { add := (· + ·)
    zero := (0 : QuadraticAlgebra a b)
    sub := fun a b => a + -b
    neg := Neg.neg
    nsmul := @nsmulRec (QuadraticAlgebra a b) ⟨0⟩ ⟨(· + ·)⟩
    zsmul := @zsmulRec (QuadraticAlgebra a b) ⟨0⟩ ⟨(· + ·)⟩ ⟨Neg.neg⟩ (@nsmulRec (QuadraticAlgebra a b) ⟨0⟩ ⟨(· + ·)⟩)
    add_assoc := ?_
    zero_add := ?_
    add_zero := ?_
    neg_add_cancel := ?_
    add_comm := ?_ } <;>
  intros <;>
  ext <;>
  simp [add_comm, add_left_comm]

@[simp]
theorem sub_x (z w : QuadraticAlgebra a b) : (z - w).x = z.x - w.x := by
  simp [sub_eq_add_neg]

@[simp]
theorem sub_y (z w : QuadraticAlgebra a b) : (z - w).y = z.y - w.y := by
  simp [sub_eq_add_neg]

theorem coe_sub (u v : R) :
    ((u - v : R) : QuadraticAlgebra a b) = u - v := by
  ext <;> simp

/-- The structure of an “additive group with one” on `QuadraticAlgebra a b` -/
instance addGroupWithOne : AddGroupWithOne (QuadraticAlgebra a b) := {
  QuadraticAlgebra.addCommGroup with
    natCast := fun n ↦ coe n
    natCast_zero := by simp only [Nat.cast_zero]; rfl
    natCast_succ n := by
      ext <;> simp
    intCast := fun n ↦ coe n
    intCast_negSucc n := by
      ext
      · rw [Int.cast_negSucc, coe_x, neg_x]; rfl
      · rw [Int.cast_negSucc, coe_y, neg_y, eq_comm, neg_eq_zero]; rfl
    intCast_ofNat n := by ext <;> simp <;> rfl
    one := 1 }

@[simp]
theorem natCast_x (n : ℕ) : (n : QuadraticAlgebra a b).x = n := rfl

@[simp]
theorem natCast_y (n : ℕ) : (n : QuadraticAlgebra a b).y = 0 := rfl

theorem natCast_val (n : ℕ) : (n : QuadraticAlgebra a b) = ⟨n, 0⟩ :=
  rfl

@[simp]
theorem coe_nat_eq_natCast (n : ℕ) :
    ((n : R) : QuadraticAlgebra a b) = n := by
  ext <;> simp [coe_x, coe_y]

@[simp]
theorem intCast_x (n : ℤ) : (n : QuadraticAlgebra a b).x = n := rfl

@[simp]
theorem intCast_y (n : ℤ) : (n : QuadraticAlgebra a b).y = 0 := rfl

theorem intCast_val (n : ℤ) : (n : QuadraticAlgebra a b) = ⟨n, 0⟩ :=
  rfl

@[simp]
theorem coe_int_eq_intCast (n : ℤ) :
    ((n : R) : QuadraticAlgebra a b) = n := by
  ext <;> simp [coe_x, coe_y]

/-- Multiplication in `QuadraticAlgebra a b`.

(x + ω y) (u + ω v) = (xy  - b y v) + ω (yu + xv - a yv) -/
instance : Mul (QuadraticAlgebra a b) :=
  ⟨fun z w ↦ ⟨z.1 * w.1 - b * z.2 * w.2, z.1 * w.2 + z.2 * w.1 - a * z.2 * w.2⟩⟩

@[simp]
theorem mul_x (z w : QuadraticAlgebra a b) :
    (z * w).x = z.x * w.x - b * z.y * w.y :=
  rfl

@[simp]
theorem mul_y (z w : QuadraticAlgebra a b) : (z * w).y = z.x * w.y + z.y * w.x - a * z.2 * w.2 :=
  rfl

theorem coe_mul (u v : R) :
    ((u * v : R) : QuadraticAlgebra a b) = u * v := by
  ext <;> simp

instance commRing : CommRing (QuadraticAlgebra a b) := by
  refine
  { QuadraticAlgebra.addGroupWithOne with
    mul := (· * ·)
    npow := @npowRec (QuadraticAlgebra a b) ⟨1⟩ ⟨(· * ·)⟩,
    add_comm := ?_
    left_distrib := ?_
    right_distrib := ?_
    zero_mul := ?_
    mul_zero := ?_
    mul_assoc := ?_
    one_mul := ?_
    mul_one := ?_
    mul_comm := ?_ } <;>
  intros <;>
  ext <;>
  simp <;>
  ring

instance : AddMonoid (QuadraticAlgebra a b) := by infer_instance

instance : Monoid (QuadraticAlgebra a b) := by infer_instance

instance : CommMonoid (QuadraticAlgebra a b) := by infer_instance

instance : CommSemigroup (QuadraticAlgebra a b) := by infer_instance

instance : Semigroup (QuadraticAlgebra a b) := by infer_instance

instance : AddCommSemigroup (QuadraticAlgebra a b) := by infer_instance

instance : AddSemigroup (QuadraticAlgebra a b) := by infer_instance

instance : CommSemiring (QuadraticAlgebra a b) := by infer_instance

instance : Semiring (QuadraticAlgebra a b) := by infer_instance

instance : Ring (QuadraticAlgebra a b) := by infer_instance

instance : Distrib (QuadraticAlgebra a b) := by infer_instance

theorem omega_add_omega' :
    (ω : QuadraticAlgebra a b) + (ω' : QuadraticAlgebra a b) = (-a : R) := by
  ext <;> simp

theorem omega_mul_omega' :
    (ω : QuadraticAlgebra a b) * (ω' : QuadraticAlgebra a b) = (b : R) := by
  ext <;> simp

/-- Conjugation in `QuadraticAlgebra a b`.
The conjugate of `x + y ω` is `x + y ω' = (x - a * y) - y ω`. -/
instance : Star (QuadraticAlgebra a b) where
  star z := ⟨z.1 - a * z.2, -z.2⟩

@[simp]
theorem star_mk (x y : R) :
    star (⟨x, y⟩ : QuadraticAlgebra a b) = ⟨x - a * y, -y⟩ :=
  rfl

theorem star_omega : star (ω : QuadraticAlgebra a b) = (ω') := by
  simp [star, omega, omega']

theorem star_omega' : star (ω' : QuadraticAlgebra a b) = (ω) := by
  simp [star, omega, omega']

@[simp]
theorem star_x (z : QuadraticAlgebra a b) :
    (star z).x = z.x - a * z.y :=
  rfl

@[simp]
theorem star_y (z : QuadraticAlgebra a b) :
    (star z).y = -z.y :=
  rfl

instance : StarRing (QuadraticAlgebra a b) where
  star_involutive _ := by
    refine QuadraticAlgebra.ext (by simp) (neg_neg _)
  star_mul a b := by ext <;> simp <;> ring
  star_add _ _ := QuadraticAlgebra.ext (by simp [star_x]; ring) (neg_add _ _)

instance nontrivial [Nontrivial R] :
    Nontrivial (QuadraticAlgebra a b) :=
  ⟨⟨0, 1, QuadraticAlgebra.ext_iff.not.mpr (by simp)⟩⟩

instance [CharZero R] : CharZero (QuadraticAlgebra a b) where
  cast_injective m n := by
    simp [QuadraticAlgebra.ext_iff]

@[simp]
theorem nsmul_val (n : ℕ) (x y : ℤ) :
    (n : QuadraticAlgebra a b) * ⟨x, y⟩ = ⟨n * x, n * y⟩ := by
  ext <;> simp

@[simp]
theorem smul_val (n x y : ℤ) :
    (n : QuadraticAlgebra a b) * ⟨x, y⟩ = ⟨n * x, n * y⟩ := by
  ext <;> simp

theorem omega_mul_omega :
    (omega : QuadraticAlgebra a b) * (omega) = ⟨-b, -a⟩ := by
  ext <;> simp [pow_two]

@[simp]
theorem omega_mul (x y : R) :
    (omega : QuadraticAlgebra a b) * ⟨x, y⟩ = ⟨-b * y, x - a * y⟩ := by
  ext <;> simp

/-- The ring morphism from `R` to `QuadraticAlgebra a b` -/
def coe_ringHom : R →+* QuadraticAlgebra a b where
  toFun r := r
  map_zero' := coe_zero
  map_add' := coe_add
  map_one' := coe_one
  map_mul' := coe_mul

@[simp]
theorem coe_ringHom_apply (r : R) :
    (coe_ringHom r : QuadraticAlgebra a b) = r := rfl

/-- The algebra structure of `QuadraticAlgebra a b`. -/
instance : Algebra R (QuadraticAlgebra a b) where
  smul n z := (n : QuadraticAlgebra a b) * z
  smul_def' r z := by rfl
  algebraMap := coe_ringHom
  commutes' r z := by ext <;> simp [mul_comm]

theorem smul_eq_coe_mul (r : R) (z : QuadraticAlgebra a b) :
    r • z = (r : QuadraticAlgebra a b) * z := rfl

theorem coe_apply (r : R) : (r : QuadraticAlgebra a b) = ⟨r, 0⟩ := rfl

theorem coe_eq_algebraMap (r : R) :
    (r : QuadraticAlgebra a b) = algebraMap R _ r := rfl

theorem algebraMap_apply (r : R) :
    (algebraMap R (QuadraticAlgebra a b)) r = r := rfl

@[simp]
theorem smul_x (r : R) (z : QuadraticAlgebra a b) :
    (r • z).x = r * z.x := by
  simp [Algebra.smul_def, algebraMap_apply]

@[simp]
theorem smul_y (r : R) (z : QuadraticAlgebra a b) :
    (r • z).y = r * z.y := by
  simp [Algebra.smul_def, algebraMap_apply]

@[simp]
theorem omega_mul_coe_mul (n x y : R) :
    (omega : QuadraticAlgebra a b) * (↑n) * ⟨x, y⟩ = ⟨-b * n * y, n * x - n * a * y⟩ := by
  ext
  · -- x component
    -- sorry
    simp [omega_mul, coe_apply]
    -- sorry
  · -- y component
    -- sorry
    simp [omega_mul, coe_apply]; ring
    -- sorry

theorem omega_prop :
    (ω) * (ω) + (a : QuadraticAlgebra a b) * (ω : QuadraticAlgebra a b) + (b : QuadraticAlgebra a b) = 0 := by
  -- sorry
  ext <;> simp [omega]
  -- sorry

theorem omega_prop' :
    (ω : QuadraticAlgebra a b) * (ω) + a • (ω) + b • 1 = 0 := by
  simp [smul_eq_coe_mul, omega_prop]

theorem decompose {x y : R} :
    (⟨x, y⟩ : QuadraticAlgebra a b) = x + y • (ω : QuadraticAlgebra a b) := by
  ext <;> simp [coe_apply]

theorem mul_star {x y : R} :
    (⟨x, y⟩ * star ⟨x, y⟩ : QuadraticAlgebra a b) =
      x * x - a * x * y + b * y * y := by
  ext <;> simp [mul_comm, algebraMap_apply] <;> ring

theorem coe_dvd_iff {r : R} {z : QuadraticAlgebra a b} :
    ↑r ∣ z ↔ r ∣ z.x ∧ r ∣ z.y := by
  -- sorry
  constructor
  · rintro ⟨x, rfl⟩
    simp [dvd_mul_right, and_self_iff, algebraMap_apply]
  · rintro ⟨⟨r, hr⟩, ⟨i, hi⟩⟩
    use ⟨r, i⟩
    simp [algebraMap_apply, QuadraticAlgebra.ext_iff, hr, hi]
  -- sorry

@[simp, norm_cast]
theorem coe_dvd_ofSelf (z w : R) :
    (z : QuadraticAlgebra a b) ∣ w ↔ z ∣ w := by
  -- sorry
  rw [coe_dvd_iff]
  constructor
  · rintro ⟨hx, -⟩
    simpa [algebraMap_apply] using hx
  · simp [algebraMap_apply]
  -- sorry

section Norm

/-- The norm of an element of `QuadraticAlgebra a b`. -/
def norm (z : QuadraticAlgebra a b) : R :=
  z.x * z.x - a * z.x * z.y + b * z.y * z.y

theorem norm_def (z : QuadraticAlgebra a b) :
    z.norm = z.x * z.x - a * z.x * z.y + b * z.y * z.y :=
  rfl

@[simp]
theorem norm_zero : norm (0 : QuadraticAlgebra a b) = 0 := by simp [norm]

@[simp]
theorem norm_one : norm (1 : QuadraticAlgebra a b) = 1 := by simp [norm]

@[simp]
theorem norm_coe (r : R) : norm (r : QuadraticAlgebra a b) = r * r := by simp [norm_def, algebraMap_apply]

@[simp]
theorem norm_natCast (n : ℕ) : norm (n : QuadraticAlgebra a b) = n * n :=
  by simp [norm_def]

@[simp]
theorem norm_intCast (n : ℤ) : norm (n : QuadraticAlgebra a b) = n * n :=
  by simp [norm_def]

@[simp]
theorem norm_mul (z w : QuadraticAlgebra a b) :
    norm (z * w) = norm z * norm w := by
  -- sorry
  simp only [norm_def, mul_x, mul_y]
  ring
  -- sorry

/-- `norm` as a `MonoidHom`. -/
def normMonoidHom : QuadraticAlgebra a b →* R where
  toFun := norm
  map_mul' := norm_mul
  map_one' := norm_one

theorem normMonoidHom_apply (r : QuadraticAlgebra a b) :
    normMonoidHom r = norm r := rfl

theorem coe_norm_eq_mul_conj (z : QuadraticAlgebra a b) :
    ((norm z : R) : QuadraticAlgebra a b) = z * star z := by
  -- sorry
  ext <;> simp [norm, star, mul_comm, algebraMap_apply] <;> ring
  -- sorry

@[simp]
theorem norm_neg (x : QuadraticAlgebra a b) : (-x).norm = x.norm := by
  simp [norm]

@[simp]
theorem norm_conj (x : QuadraticAlgebra a b) : (star x).norm = x.norm := by
  simp [norm]; ring

theorem isUnit_iff_norm_isUnit {x : QuadraticAlgebra a b} :
    IsUnit x ↔ IsUnit (x.norm) := by
  constructor
  · exact IsUnit.map normMonoidHom
  -- sorry
  · simp only [isUnit_iff_exists]
    rintro ⟨r, hr, hr'⟩
    rw [← coe_inj (R := R) (a := a) (b := b), coe_mul, coe_norm_eq_mul_conj , mul_assoc, coe_one] at hr
    refine ⟨_, hr, ?_⟩
    rw [mul_comm, hr]
  -- sorry

/-- An element of `QuadraticAlgebra a b` has norm equal to `1` if and only if it is contained in the submonoid
of unitary elements. -/
theorem norm_eq_one_iff_mem_unitary {z : QuadraticAlgebra a b} :
    z.norm = 1 ↔ z ∈ unitary (QuadraticAlgebra a b) := by
  -- sorry
  rw [unitary.mem_iff_self_mul_star, ← coe_norm_eq_mul_conj, coe_eq_one_iff]
  -- sorry

/-- The kernel of the norm map on `QuadraticAlgebra a b` equals the submonoid of unitary elements. -/
theorem mker_norm_eq_unitary :
    MonoidHom.mker (@normMonoidHom R _ a b) = unitary (QuadraticAlgebra a b) :=
  Submonoid.ext fun _ => norm_eq_one_iff_mem_unitary

theorem coe_mem_nonZeroDivisors_iff {r : R} :
    (r : QuadraticAlgebra a b) ∈ nonZeroDivisors _ ↔ r ∈ nonZeroDivisors R := by
  simp only [mem_nonZeroDivisors_iff]
  -- sorry
  constructor
  · intro H x hxr
    rw [← coe_inj, coe_zero]
    apply H
    rw [← coe_mul, hxr, coe_zero]
  · intro h z hz
    rw [QuadraticAlgebra.ext_iff, zero_x, zero_y] at hz
    simp only [mul_comm z, ← smul_eq_coe_mul, smul_x, smul_y, mul_comm r] at hz
    simp [QuadraticAlgebra.ext_iff, h _ hz.left, h _ hz.right]
  -- sorry

theorem conj_mem_nonZeroDivisors {z : QuadraticAlgebra a b}
    (hz : z ∈ nonZeroDivisors _) : star z ∈ nonZeroDivisors _ :=  by
  -- sorry
  rw [mem_nonZeroDivisors_iff] at hz ⊢
  intro w hw
  apply star_involutive.injective
  rw [star_zero]
  apply hz
  rw [← star_involutive z, ← star_mul, mul_comm, hw, star_zero]
  -- sorry

theorem conj_mem_nonZeroDivisors_iff {z : QuadraticAlgebra a b} :
    star z ∈ nonZeroDivisors _ ↔ z ∈ nonZeroDivisors _ := by
  -- sorry
  refine ⟨fun h ↦ ?_, conj_mem_nonZeroDivisors⟩
  rw [← star_involutive z]
  exact conj_mem_nonZeroDivisors h
  -- sorry

theorem norm_mem_nonZeroDivisors_iff {z : QuadraticAlgebra a b} :
    z.norm ∈ nonZeroDivisors R ↔ z ∈ nonZeroDivisors _ := by
  -- sorry
  constructor
  · simp only [mem_nonZeroDivisors_iff]
    intro h w hw
    have : norm z • w = 0 := by
      rw [smul_eq_coe_mul, coe_norm_eq_mul_conj, mul_comm, ← mul_assoc, hw, zero_mul]
    simp only [QuadraticAlgebra.ext_iff, smul_x, zero_x, smul_y, zero_y, mul_comm] at this
    ext <;> simp only [zero_x, zero_y, h _ this.left, h _ this.right]
  · intro hz
    rw [← coe_mem_nonZeroDivisors_iff, coe_norm_eq_mul_conj]
    exact Submonoid.mul_mem _ hz (conj_mem_nonZeroDivisors hz)
  -- sorry

end Norm

variable {A : Type*} [Ring A] [Algebra R A]

@[ext]
theorem hom_ext {f g : QuadraticAlgebra a b →ₐ[R] A}
    (h : f (ω) = g (ω)) : f = g := by
  ext ⟨x, y⟩
  simp [decompose, h, coe_eq_algebraMap, AlgHom.commutes, h]

/-- The unique `AlgHom` from `QuadraticAlgebra a b` to an `R`-algebra `A`,
constructed by replacing `ω` with the provided root.
Conversely, this associates to every algebra morphism `QuadraticAlgebra a b →ₐ[R] A` a value of `ω` in `A`. -/
@[simps]
def lift : { u : A // u * u + a • u + b • 1  = 0 } ≃ (QuadraticAlgebra a b →ₐ[R] A) where
  toFun u :=
    { toFun z := z.1 • 1 + z.2 • u
      map_zero' := by simp
      map_add' z w := by
        simp only [add_x, add_y, add_smul, ← add_assoc]
        congr 1
        simp only [add_assoc]
        congr 1
        rw [add_comm]
      map_one' := by simp
      map_mul' z w := by
        have u_prop : (u : A) * u = - (b • 1 + a • u) := by
          -- sorry
          rw [← sub_eq_zero, sub_neg_eq_add, add_comm (b • 1), ← add_assoc, u.prop]
          -- sorry
        symm
        -- the `module` tactic can be useful here !
        -- sorry
        calc
          (z.x • (1 : A) + z.y • ↑u) * (w.x • 1 + w.y • ↑u) =
              (z.x * w.x) • (1 : A) + (z.x * w.y) • u + (z.y * w.x) • u + (z.y * w.y) • (u * u) := by
              simp only [mul_add, mul_one, smul_add, add_mul,
                one_mul, ← add_assoc, smul_mul_smul]
              apply add_add_add_comm'
            _ = (z.x * w.x) • (1 : A) + (z.x * w.y+ z.y * w.x) • u + (z.y * w.y) • (u * u) := by
              congr 1
              simp only [add_assoc]
              rw [← add_smul]
            _ = (z.x * w.x) • 1 + (z.x * w.y + z.y * w.x) • u
                  - (z.y * w.y) • (a • u + b • 1) := by
              rw [u_prop, smul_neg, ← sub_eq_add_neg, add_comm (b • 1)]
            _ = (z.x * w.x - b * z.y * w.y) • 1 + (z.x * w.y + z.y * w.x- a * z.y * w.y) • u := by
              rw [smul_add, ← sub_sub, ← add_sub, ← mul_smul, ← sub_smul]
              rw [← sub_add_eq_add_sub, ← mul_smul, ← sub_smul]
              congr 3 <;> ring
            _ = (z * w).x • 1 + (z * w).y • u := by
              rw [← mul_x, ← mul_y]
        -- sorry
      commutes' r := by
        -- sorry
        simp only [algebraMap_apply, coe_x, coe_y, zero_smul, add_zero,   ← Algebra.algebraMap_eq_smul_one]
        -- sorry
        }
  invFun f := ⟨f (ω), by
    -- sorry
    rw [← map_mul, ← map_smul, ← map_add, ← map_one f, ← map_smul, ← map_add, omega_prop', map_zero]
    -- sorry
    ⟩
  left_inv r := by
    -- sorry
    simp
    -- sorry
  right_inv f := by
    -- sorry
    ext
    simp
    -- sorry

end QuadraticAlgebra
