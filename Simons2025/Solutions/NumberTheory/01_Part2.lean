/- A formalization of the exercises in the book by Ireland & Rosen,
   *A classical introduction to number theory*
   Antoine Chambert-Loir, 2025 -/

import Mathlib

/- #Chapter 1. Unique factorization -/

/-! ## Exercise 6
  Let a, b, c ∈ ℤ.
  Show that the equation ax + by= c has solutions in integers
  iff (a, b) ∣ c. -/

example (a b c : ℤ) :
    (∃ (x y : ℤ), a * x + b * y = c) ↔ ((a.gcd b) : ℤ) ∣ c := by
  constructor
  · intro ⟨x, y, eq⟩
    -- You can use `Int.dvd_add`, `Int.gcd_dvd_left`, `Int.gcd_dvd_right`
    -- sorry --
    rw [← eq]
    apply Int.dvd_add
    · trans a
      exact Int.gcd_dvd_left a b
      exact Int.dvd_mul_right a x
    · trans b
      exact Int.gcd_dvd_right a b
      exact Int.dvd_mul_right b y
    -- sorry --
  · intro ⟨k, eq⟩
    -- sorry
    use a.gcdA b * k, a.gcdB b * k
    rw [eq, ← mul_assoc, ← mul_assoc, ← add_mul, Int.gcd_eq_gcd_ab]
    -- sorry --

/-! ## Exercise 7.
  Let d = (a, b) and a = da' and b = db'. Show that (a', b') = 1. -/

example : ∃ (a b : ℤ), Int.gcd (a / a.gcd b) (b / a.gcd b) ≠ 1 := by
  -- don't hesitate to check that the tactic `simp` is sometimes powerful enough
  -- sorry --
  use 0, 0
  simp
  -- sorry --

example (a b : ℤ) (H : a ≠ 0 ∨ b ≠ 0) :
    Int.gcd (a / a.gcd b) (b / a.gcd b) = 1 := by
  have H' : a.gcd b ≠ 0 := by
    -- sorry --
    rwa [ne_eq, Int.gcd_eq_zero_iff, not_and_or]
    -- sorry --
  set a' := a / a.gcd b
  have ha : a = a' * a.gcd b := by
    -- sorry --
    simp only [a']
    apply Int.eq_mul_div_of_mul_eq_mul_of_dvd_left
    · exact Int.ofNat_ne_zero.mpr H'
    · exact Int.gcd_dvd_left a b
    · exact Int.mul_comm (↑(a.gcd b)) a
    -- sorry --
  set b' := b / a.gcd b
  have hb : b = b' * a.gcd b := by
    -- sorry --
    simp only [b']
    apply Int.eq_mul_div_of_mul_eq_mul_of_dvd_left
    exact Int.ofNat_ne_zero.mpr H'
    exact Int.gcd_dvd_right a b
    exact Int.mul_comm (↑(a.gcd b)) b
    -- sorry --
  -- sorry --
  rw [← Nat.mul_left_inj H', one_mul]
  nth_rewrite 2 [hb, ha]
  simp [Int.gcd_mul_right]
  -- sorry --

/-! ## Exercise 8.
  Let Xo and Yo be a solution to ax + by= c.
  Show that all solutions have the form
    x = Xo + t(b/d), Y= Yo - t(a/d), where d = (a, b) and t ∈ ℤ. -/

-- This one was a bit tough for me…

example (a b c d : ℤ) (d_def : d = a.gcd b) (hd₀ : d ≠ 0)
    (x₀ y₀ : ℤ) (eq₀ : a * x₀ + b * y₀ = c) (x y : ℤ) :
    a * x + b * y = c ↔
      ∃ t, x = x₀ + t * (b / d) ∧ y = y₀ - t * (a / d) := by
  -- sorry --
  set b' := b / d with hb'
  set a' := a / d with ha'
  have ha : a = a' * d := by
    simp [ha']
    refine Int.eq_mul_div_of_mul_eq_mul_of_dvd_left hd₀ ?_ ?_
    simp [d_def]; exact Int.gcd_dvd_left a b
    rw [mul_comm]
  have hb : b = b' * d := by
    simp [hb']
    refine Int.eq_mul_div_of_mul_eq_mul_of_dvd_left hd₀ ?_ ?_
    simp [d_def]; exact Int.gcd_dvd_right a b
    rw [mul_comm]
  have hd' : a'.gcd b' = 1 := by
    simp [ha', hb', d_def]
    refine Int.gcd_ediv_gcd_ediv_gcd ?_
    refine Int.gcd_pos_iff.mpr ?_
    simpa only [d_def, ne_eq, Int.natCast_eq_zero,
      Int.gcd_eq_zero_iff, not_and_or] using hd₀
  constructor
  · intro eq
    have H : a' * (x - x₀) = -b' * (y - y₀) := by
      rw [← mul_right_inj' hd₀]
      rw [← mul_assoc, mul_comm d, ← ha]
      rw [← mul_assoc, mul_comm d, neg_mul, ← hb]
      rw [← sub_eq_zero, neg_mul, sub_neg_eq_add]
      rw [mul_sub, mul_sub]
      rw [sub_add_sub_comm]
      rw [eq, eq₀, sub_self]
    have Ha' : a' ∣ y - y₀ := by
      apply Int.dvd_of_dvd_mul_right_of_gcd_one
      rw [← H]
      exact Int.dvd_mul_right a' (x - x₀)
      simp only [Int.gcd_neg, hd']
    have Hb' : b' ∣ x - x₀ := by
      apply Int.dvd_of_dvd_mul_right_of_gcd_one
      rw [H, neg_mul, dvd_neg]
      exact Int.dvd_mul_right b' (y - y₀)
      rw [Int.gcd_comm, hd']
    obtain ⟨t, ht⟩ := Hb'
    obtain ⟨u, hu⟩ := Ha'
    rw [ht, hu, neg_mul, eq_neg_iff_add_eq_zero,
      ← mul_assoc, ← mul_assoc, mul_comm b', ← mul_add] at H
    simp only [mul_eq_zero] at H
    rcases H with H | H
    · rcases H with H | H
      · -- case a = 0
        simp [H, sub_eq_zero] at hu hd'
        simp [H, hu]
        use (x - x₀) * b'
        simp [mul_assoc, ← pow_two, ← Int.natAbs_sq, hd']
      · -- case b = 0
        simp [H, sub_eq_zero] at ht hd'
        simp [H, ht]
        use (y₀ - y) * a'
        simp [mul_assoc, ← pow_two, ← Int.natAbs_sq, hd']
    · use t
      constructor
      · rw [mul_comm, ← ht]; ring
      · rw [← eq_neg_iff_add_eq_zero] at H
        simp [H, mul_comm u, ← hu]
  · rintro ⟨t, hx, hy⟩
    rw [hx, hy, ← eq₀, ha, hb]; ring
  -- sorry --

/-! ## Exercise 9.
  Suppose that u, v ∈ ℤ and that (u, v)= 1.
  If u ∣ n and v ∣ n,show that uv ∣ n.
  Show that this is false if (u, v) ≠ 1. -/

example (u v n : ℤ) (huv : u.gcd v = 1) (hu : u ∣ n) (hv : v ∣ n) :
    u * v ∣ n := by
  -- sorry --
  obtain ⟨a, ha⟩ := hu
  rw [ha] at hv ⊢
  refine Int.mul_dvd_mul_left u ?_
  apply Int.dvd_of_dvd_mul_right_of_gcd_one hv
  rwa [Int.gcd_comm]
  -- sorry --

example : ∃ (u v n : ℤ) (hu : u ∣ n) (hv : v ∣ n), ¬ (u * v ∣ n) := by
  -- sorry --
  use 2, 2, 2
  simp
  -- sorry --

/-! ## Exercise 10.
  Suppose that (u, v)= 1. Show that (u + v, u- v) is either 1 or 2.-/

-- What do the following examples say?

example (d : ℕ) (h1 : 1 ≤ d) : d = 1 ∨ 2 ≤ d := by
  rw [Nat.le_iff_lt_or_eq] at h1
  rcases h1 with h1 | h1
  · right
    exact h1
  · left
    exact h1.symm

example (d : ℕ) (h1 : 1 ≤ d) (h2 : d ≤ 2) : d = 1 ∨ d = 2 := by
  rw [Nat.le_iff_lt_or_eq] at h1
  rcases h1 with h1 | h1
  · right
    apply le_antisymm h2 h1
  · left
    exact h1.symm

-- Now for the exercise

example (u v : ℤ) (huv : u.gcd v = 1) :
    (u + v).gcd (u - v) = 1 ∨ (u + v).gcd (u - v) = 2 := by
  -- sorry --
  set d := (u + v).gcd (u - v) with hd
  have hd0 : d ≠ 0 := by
    intro hd0
    suffices u = 0 ∧ v = 0 by
      rw [← Int.gcd_eq_zero_iff, huv] at this
      exact Nat.one_ne_zero this
    simp [hd] at hd0
    rw [← eq_neg_iff_add_eq_zero, sub_eq_zero] at hd0
    suffices v = 0 by
      simp [this, hd0]
    suffices v = -v by
      simpa [eq_neg_iff_add_eq_zero, add_self_eq_zero] using this
    nth_rewrite 1 [← hd0.2]
    exact hd0.1
  simp only [← Nat.one_le_iff_ne_zero] at hd0
  suffices d ≤ 2 by
    rw [Nat.le_iff_lt_or_eq] at this
    rcases this with h1 | h2
    · left
      apply le_antisymm _ hd0
      exact Nat.le_of_lt_succ h1
    · right
      exact h2
  apply Nat.le_of_dvd
  norm_num
  have h1 : (d : ℤ) ∣ (u + v) := by
    simp [hd]
    exact Int.gcd_dvd_left (u + v) (u - v)
  have h2 : (d : ℤ) ∣ (u - v) := by
    simp [hd]
    exact Int.gcd_dvd_right (u + v) (u - v)
  suffices  ↑d ∣ 2 * u ∧ ↑d ∣ 2 * v by
    simpa [← Int.dvd_gcd_iff, Int.gcd_mul_left, huv] using this
  constructor
  · convert Int.dvd_add h1 h2 using 1; ring
  · convert Int.dvd_sub h1 h2 using 1; ring
  -- sorry --

/-! ## Exercise 11
  Show that (a, a + k) ∣ k. -/

-- Here, we learn a new tactic `suffices`:
-- It allows to accept something temporarily, and to prove it afterwards

example (a k : ℤ) : (a.gcd (a + k) : ℤ) ∣ k := by
  suffices a.gcd (a + k) = a.gcd k by
    -- conclude the proof assuming `this : a.gcd (a + k) = a.gcd k`
    -- sorry --
    rw [this]
    exact Int.gcd_dvd_right a k
    -- sorry --
  -- Actually, Mathlib knows about this
  -- You can guess the name or try `apply?`
  exact Int.gcd_self_add_right a k
