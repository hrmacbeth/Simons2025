/- A formalization of the exercises in the book by Ireland & Rosen,
   *A classical introduction to number theory*
   Antoine Chambert-Loir, 2025 -/

import Mathlib

/- #Chapter 1. Unique factorization -/

/-! ## Exercise 1.
Let a and b be nonzero integers.
We can find nonzero integers q and r such that a = qb + r,
where 0 ≤ r < b. Prove that (a, b)= (b, r). -/

example (a b : ℕ) (hb_ne_zero : b ≠ 0) :
    ∃ (q r : ℕ), a = q * b + r ∧ r < b ∧ a.gcd b = b.gcd r := by
  set q := a / b
  set r := a % b
  have eq : a = q * b + r := by
    -- sorry --
    conv_lhs => rw [← Nat.div_add_mod a b, mul_comm]
  -- sorry --
  use q, r, eq
  constructor
  · -- The remainder is less than b
    -- sorry --
    apply Nat.mod_lt
    exact Nat.zero_lt_of_ne_zero hb_ne_zero
    -- sorry
  · -- Equality of gcd's
    -- sorry --
    rw [Nat.gcd_comm, eq]
    exact Nat.gcd_mul_right_add_right b r q
    -- sorry --

/-! ## Exercice 2. (continuation)
  If r > 0, we can find q₁ and r₁ such that
  b= q₁ * r + r₁ with 0 ≤ r₁ < r. Show that (a, b)= (r, r₁).
  This process can be repeated.
  Show that it must end in finitely many steps.
  Show that the last nonzero remainder must equal (a, b).
  The process looks like
    a = q * b + r,
    b = q₁ * r + r₁, …
  Then r_{k+1} = (a, b).
  This process of finding (a, b) is known as the Euclidean algorithm.
  -/

#check Nat.gcd
#check Int.gcd

/-! ## Exercise 3.
  Calculate (187, 221), (6188, 4709), and (314.159). -/

#eval Nat.gcd 187 221 -- 17
#eval Nat.gcd 6188 4709 -- 17
#eval Nat.gcd 314 159 -- 1

/-! ## Exercise 4.
  Let d= (a. b).
  Show how one can use the Euclidean algorithm to find numbers
  m and n such that am + bn = d. -/

#check Int.gcd
#check Int.gcdA
#check Int.gcdB
#check Int.gcd_eq_gcd_ab

/-! ## Exercise 5
  Calculate m and n for the examples of exercise 3 -/

#eval (Int.gcdA 187 221, Int.gcdB 187 221) -- (6, -5)
#eval 6 * 187 - 5 * 221 == 17

#eval (Int.gcdA 6188 4709, Int.gcdB 6188 4709) -- (121, -159)

#eval (Int.gcdA 314 159, Int.gcdB 314 159) -- (-40, 79)

/-! ## Exercise 6
  Let a, b, c ∈ ℤ.
  Show that the equation ax + by= c has solutions in integers
  iff (a, b) ∣ c. -/

example (a b c : ℤ) :
    (∃ (x y : ℤ), a * x + b * y = c) ↔ ((a.gcd b) : ℤ) ∣ c := by
  constructor
  · intro ⟨x, y, eq⟩
    rw [← eq]
    apply Int.dvd_add
    · trans a
      exact Int.gcd_dvd_left a b
      exact Int.dvd_mul_right a x
    · trans b
      exact Int.gcd_dvd_right a b
      exact Int.dvd_mul_right b y
  · intro hyp
    obtain ⟨k, eq⟩ := hyp
    use a.gcdA b * k, a.gcdB b * k
    rw [eq, ← mul_assoc, ← mul_assoc, ← add_mul, Int.gcd_eq_gcd_ab]

/-! ## Exercise 7.
  Let d = (a, b) and a = da' and b = db'. Show that (a', b') = 1. -/

example : ∃ (a b : ℤ), Int.gcd (a / a.gcd b) (b / a.gcd b) ≠ 1 := by
  use 0, 0
  simp

example (a b : ℤ) (H : a ≠ 0 ∨ b ≠ 0) :
    Int.gcd (a / a.gcd b) (b / a.gcd b) = 1 := by
  have H' : a.gcd b ≠ 0 := by
    rwa [ne_eq, Int.gcd_eq_zero_iff, not_and_or]
  set a' := a / a.gcd b
  have ha : a = a' * a.gcd b := by
    simp only [a']
    apply Int.eq_mul_div_of_mul_eq_mul_of_dvd_left
    · exact Int.ofNat_ne_zero.mpr H'
    · exact Int.gcd_dvd_left a b
    · exact Int.mul_comm (↑(a.gcd b)) a
  set b' := b / a.gcd b
  have hb : b = b' * a.gcd b := by
    simp only [b']
    apply Int.eq_mul_div_of_mul_eq_mul_of_dvd_left
    exact Int.ofNat_ne_zero.mpr H'
    exact Int.gcd_dvd_right a b
    exact Int.mul_comm (↑(a.gcd b)) b
  rw [← Nat.mul_left_inj H', one_mul]
  nth_rewrite 2 [hb, ha]
  simp [Int.gcd_mul_right]

#check Int.gcd_div_gcd_div_gcd

/-! ## Exercise 8.
  Let Xo and Yo be a solution to ax + by= c.
  Show that all solutions have the form
    x = Xo + t(b/d), Y= Yo - t(a/d), where d = (a, b) and t ∈ ℤ. -/

example (a b c d : ℤ) (d_def : d = a.gcd b) (hd₀ : d ≠ 0)
    (x₀ y₀ : ℤ) (eq₀ : a * x₀ + b * y₀ = c) (x y : ℤ) :
    a * x + b * y = c ↔
      ∃ t, x = x₀ + t * (b / d) ∧ y = y₀ - t * (a / d) := by
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

/-! ## Exercise 9.
  Suppose that u, v ∈ ℤ and that (u, v)= 1.
  If u ∣ n and v ∣ n,show that uv ∣ n.
  Show that this is false if (u, v) ≠ 1. -/

example (u v n : ℤ) (huv : u.gcd v = 1) (hu : u ∣ n) (hv : v ∣ n) :
    u * v ∣ n := by
  obtain ⟨a, ha⟩ := hu
  rw [ha] at hv ⊢
  refine Int.mul_dvd_mul_left u ?_
  apply Int.dvd_of_dvd_mul_right_of_gcd_one hv
  rwa [Int.gcd_comm]

example : ∃ (u v n : ℤ) (hu : u ∣ n) (hv : v ∣ n), ¬ (u * v ∣ n) := by
    use 2, 2, 2
    simp

/-! ## Exercise 10.
  Suppose that (u. v)= 1. Show that (u + v, u- v) is either 1 or 2.-/

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

example (u v : ℤ) (huv : u.gcd v = 1) :
    (u + v).gcd (u - v) = 1 ∨ (u + v).gcd (u - v) = 2 := by
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

/-! ## Exercise 11
  Show that (a, a + k) ∣ k. -/

example (a k : ℤ) : (a.gcd (a + k) : ℤ) ∣ k := by
  suffices a.gcd (a + k) = a.gcd k by
    rw [this]
    exact Int.gcd_dvd_right a k
  exact Int.gcd_self_add_right a k

/-! ## Exercise 12
  Suppose that we take several copies of a regular polygon and try
  to fit them evenly about a common vertex.  Prove that the only
  possibilities are six equilateral triangles, four squares, and
  three hexagons. -/

-- The sum of the inner angles of a polygon with n vertices
-- is (n-2)π, so that the inner angle is (1-2/n)π
-- the equation is m (1-2/n)π = 2π
-- hence m(n-2)=2n : m * n = 2 * (m + n)

example (m n : ℕ) (H : m * n = 2 * (m + n)) :
    (m = 6 ∧ n = 3) ∨ (m = 4 ∧ n = 4) ∨ (m = 3 ∧ n = 6)
      ∨ (m = 0 ∧ n = 0) := by
  rcases m.eq_zero_or_pos with hm0 | hm1
  · simp [hm0] at H; simp [hm0, H]
  rcases LE.le.eq_or_gt (α := ℕ) hm1 with hm1 | hm2
  · exfalso
    simp [hm1] at H
    apply lt_irrefl n
    nth_rewrite 2 [H]
    rw [add_comm, two_mul, add_assoc]
    apply lt_add_of_le_of_pos
    · exact Nat.le_refl n
      -- or `rfl` tactic
    · exact Nat.zero_lt_succ (Nat.add 1 n)
  replace hm2 : 2 ≤ m := hm2
  have H' : (m - 2) * (n - 2) = 2 * 2 := by
    rw [Nat.mul_sub, Nat.sub_mul, H]
    rw [mul_add]
    simp only [add_tsub_cancel_right]
    rw [mul_comm _ 2, Nat.mul_sub]
    apply Nat.sub_sub_self
    exact Nat.mul_le_mul_left 2 hm2
  have : m - 2 ∣ 2 ^ 2 := by
    exact Dvd.intro (n - 2) H'
  rw [Nat.dvd_prime_pow Nat.prime_two] at this
  obtain ⟨k, hk, hm⟩ := this
  rw [Nat.sub_eq_iff_eq_add' hm2] at hm
  rcases k.eq_zero_or_pos with hk0 | hk1
  · simp [hm, hk0] at H' ⊢
    rwa [Nat.sub_eq_iff_eq_add'] at H'
    refine le_of_lt (Nat.lt_of_sub_pos ?_)
    rw [H']; norm_num
  rcases LE.le.eq_or_gt (α := ℕ) hk1 with hk1 | hk2
  · simp [hm, hk1] at H' ⊢
    change 2 * (n - 2) = 2 * 2 at H'
    rwa [Nat.mul_right_inj, Nat.sub_eq_iff_eq_add'] at H'
    · refine le_of_lt (Nat.lt_of_sub_pos ?_)
      rw [H']; norm_num
    · norm_num
  · replace hk2 : k = 2 := le_antisymm hk hk2
    simp [hm, hk2] at H' ⊢
    rwa [Nat.sub_eq_iff_eq_add'] at H'
    refine le_of_lt (Nat.lt_of_sub_pos ?_)
    rw [H']; norm_num

/-! ## Exercise 27.
   For all odd n show that 8 ∣ n^2 - 1.
   If 3 ∤ n, show that 6 ∣ n ^ 2 - 1.
-/

example (n : ℤ) (hn : Odd n) : 8 ∣ n ^ 2 - 1 := by
  obtain ⟨p, rfl⟩ := hn
  rw [show (2 * p + 1) ^ 2 - 1 = 4 * (p * (p + 1)) by ring]
  rw [show (8 : ℤ) = 4 * 2 by norm_num]
  refine Int.mul_dvd_mul_left 4 ?_
  apply Even.two_dvd
  exact Int.even_mul_succ_self p

example (m : ℕ) (n : ℤ) : (n : ZMod m) = 0 ↔ (m : ℤ) ∣ n := by
  exact ZMod.intCast_zmod_eq_zero_iff_dvd n m

example (n : ℤ) (hn : Odd n) : 8 ∣ n ^ 2 - 1 := by
  change ((8 : ℕ) : ℤ) ∣ n ^ 2 - 1
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [Int.cast_sub, Int.cast_pow, Int.cast_one, sub_eq_zero]
  obtain ⟨n, rfl⟩ := hn
  simp
  generalize hp : (n : ZMod 8) = p
  clear hp
  revert p
  decide

example (n : ℤ) (hn2 : Odd n) (hn3 : ¬ 3 ∣ n) :
    6 ∣ n ^ 2 - 1 := by
  set u := n.divModEquiv 6 with hu
  have hu' : n = u.1 * 6 + u.2 := by
    rwa [Equiv.apply_eq_iff_eq_symm_apply, Int.divModEquiv_symm_apply] at hu
  change ((6 : ℕ) : ℤ) ∣ _
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp [hu']
  set a := (u.1 : ZMod 6) with ha
  set b := (u.2 : ZMod 6) with hb
  simp [show (6 : ZMod 6) = 0 by rfl]
  have : Even (6 : ℤ) := by
    exact Int.even_iff.mpr rfl
  simp [hu', Int.odd_add', Int.even_mul,
    show Even (6 : ℤ) by exact Int.even_iff.mpr rfl,
    Nat.odd_iff] at hn2
  simp [hu'] at hn3
  match b with
  | 0 => simp at hn2
  | 1 => rfl
  | 2 => simp at hn2
  | 3 =>
    exfalso
    apply hn3
    apply Int.dvd_add
    · apply Dvd.dvd.mul_left; norm_num
    · use 1; norm_num; rfl
  | 4 =>
    change 4 % 2 = 1 at hn2
    simp at hn2
  | 5 => rfl

theorem isUnit_mod6 (n : ℕ) (hn2 : Odd n) (hn3 : ¬ 3 ∣ n) :
    IsUnit (n : ZMod 6) := by
  rw [ZMod.isUnit_iff_coprime]
  apply Nat.coprime_of_dvd
  intro p hp hpn hp6
  have pfl6 : Nat.primeFactorsList 6 = [2, 3] := by
    repeat
      change Nat.primeFactorsList (_ + 2) = _
      simp [Nat.primeFactorsList]
      norm_num
  have : p = 2 ∨ p = 3 := by
    suffices p ∈ Nat.primeFactors 6 by
      simpa [Nat.primeFactors, pfl6] using this
    simp [Nat.mem_primeFactors, hp6, hp]
  rcases this with h2 | h3
  · apply hn2.not_two_dvd_nat
    rwa [h2] at hpn
  · rw [h3] at hpn
    exact hn3 hpn

example (m : ℕ) (n : ℤ) : (m : ℤ) ∣ n ↔ m ∣ n.natAbs := by
  exact Int.ofNat_dvd_left

theorem int_isUnit_mod6 (n : ℤ) (hn2 : Odd n) (hn3 : ¬ 3 ∣ n) :
    IsUnit (n : ZMod 6) := by
  rw [ZMod.coe_int_isUnit_iff_isCoprime]
  rw [Int.isCoprime_iff_nat_coprime]
  simp only [Nat.cast_ofNat, Int.reduceAbs]
  rw [← Int.natAbs_odd, ← Nat.not_even_iff_odd, even_iff_two_dvd] at hn2
  rw [← Nat.cast_three, Int.ofNat_dvd_left] at hn3
  rw [← Nat.Prime.coprime_iff_not_dvd Nat.prime_two] at hn2
  rw [← Nat.Prime.coprime_iff_not_dvd Nat.prime_three] at hn3
  exact Nat.Coprime.mul hn2 hn3

example : Nat.primeFactorsList 198 = [2, 3, 3, 11] := by
  repeat
    simp [Nat.primeFactorsList]
    norm_num

example (n : ℤ) (hn2 : Odd n) (hn3 : ¬ 3 ∣ n) :
    6 ∣ n ^ 2 - 1 := by
  change ((6 : ℕ) : ℤ) ∣ _
  have hn : IsUnit (n : ZMod 6) := int_isUnit_mod6 n hn2 hn3
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp
  generalize hp : (n : ZMod 6) = p
  rw [hp] at hn
  clear hp
  revert p
  decide

example : Odd (5 : ZMod 6) := by
  simp [Odd]; decide

example (n : ℤ) (m : ℕ) (hm : Odd  m) : Even (n : ZMod m) :=
  sorry

example (n : ℤ) (m : ℕ) (hm : Even  m) :
    Even n ↔ Even (n : ZMod m) := by
  by_cases hn : Even n
  · obtain ⟨n, rfl⟩ := hn
    simp
  · rw [← not_iff_not]; simp [hn]
    rw [Int.not_even_iff_odd] at hn
    obtain ⟨n, rfl⟩ := hn
    rintro ⟨p, hp⟩
    simp only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_one, ← two_mul] at hp
    rw [add_comm, ← eq_sub_iff_add_eq, ← mul_sub] at hp
    obtain ⟨q, hq⟩ := hm
    rw [← two_mul] at hq
    have := congr_arg₂ HMul.hMul (refl (q : ZMod m)) hp
    rw [mul_one, ← mul_assoc, mul_comm _ 2] at this
    have that : 2 * (q : ZMod m) = ((2 * q : ℕ) : ZMod m) := by
      simp
    simp [that, ← hq] at this
    rw [ZMod.natCast_zmod_eq_zero_iff_dvd] at this
    suffices that : q < m by
      rw [← not_le] at that
      apply that (Nat.le_of_dvd _ this)
      rw [← not_le]
      intro hq'
      replace hq' : q = 0 := Nat.eq_zero_of_le_zero hq'
      simp [hq'] at hq
      simp [hq'] at that
      exact that hq
    rw [← not_le]
    intro hmq
    rw [hq] at hmq
    have : q = 0 := sorry
    simp [this] at hq
    sorry

/-! ## Exercise 29.
  Suppose that a, b, C, d ∈ ℤ and that (a, b)= (c, d) = 1.
  If (a/b) + (c/d)= an integer, show that b= ±d. -/

example (a b c d N : ℤ) (hb : b ≠ 0) (hd : d ≠ 0)
    (hab : a.gcd b = 1) (hcd : c.gcd d = 1)
    (H : (a / b : ℚ) + c / d = N) :
    b = d ∨ b = -d := by
  have H' : a * d + b * c = N * b * d := by
    rw [← Int.cast_inj (α := ℚ)]
    simp only [Int.cast_mul, Int.cast_add, ← H]
    simp [add_mul]
    apply congr_arg₂
    · apply congr_arg₂ _ _ rfl
      rw [eq_comm, ← eq_div_iff_mul_eq]
      exact Rat.num_ne_zero.mp hb
    · rw [mul_assoc, mul_comm _ (d : ℚ), ← mul_assoc, mul_comm (b : ℚ)]
      apply congr_arg₂ _ _ rfl
      rw [eq_comm, ← eq_div_iff_mul_eq]
      exact Rat.num_ne_zero.mp hd
  refine Int.natAbs_eq_natAbs_iff.mp ?_
  apply Nat.dvd_antisymm
  · rw [Int.natAbs_dvd_natAbs]
    rw [Int.gcd_comm] at hab
    apply Int.dvd_of_dvd_mul_right_of_gcd_one (b := a) _ hab
    rw [← eq_sub_iff_add_eq] at H'
    rw [H']
    apply dvd_add
    · apply dvd_mul_of_dvd_left
      apply dvd_mul_left
    · rw [dvd_neg]
      apply dvd_mul_right
  · rw [Int.natAbs_dvd_natAbs]
    rw [Int.gcd_comm] at hcd
    apply Int.dvd_of_dvd_mul_left_of_gcd_one _ hcd
    rw [add_comm, ← eq_sub_iff_add_eq] at H'
    rw [H']
    apply dvd_add
    · apply dvd_mul_left
    · rw [dvd_neg]
      apply dvd_mul_left

/-! ## Exercise 29.
  For all n, 30 ∣ n ^ 5 - n and 42 ∣ n ^ 7 - n. -/

example (n : ℤ) : 30 ∣ n ^ 5 - n := by
  rw [← Lean.Omega.Int.natCast_ofNat, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [Int.cast_sub, Int.cast_pow]
  generalize (n : ZMod 30) = p
  revert p
  decide

example (n : ℤ) : 42 ∣ n ^ 7 - n := by
  rw [← Lean.Omega.Int.natCast_ofNat, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [Int.cast_sub, Int.cast_pow]
  generalize (n : ZMod 42) = p
  revert p
  decide

-- How would one generalize this exercise to any prime number?
-- To any integer?

/-! ## Exercise 30.
  1 + 1/2 + ... + 1/n is not an integer -/

def H (n : ℕ) : ℚ := (Finset.range (n + 1)).sum (fun x ↦ (1 / x : ℚ))

theorem Hpos (n : ℕ) (hn : 1 ≤ n) : 0 < H n := by
  induction n, hn using Nat.le_induction with
  | base => simp [H]; norm_num
  | succ n hn hind =>
    apply lt_trans hind
    simp only [H, Finset.sum_range_succ]
    simp only [one_div, Nat.cast_add, Nat.cast_one, lt_add_iff_pos_right, inv_pos]
    exact Nat.cast_add_one_pos n

theorem padicValRat_H (n : ℕ) (hn : 1 ≤ n) :
    padicValRat 2 (H n) = - Nat.log 2 n := by
  induction n, hn using Nat.le_induction with
  | base =>
    simp [H]; norm_num
  | succ n hn hind =>
    have Hrec : H (n + 1) = H n + 1 / (n + 1 : ℚ) := by
      simp [H, Finset.sum_range_succ]
    rw [Hrec]
    -- There are two cases
    by_cases h : Nat.log 2 n < Nat.log 2 (n + 1)
    /- If `Nat.log 2 n < Nat.log 2 (n + 1),
      then the integer `n + 1` is of the form `2 ^ m`.
      This will imply that
      `padicValRat 2 (H n) > padicValRat 2 (1 / (n + 1))
       = - Nat.log 2 (n + 1)`
i     Then, `padivValRat 2 (H (n + 1)) = - Nat.log 2 (n + 1) . -/
    · have : padicValRat 2 (1 / (↑n + 1)) = - Nat.log 2 (n + 1) := by
        simp [one_div, padicValRat.inv]
        rw [← Nat.cast_one, ← Nat.cast_add, padicValRat.of_nat]
        simp only [Nat.cast_inj]
        rw [Nat.log_lt_log_succ_iff] at h
        nth_rewrite 1 [h]
        simp
        exact hn
      rw [add_comm, padicValRat.add_eq_of_lt]
      · exact this
      · apply ne_of_gt
        exact add_pos Nat.one_div_pos_of_nat (Hpos n hn)
      · simp
        rw [← Nat.cast_one, ← Nat.cast_add]
        exact NeZero.natCast_ne (n + 1) ℚ
      · exact ne_of_gt (Hpos n hn)
      · simp only [this, hind, neg_lt_neg_iff, Nat.cast_lt, h]
    /- Otherwise, one has `Nat.log 2 n = Nat.log 2 (n + 1),
      and `padicValRat 2 (H n) ≤ padicValRat 2 (1 / (n + 1))`.
      An explicit computation shows that their sum
      has `padicValRat (H (n + 1)) = padicValRat (H n). -/
    · replace h : Nat.log 2 n = Nat.log 2 (n + 1) := by
        simp only [not_lt] at h
        apply le_antisymm _ h
        apply Nat.log_monotone (Nat.le_add_right n 1)
      rw [eq_comm, padicValRat.add_eq_of_lt]
      · simp [hind, h]
      · suffices 0 < H n + 1/(n + 1 : ℚ) by
          exact Ne.symm (ne_of_lt this)
        apply lt_trans (Hpos n hn)
        simp only [one_div, lt_add_iff_pos_right, inv_pos]
        exact Nat.cast_add_one_pos n
      · apply (ne_of_lt (Hpos n hn)).symm
      · refine (ne_of_lt ?_).symm
        simp
        exact Nat.cast_add_one_pos n
      rw [hind]
      simp only [one_div, padicValRat.inv, neg_lt_neg_iff]
      rw [← Nat.cast_one, ← Nat.cast_add, ← padicValRat_of_nat,
        Nat.cast_lt]
      rw [h]
      rw [← not_le]
      intro h'
      replace h' : Nat.log 2 (n + 1) = padicValNat 2 (n + 1) := by
        apply le_antisymm h' (padicValNat_le_nat_log (n + 1))
      rw [← h] at h'
      apply Nat.log_ne_padicValNat_succ  _ h'
      exact Nat.ne_zero_of_lt hn

example (n : ℕ) (hn : 1 < n) : ¬ ∃ N : ℤ, H n = N := by
  rintro ⟨N, hN⟩
  have := padicValRat_H n (Nat.one_le_of_lt hn)
  simp [hN, padicValRat.of_int] at this
  rw [← not_le] at this
  exact this.2 hn

lemma Nat.max_log_padicValNat_succ_eq_log_succ' {p : ℕ} (n : ℕ) [hp : Fact (Nat.Prime p)] :
    max (log p n) (padicValNat p (n + 1)) = log p (n + 1) := by
  have hp' : 1 < p := hp.out.one_lt
  apply le_antisymm (max_le (le_log_of_pow_le hp.out.one_lt (pow_log_le_add_one p n))
    (padicValNat_le_nat_log (n + 1)))
  rw [le_max_iff, or_iff_not_imp_left, not_le]
  intro h
  replace h := le_antisymm (add_one_le_iff.mpr (lt_pow_of_log_lt hp.out.one_lt h))
    (pow_log_le_self p n.succ_ne_zero)
  rw [h, padicValNat.prime_pow, ← h]

/-! ## Exercise 39.
  Show that in any integral domain a prime element is irreducible. -/

#print IsDomain
#print IsCancelMulZero
#print Prime
#print Irreducible

example (R : Type*) [CommRing R] [IsDomain R] (a : R) (ha : Prime a) :
    Irreducible a where
  not_isUnit := ha.2.1
  isUnit_or_isUnit {x y} h := by
    rcases ha.2.2 x y (dvd_of_eq h) with hx | hy
    · obtain ⟨u, rfl⟩ := hx
      right
      apply isUnit_of_mul_eq_one_right u y
      rw [mul_assoc, eq_comm, mul_right_eq_self₀] at h
      exact Or.resolve_right h ha.1
      -- apply mul_left_cancel₀ ha.1
      --  apply IsLeftCancelMulZero.mul_left_cancel_of_ne_zero  ha.1
      -- rw [h, mul_one]
    · obtain ⟨v, rfl⟩ := hy
      left
      apply isUnit_of_mul_eq_one x v
      rw [mul_comm a, ← mul_assoc, eq_comm, mul_left_eq_self₀] at h
      exact Or.resolve_right h ha.1
      -- apply IsRightCancelMulZero.mul_right_cancel_of_ne_zero ha.1
      -- rw [mul_assoc, mul_comm v, ← h, one_mul]

example (R : Type*) [CommRing R] [IsDomain R] (a x y : R) (ha : a ≠ 0)
  (hx : a * x = a * y) : x = y := by
      apply IsLeftCancelMulZero.mul_left_cancel_of_ne_zero  ha hx

example (R : Type*) [CommRing R] [IsDomain R] (a : R) (ha : Prime a) :
    Irreducible a where
  not_isUnit := ha.2.1
  isUnit_or_isUnit {x y} h := by
    rcases ha.2.2 x y (dvd_of_eq h) with hx | hy
    · obtain ⟨u, rfl⟩ := hx
      right
      apply isUnit_of_mul_eq_one_right u y
      apply IsLeftCancelMulZero.mul_left_cancel_of_ne_zero  ha.1
      rw [← mul_assoc, ← h, mul_one]
    · obtain ⟨v, rfl⟩ := hy
      left
      apply isUnit_of_mul_eq_one x v
      apply IsRightCancelMulZero.mul_right_cancel_of_ne_zero ha.1
      rw [mul_assoc, mul_comm v, ← h, one_mul]

#print IsCancelMulZero
#print IsLeftCancelMulZero

#min_imports
