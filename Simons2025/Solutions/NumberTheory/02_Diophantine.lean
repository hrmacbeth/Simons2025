/- Solving diophantine equations in Lean
   NYC 2025 Workshop on Lean
   (c) Antoine Chambert-Loir, 2025 -/

import Mathlib

/-! # Diophantine Equations

  This sheet contains the study four diophantine equations.  -/

/-!

  ## A diophantine equation from geometry

  This exercise is taken from the first chapter of the book by Ireland and Rosen.

  **Problem 12.**
  Suppose that we take several copies of a regular polygon and try
  to fit them evenly about a common vertex.  Prove that the only
  possibilities are six equilateral triangles, four squares, and
  three hexagons. -/

/- The sum of the inner angles of a polygon with n vertices is (n-2)π,
  so that the inner angle is (1-2/n)π.
  The condition that m polygons fit evenly is m (1-2/n)π = 2π, hence m(n-2)=2n :
  we get the diophantine equation m * n = 2 * (m + n). -/

/- ### A solution due to Heather Macbeth -/
example (m n : ℕ) (H : m * n = 2 * (m + n)) :
    (m = 6 ∧ n = 3) ∨ (m = 4 ∧ n = 4) ∨ (m = 3 ∧ n = 6) ∨ (m = 0 ∧ n = 0) := by
  match m, n with
  -- if `m` or `n` is `0` or `1` we get a contradiction trivially,
  -- or else `(m, n) = (0, 0)` which is allowed
  | 0, n | 1, n | m, 0 | m, 1 => omega
  -- the nontrivial case is when both variables are of the form _ + 2
  | u + 2, v + 2 =>
    -- in this case `u ≤ 4`, i.e. `2 ≤ m ≤ 6`
    have H : 4 = u * v := by linarith
    have : u ∣ 4 := ⟨v, H⟩
    have : u ≤ 4 := by
      refine Nat.le_of_dvd ?_ this
      norm_num
    -- so, case bash
    interval_cases u <;> omega

/- ### Let's solve the same equation in integers -/
example (m n : ℤ) (H : m * n = 2 * (m + n)) :
    (m = -2 ∧ n = 1) ∨ (m = 0 ∧ n = 0) ∨ (m = 1 ∧ n = -2) ∨
      (m = 3 ∧ n = 6) ∨ (m = 4 ∧ n = 4) ∨ (m = 6 ∧ n = 3) := by
  -- we start in a similar way
  have h : (m - 2) * (n - 2) = 4 := by linarith
    /- other options :
       * compute
       * use the `ring` tactic, after some rewriting
       * use the `linear_combination` tactic with `-H`
       * but `omega` doesn't work -/
  -- now, `u` is of the form ± 2 ^ i, for some i ≤ 2
  obtain ⟨i, hi, hu⟩ := (dvd_prime_pow Int.prime_two (q := m - 2) 2).mp ⟨n-2, h.symm⟩
  simp [Int.associated_iff] at hu
  -- There are three cases for `i`, which the tactic `interval_cases` can build
  -- and two cases for the sign, which we split using `rcases`
  interval_cases i <;>
  · rcases hu with hu | hu <;>
     simp only [hu] at h <;> omega

/-! Variants : could you solve the equation
      x y = a (x + y)
    in integers, where a is an integer (either a specific one or an arbitrary number) ? -/

/-! ## A diophantine equation due to Fermat

    Prove that the diophantine equation
      x ^ 3 + 2 y ^ 3 = 4 z ^ 3
    only has (0, 0, 0) for solution. -/

lemma even_pow_three_iff {a : ℕ} : Even (a ^3) ↔ Even a := by
  refine Nat.even_pow' (by norm_num)

theorem fermat {x y z : ℕ} (H : x ^ 3 + 2 * y ^ 3 = 4 * z ^ 3) :
    x = 0 ∧ y = 0 ∧ z = 0 := by
  have hx : Even x := by
    rw [← even_pow_three_iff]
    -- look at `Nat.even_add`
    -- sorry --
    have := Nat.even_add (m := x ^3) (n := 2 * y ^ 3)
    erw [H, mul_assoc 2 2 (z ^3)] at this
    simpa using this
    -- sorry --
  obtain ⟨u, hu⟩ := hx
  have H' : 4 * u ^3 + y ^ 3 = 2 * z ^ 3 := by
    -- sorry --
    rw [hu] at H; linarith
    -- sorry --
  have hy : Even y := by
    -- sorry --
    rw [← even_pow_three_iff]
    have := Nat.even_add (m := 4 * u ^ 3) (n := y ^ 3)
    erw [H', mul_assoc 2 2 _] at this
    simpa using this
    -- sorry --
  obtain ⟨v, hv⟩ := hy
  have H'' : 2 * u ^ 3 + 4 * v ^ 3 = z ^3 := by
    -- sorry --
    rw [hv] at H'; linarith
    -- sorry --
  have hz : Even z := by
    -- sorry --
    rw [← even_pow_three_iff, ← H'']
    erw [mul_assoc 2 2, ← mul_add]
    apply even_two_mul
    -- sorry --
  obtain ⟨w, hw⟩ := hz
  have K : u ^3 + 2 * v ^3 = 4 * w ^3 := by
    -- sorry --
    rw [hw] at H''; linarith
    -- sorry --
  -- At this point, we have constructed a new solution (u, v, w)
  -- which is half the initial one (x, y, z)
  -- we consider whether the sum x + y + z vanishes or not
  rcases Nat.eq_zero_or_pos (x + y + z) with h | h
  · -- when x + y + z = 0, one must have x = y = z = 0
    -- sorry --
    simp only [Nat.add_eq_zero] at h
    exact ⟨h.1.1, h.1.2, h.2⟩
    -- sorry --
  · -- otherwise, let's apply the theorem to (u, v, w) :
    have := fermat K
    -- sorry --
    simp [hu, hv, hw, this.1, this.2.1, this.2.2]
    -- sorry --

/-! Another diophantine equation from a Putnam competition :

    Prove that the solutions in natural numbers of the equation
       2 ^ m = 1 + m * n
    are just m = 0 (and any n) or m = 1 and n = 1.

    -/

-- theorem minFac_le_of_dvd (m n p : ℕ) (hp : p.Prime)

theorem putnam (m n : ℕ) :
    2 ^ m  = 1 + m * n ↔ m = 0 ∨ (m = 1 ∧ n = 1) := by
  -- we split the `iff` as the two implications and swap the
  -- order in which we prove them
  constructor ; swap
  · -- the given integers define solutions
    -- sorry --
    rintro (⟨rfl⟩ | ⟨rfl, rfl⟩) <;> simp
    -- sorry --
  · -- now for the resolution of the equation
    intro H
    match m with
    | 0 => -- when m = 0
      -- sorry --
      simp
      -- sorry --
    | 1 => -- when m = 1
      -- sorry --
      simp; simp at H; linarith
      -- sorry --
    | m + 2 => -- no integer m at least 2 gives a solution,
      -- so we argue by *ex falso*:
      exfalso
      -- for ease of reading, we write `M` for `m + 2`
      set M := m + 2 with hM
      -- `Nat.minFac` returns the smallest prime divisor
      -- … or `0` when there is none.
      let p := Nat.minFac M
      have hp : Fact (p.Prime) := ⟨Nat.minFac_prime (by linarith)⟩
      have pdvd : p ∣ m + 2 := Nat.minFac_dvd M
      -- `orderOf` returns the order of an element in a monoid
      -- … or `0` when the element is not of finite order
      let r := orderOf (2 : ZMod p)
      have hr_dvd_M : r ∣ M := by
        rw [orderOf_dvd_iff_pow_eq_one]
        -- sorry --
        rw [← Nat.cast_two, ← Nat.cast_pow, H]
        simp only [Nat.cast_add, Nat.cast_one, add_eq_left]
        simp only [Nat.cast_mul]
        convert zero_mul _
        rw [ZMod.natCast_zmod_eq_zero_iff_dvd]
        exact Nat.minFac_dvd M
        -- sorry --
      have hr : r ∣ p - 1 := by
        apply ZMod.orderOf_dvd_card_sub_one
        -- sorry --
        rw [← Nat.cast_two, ne_eq, ZMod.natCast_zmod_eq_zero_iff_dvd,
          Nat.prime_two.dvd_iff_eq hp.out.ne_one, eq_comm]
        have : Even (2 ^ M) := by
          rw [even_iff_two_dvd]
          exact ⟨2 ^ (m + 1),  Nat.pow_succ'⟩
        simp [H, Nat.even_add', Nat.odd_mul] at this
        rw [← Nat.not_even_iff_odd] at this
        intro h2
        apply this.1
        rwa [h2, ← even_iff_two_dvd] at pdvd
        -- sorry --
      -- r is nonzero
      have hr_ne_zero : r ≠ 0 := fun hr0 ↦ by
        simp [hM, hr0] at hr_dvd_M
      -- r is not equal to 1
      have hr_ne_one : r ≠ 1 := by
        -- sorry --
        rw [ne_eq, orderOf_eq_one_iff, ← sub_eq_zero]
        ring_nf
        exact one_ne_zero
        -- sorry --
      have hr_lt_p : r < p := by
        apply lt_of_le_of_lt (b := p - 1)
        · apply Nat.le_of_dvd
          refine Nat.sub_pos_of_lt hp.out.two_le
          exact hr
        · apply Nat.sub_one_lt
          exact hp.out.ne_zero
      rw [← not_le] at hr_lt_p
      apply hr_lt_p
      -- Now for the contradiction, using that `p` is the
      -- smallest prime factor of `M`.
      apply (Nat.le_minFac' (n := M) (m := p)).mp ?_ _ _ hr_dvd_M
      · simp [p]
      · rw [Nat.two_le_iff]
        exact ⟨hr_ne_zero, hr_ne_one⟩
