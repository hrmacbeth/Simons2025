import Mathlib

theorem ZMod.coe_int_isUnit_iff_isCoprime (n : ℤ) (m : ℕ) :
    IsUnit (n : ZMod m) ↔ IsCoprime (m : ℤ) n := by
  rw [Int.isCoprime_iff_nat_coprime, Nat.coprime_comm, ← ZMod.isUnit_iff_coprime, Associated.isUnit_iff]
  simpa only [eq_intCast, @Int.cast_natCast] using
    Associated.map (Int.castRingHom _) (Int.associated_natAbs _)

theorem Int.isCoprime_of_dvd (m n : ℤ)
    (H : ∀ (p : ℕ), Nat.Prime p → (p : ℤ) ∣ m → ¬ (p : ℤ) ∣ n) :
    IsCoprime m n := by
  rw [Int.isCoprime_iff_nat_coprime]
  apply Nat.coprime_of_dvd
  simpa [← Int.ofNat_dvd_left] using H

theorem Nat.log_lt_log_succ_iff {p : ℕ} [hp : Fact (p.Prime)] {n : ℕ} (hn : 1 ≤ n) :
    Nat.log p n < Nat.log p (n + 1) ↔ n + 1 = p ^ (Nat.log p (n + 1)) := by
  refine ⟨fun H ↦ ?_, fun H ↦ ?_⟩
  · apply le_antisymm (Nat.lt_pow_of_log_lt hp.out.one_lt H)
    exact Nat.pow_log_le_self p (Ne.symm (Nat.zero_ne_add_one n))
  · apply Nat.log_lt_of_lt_pow (Nat.ne_zero_of_lt hn)
    simp [← H]

theorem Nat.log_eq_log_succ_iff {p : ℕ} [hp : Fact (p.Prime)] {n : ℕ} (hn : 1 ≤ n) :
    log p n = log p (n + 1) ↔ n + 1 ≠ p ^ (log p (n + 1)) := by
  rw [ne_eq, ← log_lt_log_succ_iff hn, not_lt]
  simp only [le_antisymm_iff, and_iff_right_iff_imp]
  exact fun  _ ↦ log_monotone (le_add_right n 1)

theorem Nat.clog_lt_clog_succ_iff {p : ℕ} [hp : Fact (p.Prime)] {n : ℕ} (hn : 1 ≤ n) :
    clog p n < clog p (n + 1) ↔ n  = p ^ (clog p n) := by
  refine ⟨fun H ↦ ?_, fun H ↦ ?_⟩
  · apply le_antisymm (le_pow_clog hp.out.one_lt n)
    apply le_of_lt_succ
    exact (pow_lt_iff_lt_clog hp.out.one_lt).mpr H
  · rw [← pow_lt_iff_lt_clog hp.out.one_lt, ← H]
    exact lt_add_one n

theorem Nat.clog_eq_clog_succ_iff {p : ℕ} [hp : Fact (p.Prime)] {n : ℕ} (hn : 1 ≤ n) :
    clog p n = clog p (n + 1) ↔ n ≠ p ^ (clog p n) := by
  rw [ne_eq, ← clog_lt_clog_succ_iff hn, not_lt]
  simp only [le_antisymm_iff, and_iff_right_iff_imp]
  exact fun _ ↦ clog_monotone p (le_add_right n 1)



