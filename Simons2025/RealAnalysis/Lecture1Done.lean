import Mathlib

#eval 2+2

def seqLimIs (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - L| < ε

-- Definition of a sequence being convergent (has some limit)
def seqConv (a : ℕ → ℝ) : Prop :=
  ∃ L : ℝ, seqLimIs a L

example (s : ℕ → ℝ) :
  seqConv s → seqConv (fun n ↦ |s n|) := by
  intro P --⟨bob, Ida⟩
  unfold seqConv at P
  obtain ⟨bob, Ida⟩ := P
  unfold seqConv
  let L := |bob|
  use L
  unfold seqLimIs at *
  set t : ℕ → ℝ := fun n ↦ |s n|
  intro ε eps_pos
  have := Ida ε eps_pos
  obtain ⟨N, hN⟩ := this
  use N
  intro n
  intro n_ge_N
  have h1 : |s n - bob| < ε := hN n n_ge_N
  have h2 : |t n - L| ≤ |s n - bob| :=
    abs_abs_sub_abs_le_abs_sub _ _ -- reverse triangle inequality
  --linarith [h1, h2]
  calc |t n - L|
          ≤ |s n - bob| := by exact h2
        _ < ε := h1





#exit
  -- Setup: assume s_n converges to some limit L
  -- We want to show |s_n| converges to |L|
  -- Now prove seq_limit (fun n ↦ |s n|) |L|
  intro ε hε
  -- Since s_n → L, get N for this ε
  obtain ⟨N, hN⟩ := hL ε hε
  -- Use the same N for |s_n| → |L|
  use N
  intro n hn
  -- For n ≥ N, we have |s_n - L| < ε
  have h1 : |s n - L| < ε := hN n hn
  -- Apply reverse triangle inequality: ||s_n| - |L|| ≤ |s_n - L|
  have h2 : |(|s n|) - (|L|)| ≤ |s n - L| := sorry -- reverse triangle inequality
  -- Combine to get ||s_n| - |L|| < ε
  linarith [h1, h2]
