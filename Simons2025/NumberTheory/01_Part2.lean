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
    sorry
  · intro ⟨k, eq⟩
    sorry

/-! ## Exercise 7.
  Let d = (a, b) and a = da' and b = db'. Show that (a', b') = 1. -/

example : ∃ (a b : ℤ), Int.gcd (a / a.gcd b) (b / a.gcd b) ≠ 1 := by
  -- don't hesitate to check that the tactic `simp` is sometimes powerful enough
  sorry

example (a b : ℤ) (H : a ≠ 0 ∨ b ≠ 0) :
    Int.gcd (a / a.gcd b) (b / a.gcd b) = 1 := by
  have H' : a.gcd b ≠ 0 := by
    sorry
  set a' := a / a.gcd b
  have ha : a = a' * a.gcd b := by
    sorry
  set b' := b / a.gcd b
  have hb : b = b' * a.gcd b := by
    sorry
  sorry

/-! ## Exercise 8.
  Let Xo and Yo be a solution to ax + by= c.
  Show that all solutions have the form
    x = Xo + t(b/d), Y= Yo - t(a/d), where d = (a, b) and t ∈ ℤ. -/

-- This one was a bit tough for me…

example (a b c d : ℤ) (d_def : d = a.gcd b) (hd₀ : d ≠ 0)
    (x₀ y₀ : ℤ) (eq₀ : a * x₀ + b * y₀ = c) (x y : ℤ) :
    a * x + b * y = c ↔
      ∃ t, x = x₀ + t * (b / d) ∧ y = y₀ - t * (a / d) := by
  sorry

/-! ## Exercise 9.
  Suppose that u, v ∈ ℤ and that (u, v)= 1.
  If u ∣ n and v ∣ n,show that uv ∣ n.
  Show that this is false if (u, v) ≠ 1. -/

example (u v n : ℤ) (huv : u.gcd v = 1) (hu : u ∣ n) (hv : v ∣ n) :
    u * v ∣ n := by
  sorry

example : ∃ (u v n : ℤ) (hu : u ∣ n) (hv : v ∣ n), ¬ (u * v ∣ n) := by
  sorry

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
  sorry

/-! ## Exercise 11
  Show that (a, a + k) ∣ k. -/

-- Here, we learn a new tactic `suffices`:
-- It allows to accept something temporarily, and to prove it afterwards

example (a k : ℤ) : (a.gcd (a + k) : ℤ) ∣ k := by
  suffices a.gcd (a + k) = a.gcd k by
    -- conclude the proof assuming `this : a.gcd (a + k) = a.gcd k`
    sorry
  -- Actually, Mathlib knows about this
  -- You can guess the name or try `apply?`
  exact Int.gcd_self_add_right a k

