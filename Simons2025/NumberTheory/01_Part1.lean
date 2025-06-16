/- A formalization of the exercises in the book by Ireland & Rosen,
   *A classical introduction to number theory*
   Antoine Chambert-Loir, 2025 -/

import Mathlib

/-! # Chapter 1. Unique factorization -/

/-! ## Exercise 1.
Let a and b be nonzero integers.
We can find nonzero integers q and r such that a = qb + r,
where 0 ≤ r < b. Prove that (a, b)= (b, r). -/

example (a b : ℕ) (hb_ne_zero : b ≠ 0) :
    ∃ (q r : ℕ), a = q * b + r ∧ r < b ∧ a.gcd b = b.gcd r := by
  set q := a / b
  set r := a % b
  have eq : a = q * b + r := by
    sorry
  use q, r, eq
  constructor
  · -- The remainder is less than b
    sorry
  · -- Equality of gcd's
    sorry

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

/- Comment : This exercise requires to define a function
by induction, which is out of scope, and maybe too advanced for the moment.
We just check that Mathlib knows about gcd's of natural numbers and of integers. -/

-- This informs about gcd of natural numbers
#check Nat.gcd

-- How would know about gcd of integers ?


/-! ## Exercise 3.
  Calculate (187, 221), (6188, 4709), and (314.159). -/

-- Use #eval to compute these gcd's



/-! ## Exercise 4.
  Let d= (a. b).
  Show how one can use the Euclidean algorithm to find numbers
  m and n such that am + bn = d. -/

/- This follows from undone exercise 2, but Mathlib has these functions
Read the output and convince yourself that they do what we want. -/

#check Int.gcd
#check Int.gcdA
#check Int.gcdB
#check Int.gcd_eq_gcd_ab

/-! ## Exercise 5
  Calculate m and n for the examples of exercise 3 -/




