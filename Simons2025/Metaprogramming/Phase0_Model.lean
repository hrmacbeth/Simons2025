/-
Copyright (c) 2025 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Tactic.IntervalCases

/-!
## Phase 0: What should the `interval_cases` tactic do?

The first step in writing a tactic is to write by hand some examples of what the tactic should do.

Here is a typical use case for the `interval_cases` tactic.
-/

example (k : Nat) (h1 : 1 ≤ k) (h2 : k ≤ 4) : k ∣ 12 := by
  interval_cases k <;>
  sorry

/-
Exercise: Write code which does the same thing without using the `interval_cases` tactic.
-/

example (k : Nat) (h1 : 1 ≤ k) (h2 : k ≤ 4) : k ∣ 12 := by
  sorry
