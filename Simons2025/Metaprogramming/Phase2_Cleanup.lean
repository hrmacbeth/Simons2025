/-
Copyright (c) 2025 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Qq
import Mathlib.Lean.Expr.Basic

theorem eq_or_le_succ_of_le {k l : Nat} (h : k ≤ l) : k = l ∨ k + 1 ≤ l :=
  Nat.eq_or_lt_of_le h

open Lean Meta Qq

/-!
## Phase 2: Cleaning up the `interval_cases` tactic

The function below is my solution to the task from file 1: implementing the core logic of
`interval_cases`.

It produces goals that look like this:
```
k : Nat
h1 : 1 ≤ k
h2 : k ≤ 4
⊢ 2 = k → k ∣ 12
```

### Task (i): clean up `intervalCases`

*** Exercise *** Let's clean this up in two ways:
* rathing than having an implication goal with antecedent `2 = k`, just change all the `k`s to `2`s
* get rid of the two hypotheses `h1` and `h2`, which have been "used up"

Here are the `MetaM` operations I expect you to use.
-/

#check subst -- run `subst` on a specified goal, `MVarId → FVarId → MetaM MVarId`

-- run `clear` on all goals created by a tactic, `{α : Type} → Array FVarId → MetaM α → MetaM α`
#check withErasedFVars

partial def intervalCases (n1 n2 : Nat) (x : Q(Nat)) (h_min : Q($n1 ≤ $x)) (h_max : Q($x ≤ $n2))
    (g : MVarId) :
    MetaM (List MVarId) := do
  let t : Q(Prop) ← g.getType
  if n1 > n2  then
    let h_contra : Q(¬ ($n1 ≤ $n2)) ← mkDecideProof q(¬ ($n1 ≤ $n2))
    let pf : Q($t) := q(absurd (Nat.le_trans $h_min $h_max) $h_contra)
    g.assign pf
    return []
  else
    let n1' : Nat := n1 + 1
    let split : Q($n1 = $x ∨ $n1' ≤ $x) := q(eq_or_le_succ_of_le $h_min)
    let e1 : Q($n1 = $x → $t) ← mkFreshExprMVar q($n1 = $x → $t)
    let e2 : Q($n1' ≤ $x → $t) ← mkFreshExprMVar q($n1' ≤ $x → $t)
    let (f_min', g2) ← e2.mvarId!.intro1
    let G2 ← intervalCases n1' n2 x (.fvar f_min') h_max g2
    let pf : Q($t) := q(Or.elim $split $e1 $e2)
    g.assign pf
    return (e1.mvarId! :: G2)

/-! ### Task (ii): streamline the user syntax for `my_interval_cases`

It would also be a better user experience for the user not to have to specify the natural number
bounds.  We want the tactic to infer from the form of the hypotheses `(h1 : 1 ≤ k) (h2 : k ≤ 4)`
that the `n1` should be 1 and the `n2` should be 4.

Fortunately there are a number of pre-written library functions for parsing expressions.
-/
#check Expr.le? -- `Expr → Option (Expr × Expr × Expr)`
#check Expr.nat? -- `Expr → Option Nat`

def Lean.Expr.isLowerBoundOn? (x : Q(Nat)) (h : Expr) : MetaM (Option Nat) := do
  let e ← inferType h
  let some (α, a, b) := e.le? | return none
  -- *** Exercise *** more parsing here, then replace the hard-coded `1`
  return some 1

def Lean.Expr.isUpperBoundOn? (x : Q(Nat)) (h : Expr) : MetaM (Option Nat) := do
  -- *** Exercise *** more parsing here, then replace the hard-coded `4`
  return some 4

/-
Fill in the rest of the necessary parsing above.  For bonus points, guard against user error:
The tactic implicitly assumes that `h1` and `h2` are inequalities between `Nat`s, and that `x` is
the `RHS` of `h1` and the `LHS` of `h2`.  It would be good to make the tactic throw an error if
these conditions don't hold.
-/

/-
### The rest of the file (you shouldn't need to change anything here)

The rest of the file implements the user-facing end of the tactic and runs a test of the tactic.
-/

def intervalCasesWrapper (x : Q(Nat)) (h_min h_max : Expr) (g : MVarId) :
    MetaM (List MVarId) := do
  let some n1 ← h_min.isLowerBoundOn? x |
    throwError "The hypothesis {h_min} seems to have the wrong form"
  let some n2 ← h_max.isUpperBoundOn? x |
    throwError "The hypothesis {h_max} seems to have the wrong form"
  intervalCases n1 n2 x h_min h_max g

elab "my_interval_cases " x:term " with" h1:(ppSpace colGt ident) h2:(ppSpace colGt ident) :
    tactic => do
  let x : Expr ← Elab.Tactic.elabTerm x none
  let h1 : Expr ← Elab.Tactic.elabTerm h1 none
  let h2 : Expr ← Elab.Tactic.elabTerm h2 none
  Elab.Tactic.liftMetaTactic <| intervalCasesWrapper x h1 h2

set_option trace.debug true

example (k : Nat) (h1 : 1 ≤ k) (h2 : k ≤ 4) : k ∣ 12 := show_term by
  my_interval_cases k with h1 h2 <;>
  sorry
