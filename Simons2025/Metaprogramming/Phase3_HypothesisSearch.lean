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
## Phase 3: Finding the right hypotheses automatically

The functions below are my solution to the task from file 2: cleaning up the core logic of
`interval_cases` and parsing a hypothesis as a potential lower or upper `Nat`-bound for an
expression.
-/

partial def intervalCases (n1 n2 : Nat) (x : Q(Nat)) (h_min : Q($n1 ≤ $x)) (h_max : Q($x ≤ $n2))
    (g : MVarId) :
    MetaM (List MVarId) := withErasedFVars #[h_min.fvarId!, h_max.fvarId!] do
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
    let (f, g1) ← e1.mvarId!.intro1
    let G1 ← subst g1 f
    let e2 : Q($n1' ≤ $x → $t) ← mkFreshExprMVar q($n1' ≤ $x → $t)
    let (f_min', g2) ← e2.mvarId!.intro1
    let G2 ← intervalCases n1' n2 x (.fvar f_min') h_max g2
    let pf : Q($t) := q(Or.elim $split $e1 $e2)
    g.assign pf
    return (G1 :: G2)

def Lean.Expr.isLowerBoundOn? (x : Q(Nat)) (h : Expr) : MetaM (Option Nat) := do
  let e ← inferType h
  let some (α, a, b) := e.le? | return none
  unless α == q(Nat) do return none
  unless ← isDefEq b x do return none
  return a.nat?

def Lean.Expr.isUpperBoundOn? (x : Q(Nat)) (h : Expr) : MetaM (Option Nat) := do
  let e ← inferType h
  let some (α, a, b) := e.le? | return none
  unless α == q(Nat) do return none
  unless ← isDefEq a x do return none
  return b.nat?

/-
### Iterating over the hypotheses (your work goes here)

Now we want to make the tactic even more user-friendly: rather than making the user specify
hypotheses which give upper and lower bounds for the variable, the tactic will search for such
hypotheses.

The local context provides a list of the available hypotheses.
They are in the form of `LocalDecl`s (think of these as "`FVarId`s with decoration").
-/
#check getLCtx -- `MetaM LocalContext`
#check LocalDecl.fvarId -- `LocalDecl → FVarId`
#check LocalDecl.toExpr -- `LocalDecl → Expr`

/-
Typically you loop over the local context using a for-loop, using some mutable variables to track
what you find.  Here's the structure of such a loop in our use case.  Fill it in.
-/

def intervalCasesWrapper (x : Q(Nat)) (g : MVarId) : MetaM (List MVarId) := do
  let mut h_min : Option (FVarId × Nat) := none -- best lower bound we found so far, if any
  let mut h_max : Option (FVarId × Nat) := none -- best upper bound we found so far, if any
  let mut i := 0
  for h in ← getLCtx do
    -- *** Exercise *** see if `h` parses as a lower bound on `x`, if so update `h_min`
    if i == 2 then h_min := (h.fvarId, 1) -- hack: in our test we know this comes as hypothesis 2
    -- *** Exercise *** see if `h` parses as an upper bound on `x`, if so update `h_max`
    if i == 3 then h_max := (h.fvarId, 4) -- hack: in our test we know this comes as hypothesis 3
    i := i + 1
  let some (f_min, n1) := h_min | throwError "No lower bound found for {x}"
  -- *** Exercise *** we can be cleverer: if no lower bound is found for `x`, use `0`
  let some (f_max, n2) := h_max | throwError "No upper bound found for {x}"
  intervalCases n1 n2 x (.fvar f_min) (.fvar f_max) g

/-
### The rest of the file (you shouldn't need to change anything here)

The rest of the file implements the user-facing end of the tactic and runs a test of the tactic.
-/

elab "my_interval_cases " x:term : tactic => do
  let x : Expr ← Elab.Tactic.elabTerm x none
  Elab.Tactic.liftMetaTactic <| intervalCasesWrapper x

set_option trace.debug true

example (k : Nat) (h1 : 1 ≤ k) (h2 : k ≤ 4) : k ∣ 12 := show_term by
  my_interval_cases k <;>
  sorry
