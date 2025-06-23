/-
Copyright (c) 2025 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Qq
import Mathlib.Lean.Expr.Basic

/-!
## Phase 4: Documentation

This is my final version of the tactic.  Document it.  (Or copy in your final version and document
that.)  Also add some more tests.
-/

theorem eq_or_le_succ_of_le {k l : Nat} (h : k ≤ l) : k = l ∨ k + 1 ≤ l :=
  Nat.eq_or_lt_of_le h

open Lean Meta Qq

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

def intervalCasesWrapper (x : Q(Nat)) (g : MVarId) : MetaM (List MVarId) := do
  let mut h_min : Option (FVarId × Nat) := none -- best lower bound we found so far, if any
  let mut h_max : Option (FVarId × Nat) := none -- best upper bound we found so far, if any
  for h in ← getLCtx do
    h_min := match ← h.toExpr.isLowerBoundOn? x, h_min with
      | some n1, some (_, n₀) => if n1 > n₀ then (h.fvarId, n1) else h_min
      | some n1, none => (h.fvarId, n1)
      | none, _ => h_min
    h_max := match ← h.toExpr.isUpperBoundOn? x, h_max with
      | some n2, some (_, n₀) => if n2 < n₀ then (h.fvarId, n2) else h_max
      | some n2, none => (h.fvarId, n2)
      | none, _ => h_max
  let some (f_max, n2) := h_max | throwError "No upper bound found for {x}"
  withErasedFVars #[f_max] do
  match h_min with
  | some (f_min, n1) => withErasedFVars #[f_min] do
    intervalCases n1 n2 x (.fvar f_min) (.fvar f_max) g
  | none =>
    let pf : Q(0 ≤ $x) := q(Nat.zero_le _)
    intervalCases 0 n2 x pf (.fvar f_max) g

elab "my_interval_cases " x:term : tactic => do
  let x : Expr ← Elab.Tactic.elabTerm x none
  Elab.Tactic.liftMetaTactic <| intervalCasesWrapper x

/-! ### Tests -/

/--
error: unsolved goals
⊢ 1 ∣ 12

⊢ 2 ∣ 12

⊢ 3 ∣ 12

⊢ 4 ∣ 12
-/
#guard_msgs in
example (k : Nat) (h1 : 1 ≤ k) (h2 : k ≤ 4) : k ∣ 12 := by
  my_interval_cases k
