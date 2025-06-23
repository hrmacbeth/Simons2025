/-
Copyright (c) 2025 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Qq

open Lean Meta Qq

/-!
## Phase 1: Core logic of the `interval_cases` tactic

This file currently implements the syntax which will be used for the first version of the
`interval_cases` tactic.  The typical syntax will be
```
my_interval_cases k with h1 h2 between 1 4
```
where we will assume that
* `h1` is a hypothesis of type `1 ≤ k`
* `h2` is a hypothesis of type `k ≤ 4`

Look at the end of the file to see this syntax being parsed and tested.

The core logic is going to be performed in the function `intervalCases`.  The arguments to this
function are
* natural numbers called `n1` and `n2`;
* expressions (`Expr`) called `x`, `h_min` and `h_max`, where
  `x` is assumed to represent a natural number,
  `h_min` is assumed to represent a proof of the statement `n1 ≤ x`, and
  `h_max` is assumed to represent a proof of the statement `x ≤ n2`;
* a metavariable (`MVarId`) called `g`

and the output (in the monad `MetaM`) to this function is a list of metavariables (the subgoals
produced by the tactic).
-/
#check Expr
#check MVarId
#check MetaM

/-! ### The core `intervalCases` function (your work goes here) -/

/-
Currently the tactic just closes the goal with "sorry", producing no subgoals.
-/
#check MVarId.getType -- MVarId → MetaM Expr
#check MVarId.assign -- MVarId → Expr → MetaM Unit

partial def intervalCases (n1 n2 : Nat) (x : Q(Nat)) (h_min : Q($n1 ≤ $x)) (h_max : Q($x ≤ $n2))
    (g : MVarId) :
    MetaM (List MVarId) := do
  /-
  *** Exercise *** replace the placeholder code below!
  -/
  let t : Q(Prop) ← g.getType
  trace[debug] "our goal is {t}"
  let pf : Q($t) := q(sorry)
  g.assign pf
  return []

/-
The task in this file is to fill in (without sorries) the body of the above `intervalCases`
function.  If, as above, the input goal `g` has type `⊢ t`, then we want to write logic which
reduces `t` to new subgoals of the form `⊢ n1 = x → t`, `⊢ n1 + 1 = x → t`, ... `⊢ n2 = x → t`.

The following operations in `MetaM` will be useful:
-/
#check mkFreshExprMVarQ -- make a new goal of specified type, `∀ t : Q(Sort _), MetaM Q($t)`
#check MVarId.intro1 -- run `intro` on a specified goal, `MVarId → MetaM (FVarId × MVarId)`
#check mkDecideProof -- run `decide` to prove a specified statement, `Expr → MetaM Expr`

/-
Also: `MVarId`s (metavariables) and `FVarId`s (free variables) are particular kinds of expressions
(representing, respectively, goals and hypotheses/variables).  Here are convenience functions for
going back and forth.
-/
#check Expr.mvarId! -- `Expr → MVarId`
#check Expr.fvar -- `FVarId → Expr`

/-
### The rest of the file (you shouldn't need to change anything here)

The rest of the file implements the user-facing end of the tactic and runs a test of the tactic.
-/

/-- Interpret the syntax `my_interval_cases k with h1 h2 between n1 n2`, and run the `intervalCases`
function on what gets parsed. -/
elab "my_interval_cases " x:term " with" h1:(ppSpace colGt ident) h2:(ppSpace colGt ident)
    " between" n1:(ppSpace colGt num) n2:(ppSpace colGt num) :
    tactic => do
  let x : Expr ← Elab.Tactic.elabTerm x none
  let h1 : Expr ← Elab.Tactic.elabTerm h1 none
  let h2 : Expr ← Elab.Tactic.elabTerm h2 none
  let n1 : Nat := TSyntax.getNat n1
  let n2 : Nat := TSyntax.getNat n2
  Elab.Tactic.liftMetaTactic <| intervalCases n1 n2 x h1 h2

set_option trace.debug true

/-! Here's a test for the tactic.

I have turned on a few diagnostics here.
* `show_term` shows us the (partial) proof term our tactic produced (initially, just `sorry`)
* `set_option trace.debug true` turns on the display of the "debug" trace channel. We can post
  messages to this channel within the tactic logic using the syntax `trace[debug] "blah blah"`.
-/
example (k : Nat) (h1 : 1 ≤ k) (h2 : k ≤ 4) : k ∣ 12 := show_term by
  my_interval_cases k with h1 h2 between 1 4
