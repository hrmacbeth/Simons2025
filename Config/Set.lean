/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Set.Basic

open Set

attribute [default_instance] Set.instSingletonSet
attribute [default_instance] Set.instEmptyCollection

variable {α : Type*}

/-! ### Some additions to the `dsimp` set

Restate some standard set `simp`-lemmas with `=` rather than `↔`, so that they are definitional. -/

@[simp] theorem Set.mem_insert_eq {x a : α} {s : Set α} : (x ∈ insert a s) = (x = a ∨ x ∈ s) := rfl
@[simp] theorem Set.mem_singleton_eq {x y : α} : (x ∈ ({y} : Set α)) = (x = y) := rfl

@[simp] theorem Set.mem_union_eq (x : α) (a b : Set α) : (x ∈ a ∪ b) = (x ∈ a ∨ x ∈ b) := rfl
@[simp] theorem Set.mem_inter_eq (x : α) (a b : Set α) : (x ∈ a ∩ b) = (x ∈ a ∧ x ∈ b) := rfl
@[simp] theorem Set.mem_compl_eq (s : Set α) (x : α) : (x ∈ sᶜ) = ¬x ∈ s := rfl

@[simp] theorem Set.mem_empty_eq_false (x : α) : (x ∈ ∅) = False := rfl
@[simp] theorem Set.mem_univ_eq (x : α) : (x ∈ univ) = True := rfl
