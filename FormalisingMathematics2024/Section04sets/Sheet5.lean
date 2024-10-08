/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- import all the tactics

/-!

# Sets in Lean, sheet 5 : equality of sets

Sets are extensional objects to mathematicians, which means that
if two sets have the same elements, then they are equal.

## Tactics

Tactics you will need to know for this sheet:

* `ext`

### The `ext` tactic

If the goal is `⊢ A = B` where `A` and `B` are subsets of `X`, then
the tactic `ext x,` will create a hypothesis `x : X` and change
the goal to `x ∈ A ↔ x ∈ B`.

-/

open Set

variable (X : Type)
  -- Everything will be a subset of `X`
  (A B C D E : Set X)
  -- A,B,C,D,E are subsets of `X`
  (x y z : X)

-- x,y,z are elements of `X` or, more precisely, terms of type `X`
example : A ∪ A = A := by
  ext a
  constructor
  · rintro (hA | hA) <;> exact hA
  · intro hA
    left
    exact hA

example : A ∩ A = A := by
  ext a
  constructor
  · intro hA
    cases' hA with h _
    exact h
  · intro hA
    constructor <;> exact hA

example : A ∩ ∅ = ∅ := by
  ext a
  constructor
  · intro ⟨_, hB⟩
    exact hB
  · intro hB
    exfalso
    exact hB

example : A ∪ univ = univ := by
  ext a
  constructor
  · rintro (ha | h)
    · triv
    · exact h
  · intro h
    right
    triv

example : A ⊆ B → B ⊆ A → A = B := by
  intro hA hB
  ext a
  constructor <;> intro h
  · exact hA h
  · exact hB h

example : A ∩ B = B ∩ A := by 
  exact inter_comm A B

example : A ∩ (B ∩ C) = A ∩ B ∩ C := by sorry

example : A ∪ (B ∪ C) = A ∪ B ∪ C := by sorry

example : A ∪ B ∩ C = (A ∪ B) ∩ (A ∪ C) := by sorry

example : A ∩ (B ∪ C) = A ∩ B ∪ A ∩ C := by sorry
