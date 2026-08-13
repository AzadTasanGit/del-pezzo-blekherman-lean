/-
Copyright (c) 2026 Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import Mathlib.Data.Fintype.Card

/-!
# Finite conjugate-pair counting

Elementary finite-set facts used in the last contradiction of Theorem 8.3.
-/

namespace DelPezzoBlekherman

/-- If every point of a finite type belongs to one chosen two-element orbit,
the type has cardinality at most two. -/
theorem card_le_two_of_single_conjugate_orbit
    {X : Type*} [Fintype X]
    (tau : X → X) (x : X)
    (horbit : ∀ y, y = x ∨ y = tau x) :
    Fintype.card X ≤ 2 := by
  classical
  have hsub : (Finset.univ : Finset X) ⊆ {x, tau x} := by
    intro y hy
    rcases horbit y with rfl | rfl
    · simp
    · simp
  calc
    Fintype.card X = (Finset.univ : Finset X).card := rfl
    _ ≤ ({x, tau x} : Finset X).card := Finset.card_le_card hsub
    _ ≤ ({tau x} : Finset X).card + 1 := Finset.card_insert_le _ _
    _ ≤ 2 := by simp

/-- With no real points, a conjugation-stable reduced set consists of pairs;
if it has at least three geometric points, it has at least two pairs. -/
theorem two_le_conjugatePairCount_of_three_le_total
    (pairCount : ℕ) (hcard : 3 ≤ 2 * pairCount) :
    2 ≤ pairCount := by
  omega

/-- Equivalently, a set made of at most one conjugate pair has total cardinality
strictly below three. -/
theorem total_lt_three_of_conjugatePairCount_le_one
    (pairCount : ℕ) (hpair : pairCount ≤ 1) :
    2 * pairCount < 3 := by
  omega

end DelPezzoBlekherman
