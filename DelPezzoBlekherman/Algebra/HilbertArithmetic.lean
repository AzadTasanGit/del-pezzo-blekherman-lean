/-
Copyright (c) 2026 Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring

/-!
# Hilbert-series arithmetic

This file records the polynomial arithmetic in Proposition 2.1.  The expressions
are doubled to avoid division by two: `n(n-1)` is twice the dimension of quadratic
forms on an `n`-dimensional space.
-/

namespace DelPezzoBlekherman

/-- The coefficient of `t` in `(1 + c t + t²)/(1-t)^(m+1)`. -/
def hilbertDegreeOne (m c : ℕ) : ℕ := m + 1 + c

/-- The coefficient of `t²` in `(1 + c t + t²)/(1-t)^(m+1)`. -/
def hilbertDegreeTwo (m c : ℕ) : ℕ :=
  (m + 2) * (m + 1) / 2 + c * (m + 1) + 1

/-- Twice the quadratic-dimension computation in Proposition 2.1. -/
theorem quadratic_deficiency_one_twice (m c : ℤ) :
    (m + c + 2) * (m + c + 1) -
        ((m + 2) * (m + 1) + 2 * c * (m + 1) + 2) =
      c * (c + 1) - 2 := by
  ring

/-- Evaluating the Hilbert numerator at one gives the asserted degree `c + 2`. -/
theorem hilbert_numerator_at_one (c : ℤ) : 1 + c + 1 = c + 2 := by
  ring

/-- The `a`-invariant arithmetic: numerator degree minus Krull dimension. -/
theorem gorenstein_a_invariant_arithmetic (m : ℤ) :
    2 - (m + 1) = 1 - m := by
  ring

end DelPezzoBlekherman
