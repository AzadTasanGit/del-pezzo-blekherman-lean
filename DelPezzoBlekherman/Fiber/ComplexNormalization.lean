/-
Copyright (c) 2026 Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Normalization of the one-conjugate-pair coefficient

This file checks the final normalization calculation in Theorem 7.4: after making
the complex relation coefficient equal to one, the complex reciprocal term is
`2α / (α² + β²)`, and the reciprocal identity forces `α < 0`.
-/

namespace DelPezzoBlekherman

/-- The real part of the inverse of `α + iβ`, in the normalization used by
Theorem 7.4. -/
theorem two_re_inv_mk (α β : ℝ) :
    2 * ((Complex.mk α β)⁻¹).re = 2 * α / (α ^ 2 + β ^ 2) := by
  simp only [Complex.inv_re, Complex.normSq_apply]
  ring

/-- If the real reciprocal contribution is positive and the normalized identity
holds, then the real part `α` of the complex coefficient is negative. -/
theorem normalized_complex_coefficient_real_part_negative
    {S α β : ℝ} (hS : 0 < S) (hb : α ^ 2 + β ^ 2 ≠ 0)
    (hid : S + 2 * α / (α ^ 2 + β ^ 2) = 0) :
    α < 0 := by
  have hden : 0 < α ^ 2 + β ^ 2 := by
    positivity
  have hquot : 2 * α / (α ^ 2 + β ^ 2) < 0 := by
    linarith
  rcases (div_neg_iff.mp hquot) with h | h
  · exact (not_lt_of_ge hden.le h.2).elim
  · nlinarith [h.1]

end DelPezzoBlekherman
