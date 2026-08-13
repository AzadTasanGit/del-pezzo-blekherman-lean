/-
Copyright (c) 2026 Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Signature

/-!
# Hyperplane inertia

This file formalizes Lemma 6.1 of the source paper. Mathlib's `QuadraticForm.sigNeg`
is the negative index of inertia, defined as the largest dimension of a subspace on
which the negative of the form is positive definite.
-/

open Finset QuadraticMap

namespace DelPezzoBlekherman

/-- **Lemma 6.1 (Hyperplane inertia bound).** If the restriction of a real quadratic
form to a hyperplane is positive semidefinite, its negative index is at most one.

The codimension-one hypothesis is written as the corresponding finrank identity;
this avoids choosing an equation for the hyperplane. -/
theorem hyperplane_inertia_bound
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (Q : QuadraticForm ℝ V) (H : Submodule ℝ V)
    (hH : Module.finrank ℝ H + 1 = Module.finrank ℝ V)
    (hpsd : ∀ x ∈ H, 0 ≤ Q x) :
    sigNeg Q ≤ 1 := by
  obtain ⟨N, hNdim, hNneg⟩ := exists_finrank_eq_sigNeg_and_negDef Q
  have hdisjoint : Disjoint N H := by
    rw [Submodule.disjoint_def]
    intro x hxN hxH
    by_contra hx
    have hneg : Q x < 0 := by
      have hp := hNneg ⟨x, hxN⟩ (by simpa using hx)
      simpa [QuadraticMap.restrict_apply] using hp
    exact (not_lt_of_ge (hpsd x hxH)) hneg
  have hdim := Submodule.finrank_add_finrank_le_of_disjoint hdisjoint
  rw [hNdim, ← hH] at hdim
  omega

end DelPezzoBlekherman
