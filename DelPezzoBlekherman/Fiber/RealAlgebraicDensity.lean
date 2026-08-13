/-
Copyright (c) 2026 Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Density of real principal opens

The real-algebraic density fact used in the perturbation step of Theorem 8.3:
a nonzero real polynomial cannot vanish on a nonempty Euclidean open subset.
-/

open Set MvPolynomial
open scoped Topology

namespace DelPezzoBlekherman

/-- The zero set of a nonzero real multivariate polynomial in finitely many
variables has empty Euclidean interior.  The proof uses analyticity and its
identity principle, followed by polynomial function extensionality over the
infinite field `ℝ`. -/
theorem interior_mvPolynomial_zeroSet_eq_empty
    {sigma : Type*} [Finite sigma]
    (p : MvPolynomial sigma ℝ) (hp : p ≠ 0) :
    interior {x : sigma → ℝ | eval x p = 0} = ∅ := by
  let _ := Fintype.ofFinite sigma
  apply Set.not_nonempty_iff_eq_empty.mp
  intro hnonempty
  obtain ⟨x, hx⟩ := hnonempty
  have hevent : (fun y : sigma → ℝ ↦ eval y p) =ᶠ[𝓝 x] 0 := by
    filter_upwards [isOpen_interior.mem_nhds hx] with y hy
    exact (interior_subset :
      interior {z : sigma → ℝ | eval z p = 0} ⊆ _) hy
  have hana : AnalyticOnNhd ℝ (fun y : sigma → ℝ ↦ eval y p) Set.univ :=
    AnalyticOnNhd.eval_mvPolynomial p
  have heq : (fun y : sigma → ℝ ↦ eval y p) = 0 :=
    hana.eq_of_eventuallyEq analyticOnNhd_const hevent
  apply hp
  apply MvPolynomial.funext
  intro y
  have hy := congrFun heq y
  simpa using hy

/-- The real principal open cut out by a nonzero polynomial is Euclidean
dense. -/
theorem dense_mvPolynomial_ne_zero
    {sigma : Type*} [Finite sigma]
    (p : MvPolynomial sigma ℝ) (hp : p ≠ 0) :
    Dense {x : sigma → ℝ | eval x p ≠ 0} := by
  have h := interior_eq_empty_iff_dense_compl.mp
    (interior_mvPolynomial_zeroSet_eq_empty p hp)
  simpa only [Set.compl_ofPred] using h

/-- Any real algebraic subset contained in the zero set of one nonzero
polynomial has dense Euclidean complement. -/
theorem dense_compl_of_subset_mvPolynomial_zeroSet
    {sigma : Type*} [Finite sigma]
    (Z : Set (sigma → ℝ)) (p : MvPolynomial sigma ℝ) (hp : p ≠ 0)
    (hZ : Z ⊆ {x | eval x p = 0}) :
    Dense Zᶜ := by
  apply (dense_mvPolynomial_ne_zero p hp).mono
  intro x hx hxZ
  exact hx (hZ hxZ)

end DelPezzoBlekherman
