/-
Copyright (c) 2026 Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import DelPezzoBlekherman.Convexity.DualSlice

/-!
# Final separation assemblies

These theorems isolate the last logical step of Theorems 8.2 and 8.3.  Once an
extreme dual ray is known to satisfy the paper's evaluation/basepoint-free
dichotomy, positivity rules out the evaluation branch.
-/

open Set

namespace DelPezzoBlekherman

/-- Conditional abstract form of Theorem 8.2.  `IsEvaluationRay` is the
positive point-evaluation branch and `Good` packages the basepoint-free kernel,
dimension, and rank conclusions supplied by Lemma 4.1 and Theorem 4.3. -/
theorem complete_extreme_separation_of_ray_dichotomy
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (C P : Set E) (hCconv : Convex ℝ C) (hCclosed : IsClosed C)
    (hzero : (0 : E) ∈ C)
    (hsmul : ∀ {a : ℝ}, 0 ≤ a → ∀ {x}, x ∈ C → a • x ∈ C)
    (rho : E) (hrho : rho ∈ interior C)
    (IsEvaluationRay Good : (E →L[ℝ] ℝ) → Prop)
    (hdichotomy : ∀ ℓ, SpansExtremeRay (dualConeSet C) ℓ →
      IsEvaluationRay ℓ ∨ Good ℓ)
    (hevaluation_nonneg : ∀ ℓ, IsEvaluationRay ℓ → ∀ p ∈ P, 0 ≤ ℓ p)
    {p : E} (hpP : p ∈ P) (hpC : p ∉ C) :
    ∃ ℓ : E →L[ℝ] ℝ,
      SpansExtremeRay (dualConeSet C) ℓ ∧ ℓ p < 0 ∧ Good ℓ := by
  obtain ⟨ℓ, hℓray, hℓp⟩ :=
    exists_extreme_dual_neg_of_not_mem_closed_convex_cone
      C hCconv hCclosed hzero hsmul rho hrho hpC
  rcases hdichotomy ℓ hℓray with hℓeval | hℓgood
  · have := hevaluation_nonneg ℓ hℓeval p hpP
    linarith
  · exact ⟨ℓ, hℓray, hℓp, hℓgood⟩

/-- Point-evaluation-specialized form of the complete separation assembly. -/
theorem complete_extreme_separation_of_evaluation_dichotomy
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (C P : Set E) (hCconv : Convex ℝ C) (hCclosed : IsClosed C)
    (hzero : (0 : E) ∈ C)
    (hsmul : ∀ {a : ℝ}, 0 ≤ a → ∀ {x}, x ∈ C → a • x ∈ C)
    (rho : E) (hrho : rho ∈ interior C)
    {X : Type*} (ev : X → E →L[ℝ] ℝ)
    (Good : (E →L[ℝ] ℝ) → Prop)
    (hdichotomy : ∀ ℓ, SpansExtremeRay (dualConeSet C) ℓ →
      (∃ x, ∃ a : ℝ, 0 < a ∧ ℓ = a • ev x) ∨ Good ℓ)
    (hev_nonneg : ∀ x p, p ∈ P → 0 ≤ ev x p)
    {p : E} (hpP : p ∈ P) (hpC : p ∉ C) :
    ∃ ℓ : E →L[ℝ] ℝ,
      SpansExtremeRay (dualConeSet C) ℓ ∧ ℓ p < 0 ∧ Good ℓ := by
  apply complete_extreme_separation_of_ray_dichotomy C P hCconv hCclosed hzero
    hsmul rho hrho (fun ℓ => ∃ x, ∃ a : ℝ, 0 < a ∧ ℓ = a • ev x) Good
    hdichotomy _ hpP hpC
  rintro ℓ ⟨x, a, ha, rfl⟩ q hq
  simp only [smul_apply, smul_eq_mul]
  exact mul_nonneg (le_of_lt ha) (hev_nonneg x q hq)

/-- Conditional first step of Theorem 8.3.  Strict positivity on all point
evaluation rays forces an extreme supporting ray at a boundary sum of squares
into the basepoint-free branch. -/
theorem boundary_extreme_support_good_of_ray_dichotomy
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (C : Set E) (hCconv : Convex ℝ C) (hCclosed : IsClosed C)
    (hzero : (0 : E) ∈ C)
    (hsmul : ∀ {a : ℝ}, 0 ≤ a → ∀ {x}, x ∈ C → a • x ∈ C)
    (rho : E) (hrho : rho ∈ interior C)
    (IsEvaluationRay Good : (E →L[ℝ] ℝ) → Prop)
    (hdichotomy : ∀ ℓ, SpansExtremeRay (dualConeSet C) ℓ →
      IsEvaluationRay ℓ ∨ Good ℓ)
    {p : E} (hp : p ∈ frontier C)
    (hstrict : ∀ ℓ, IsEvaluationRay ℓ → 0 < ℓ p) :
    ∃ ℓ : E →L[ℝ] ℝ,
      SpansExtremeRay (dualConeSet C) ℓ ∧ ℓ p = 0 ∧ Good ℓ := by
  obtain ⟨ℓ, hℓray, hℓp⟩ :=
    exists_extreme_dual_eq_zero_of_mem_frontier_closed_convex_cone
      C hCconv hCclosed hzero hsmul rho hrho hp
  rcases hdichotomy ℓ hℓray with hℓeval | hℓgood
  · have := hstrict ℓ hℓeval
    linarith
  · exact ⟨ℓ, hℓray, hℓp, hℓgood⟩

/-- Point-evaluation-specialized form of the strictly-positive boundary
support assembly. -/
theorem boundary_extreme_support_good_of_evaluation_dichotomy
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (C : Set E) (hCconv : Convex ℝ C) (hCclosed : IsClosed C)
    (hzero : (0 : E) ∈ C)
    (hsmul : ∀ {a : ℝ}, 0 ≤ a → ∀ {x}, x ∈ C → a • x ∈ C)
    (rho : E) (hrho : rho ∈ interior C)
    {X : Type*} (ev : X → E →L[ℝ] ℝ)
    (Good : (E →L[ℝ] ℝ) → Prop)
    (hdichotomy : ∀ ℓ, SpansExtremeRay (dualConeSet C) ℓ →
      (∃ x, ∃ a : ℝ, 0 < a ∧ ℓ = a • ev x) ∨ Good ℓ)
    {p : E} (hp : p ∈ frontier C)
    (hev_pos : ∀ x, 0 < ev x p) :
    ∃ ℓ : E →L[ℝ] ℝ,
      SpansExtremeRay (dualConeSet C) ℓ ∧ ℓ p = 0 ∧ Good ℓ := by
  apply boundary_extreme_support_good_of_ray_dichotomy C hCconv hCclosed hzero
    hsmul rho hrho (fun ℓ => ∃ x, ∃ a : ℝ, 0 < a ∧ ℓ = a • ev x) Good
    hdichotomy hp
  rintro ℓ ⟨x, a, ha, rfl⟩
  simp only [smul_apply, smul_eq_mul]
  exact mul_pos ha (hev_pos x)

end DelPezzoBlekherman
