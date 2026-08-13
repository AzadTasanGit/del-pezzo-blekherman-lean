/-
Copyright (c) 2026 Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Radicals of hyperplane restrictions

This file isolates the common bilinear-algebra mechanism behind Lemmas 7.1 and 7.3.
If a nondegenerate symmetric form identifies a vector `ρ` with a linear functional
defining a hyperplane, then the restriction has radical exactly the line through `ρ`
when `ρ` lies on that hyperplane.
-/

open LinearMap (BilinForm)

namespace DelPezzoBlekherman

/-- The radical of the restriction of a symmetric bilinear form to `W`, mapped back
into the ambient space, is `W ∩ Wᗮ`. -/
theorem map_ker_restrict_eq_inf_orthogonal
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : BilinForm K V) (hB : B.IsSymm) (W : Submodule K V) :
    (LinearMap.ker (B.restrict W)).map W.subtype = W ⊓ B.orthogonal W := by
  apply le_antisymm
  · rintro x hx
    rcases hx with ⟨x, hxker, rfl⟩
    refine ⟨x.property, ?_⟩
    intro y hy
    have hz := LinearMap.congr_fun (LinearMap.mem_ker.mp hxker) ⟨y, hy⟩
    simpa [LinearMap.BilinForm.restrict_apply, hB.eq] using hz
  · exact B.inf_orthogonal_self_le_ker_restrict hB.isRefl

/-- If `B(-, ρ) = L`, `B` is nondegenerate, `ker L` is a hyperplane, and `L ρ = 0`,
then the mapped radical of `B` restricted to `ker L` is precisely `ℝ ρ`.

This is normalization-free and applies to both the fully real diagonal evaluation
form and the one-conjugate-pair Lorentzian evaluation form. -/
theorem hyperplane_restriction_radical_span
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (B : BilinForm ℝ V) (hBsymm : B.IsSymm) (hBnondeg : B.Nondegenerate)
    (L : V →ₗ[ℝ] ℝ) (ρ : V)
    (hH : Module.finrank ℝ (LinearMap.ker L) + 1 = Module.finrank ℝ V)
    (hρ : ρ ≠ 0) (hrep : ∀ x, B x ρ = L x) (hnull : L ρ = 0) :
    (LinearMap.ker (B.restrict (LinearMap.ker L))).map (LinearMap.ker L).subtype =
      ℝ ∙ ρ := by
  let H := LinearMap.ker L
  change Module.finrank ℝ H + 1 = Module.finrank ℝ V at hH
  have hρH : ρ ∈ H := LinearMap.mem_ker.mpr hnull
  have hρorth : ρ ∈ B.orthogonal H := by
    intro x hx
    rw [hrep]
    exact LinearMap.mem_ker.mp hx
  have hspan_le : ℝ ∙ ρ ≤ B.orthogonal H :=
    (Submodule.span_singleton_le_iff_mem ρ _).mpr hρorth
  have horth_finrank : Module.finrank ℝ (B.orthogonal H) = 1 := by
    rw [B.finrank_orthogonal hBnondeg H]
    omega
  have horth_eq : B.orthogonal H = ℝ ∙ ρ := by
    symm
    apply Submodule.eq_of_le_of_finrank_le hspan_le
    rw [finrank_span_singleton hρ, horth_finrank]
  rw [map_ker_restrict_eq_inf_orthogonal B hBsymm H, horth_eq]
  exact inf_eq_right.mpr ((Submodule.span_singleton_le_iff_mem ρ H).mpr hρH)

end DelPezzoBlekherman
