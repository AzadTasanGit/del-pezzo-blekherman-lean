/-
Copyright (c) 2026 Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.SesquilinearForm.Basic

/-!
# Kernel faces of cones of positive-semidefinite forms

This file begins the formalization of Lemma 3.2. The paper works with symmetric
bilinear forms and their bilinear radicals; mathlib represents such a form by
`LinearMap.BilinForm` and its radical by `LinearMap.ker`.
-/

open LinearMap (BilinForm)

namespace DelPezzoBlekherman

/-- A nonzero element spans an extreme ray of a cone when every conical decomposition
has both summands on the same nonnegative ray. -/
def SpansExtremeRay {E : Type*} [AddCommMonoid E] [SMul ℝ E]
    (C : Set E) (x : E) : Prop :=
  x ∈ C ∧ x ≠ 0 ∧
    ∀ y ∈ C, ∀ z ∈ C, x = y + z →
      ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ y = a • x ∧ z = b • x

/-- The cone obtained by intersecting a linear space of bilinear forms with the
positive-semidefinite cone. -/
def psdIn {V : Type*} [AddCommGroup V] [Module ℝ V]
    (H : Submodule ℝ (BilinForm ℝ V)) : Set (BilinForm ℝ V) :=
  {B | B ∈ H ∧ B.IsPosSemidef}

/-- For a positive-semidefinite symmetric bilinear form, a zero quadratic value is
equivalent to membership in the bilinear radical. This is the Cauchy--Schwarz step
used in the converse half of Lemma 3.2. -/
theorem psd_eq_zero_iff_mem_ker
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {B : BilinForm ℝ V} (hB : B.IsPosSemidef) (x : V) :
    B x x = 0 ↔ x ∈ LinearMap.ker B :=
  B.apply_apply_same_eq_zero_iff hB.isNonneg.nonneg
    (LinearMap.BilinForm.isSymm_iff.mp hB.isSymm)

/-- The kernel-uniqueness criterion implies extremality.

This is the direction `(ii) -> (i)` of Lemma 3.2. It is the direction used to prove
the converse fiber constructions are extreme: in a decomposition `Q = Q₁ + Q₂`,
positive semidefiniteness forces `ker Q` into both summand radicals, after which the
one-dimensional kernel face makes both summands proportional to `Q`. -/
theorem kernel_face_extreme_of_unique
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (H : Submodule ℝ (BilinForm ℝ V)) (Q : BilinForm ℝ V)
    (hQH : Q ∈ H) (hQpsd : Q.IsPosSemidef) (hQ0 : Q ≠ 0)
    (hunique : ∀ P ∈ H, LinearMap.ker Q ≤ LinearMap.ker P → ∃ a : ℝ, P = a • Q) :
    SpansExtremeRay (psdIn H) Q := by
  refine ⟨⟨hQH, hQpsd⟩, hQ0, ?_⟩
  intro Q₁ hQ₁ Q₂ hQ₂ hsum
  rcases hQ₁ with ⟨hQ₁H, hQ₁psd⟩
  rcases hQ₂ with ⟨hQ₂H, hQ₂psd⟩
  have hker₁ : LinearMap.ker Q ≤ LinearMap.ker Q₁ := by
    intro v hv
    have hdiag : Q v v = 0 := by
      rw [show Q v = 0 from LinearMap.mem_ker.mp hv]
      rfl
    have hsumdiag : Q₁ v v + Q₂ v v = 0 := by
      simpa [hsum] using hdiag
    have h₁zero : Q₁ v v = 0 := by
      have h₁ := hQ₁psd.isNonneg.nonneg v
      have h₂ := hQ₂psd.isNonneg.nonneg v
      linarith
    exact (psd_eq_zero_iff_mem_ker hQ₁psd v).mp h₁zero
  have hker₂ : LinearMap.ker Q ≤ LinearMap.ker Q₂ := by
    intro v hv
    have hdiag : Q v v = 0 := by
      rw [show Q v = 0 from LinearMap.mem_ker.mp hv]
      rfl
    have hsumdiag : Q₁ v v + Q₂ v v = 0 := by
      simpa [hsum] using hdiag
    have h₂zero : Q₂ v v = 0 := by
      have h₁ := hQ₁psd.isNonneg.nonneg v
      have h₂ := hQ₂psd.isNonneg.nonneg v
      linarith
    exact (psd_eq_zero_iff_mem_ker hQ₂psd v).mp h₂zero
  obtain ⟨a, ha⟩ := hunique Q₁ hQ₁H hker₁
  obtain ⟨b, hb⟩ := hunique Q₂ hQ₂H hker₂
  have hex : ∃ v : V, 0 < Q v v := by
    by_contra hn
    push Not at hn
    have hall : ∀ v : V, Q v v = 0 := fun v ↦
      le_antisymm (hn v) (hQpsd.isNonneg.nonneg v)
    have hker : LinearMap.ker Q = ⊤ := by
      rw [eq_top_iff]
      intro v _
      exact (psd_eq_zero_iff_mem_ker hQpsd v).mp (hall v)
    apply hQ0
    rw [LinearMap.ker_eq_top] at hker
    exact hker
  obtain ⟨v, hv⟩ := hex
  have ha0 : 0 ≤ a := by
    have h := hQ₁psd.isNonneg.nonneg v
    rw [ha] at h
    change 0 ≤ a * Q v v at h
    nlinarith
  have hb0 : 0 ≤ b := by
    have h := hQ₂psd.isNonneg.nonneg v
    rw [hb] at h
    change 0 ≤ b * Q v v at h
    nlinarith
  exact ⟨a, b, ha0, hb0, ha, hb⟩

/-- The perturbative algebra in the reverse direction of Lemma 3.2.  If `Q`
spans an extreme ray and both `Q + ε P` and `Q - ε P` are PSD for some
positive `ε`, then `P` is proportional to `Q`. -/
theorem proportional_of_extreme_and_two_sided_psd
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (H : Submodule ℝ (BilinForm ℝ V)) (Q P : BilinForm ℝ V)
    (hQext : SpansExtremeRay (psdIn H) Q)
    (hPH : P ∈ H) {ε : ℝ} (hε : 0 < ε)
    (hplus : (Q + ε • P).IsPosSemidef)
    (hminus : (Q - ε • P).IsPosSemidef) :
    ∃ a : ℝ, P = a • Q := by
  let Y : BilinForm ℝ V := (2 : ℝ)⁻¹ • (Q + ε • P)
  let Z : BilinForm ℝ V := (2 : ℝ)⁻¹ • (Q - ε • P)
  have hQH : Q ∈ H := hQext.1.1
  have hYH : Y ∈ H := H.smul_mem _ (H.add_mem hQH (H.smul_mem _ hPH))
  have hεP : ε • P ∈ H := H.smul_mem ε hPH
  have hsub : Q - ε • P ∈ H := by
    have heq : Q - ε • P = Q + (-ε) • P := by
      ext x y
      simp
      ring
    rw [heq]
    exact H.add_mem hQH (H.smul_mem (-ε) hPH)
  have hZH : Z ∈ H := H.smul_mem _ hsub
  have hhalf : (0 : ℝ) ≤ (2 : ℝ)⁻¹ := by norm_num
  have hYpsd : Y.IsPosSemidef := hplus.smul hhalf
  have hZpsd : Z.IsPosSemidef := hminus.smul hhalf
  have hsum : Q = Y + Z := by
    ext x y
    simp only [Y, Z, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul]
    ring
  obtain ⟨a, _, _, _, hYa, _⟩ :=
    hQext.2.2 Y ⟨hYH, hYpsd⟩ Z ⟨hZH, hZpsd⟩ hsum
  refine ⟨(2 * a - 1) / ε, ?_⟩
  ext x y
  have happ := LinearMap.congr_fun (LinearMap.congr_fun hYa x) y
  simp only [Y, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at happ ⊢
  field_simp [ne_of_gt hε]
  linarith

/-- Reverse kernel-face criterion with the finite-dimensional perturbation estimate
exposed as a hypothesis.  In Lemma 3.2 that estimate follows by restricting to a
complement of `ker Q`, where `Q` is positive definite. -/
theorem kernel_face_unique_of_extreme_of_perturbable
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (H : Submodule ℝ (BilinForm ℝ V)) (Q : BilinForm ℝ V)
    (hQext : SpansExtremeRay (psdIn H) Q)
    (hperturb : ∀ P ∈ H, LinearMap.ker Q ≤ LinearMap.ker P →
      ∃ ε : ℝ, 0 < ε ∧ (Q + ε • P).IsPosSemidef ∧
        (Q - ε • P).IsPosSemidef) :
    ∀ P ∈ H, LinearMap.ker Q ≤ LinearMap.ker P →
      ∃ a : ℝ, P = a • Q := by
  intro P hPH hker
  obtain ⟨ε, hε, hplus, hminus⟩ := hperturb P hPH hker
  exact proportional_of_extreme_and_two_sided_psd H Q P hQext hPH hε hplus hminus

end DelPezzoBlekherman
