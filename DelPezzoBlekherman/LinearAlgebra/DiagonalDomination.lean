/-
Copyright (c) 2026 Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import DelPezzoBlekherman.LinearAlgebra.KernelFace

/-!
# Diagonal domination and PSD perturbations

A positive-definite bilinear form dominates the diagonal of every other bilinear
form in finite dimension. Applying this on a complement of a PSD form's radical
produces the two-sided perturbations used in the reverse direction of the
kernel-face criterion.
-/


open LinearMap (BilinForm)
open Metric

namespace DelPezzoBlekherman

noncomputable def bilinToContinuous
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (B : BilinForm ℝ V) : V →L[ℝ] (V →L[ℝ] ℝ) := by
  let f : V →ₗ[ℝ] (V →L[ℝ] ℝ) :=
    { toFun := fun x ↦ ⟨B x, (B x).continuous_of_finiteDimensional⟩
      map_add' := by
        intro x y
        ext z
        simp
      map_smul' := by
        intro c x
        ext z
        simp }
  exact ⟨f, f.continuous_of_finiteDimensional⟩

@[simp] theorem bilinToContinuous_apply
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (B : BilinForm ℝ V) (x y : V) : bilinToContinuous B x y = B x y := rfl

theorem bilin_diagonal_continuous
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (B : BilinForm ℝ V) : Continuous (fun x : V ↦ B x x) := by
  change Continuous (fun x : V ↦ bilinToContinuous B x x)
  exact (bilinToContinuous B).continuous.clm_apply continuous_id

theorem exists_diagonal_domination_of_posDef
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [Nontrivial V]
    (Q P : BilinForm ℝ V) (hQ : Q.toQuadraticMap.PosDef) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : V, |P x x| ≤ C * Q x x := by
  let S : Set V := sphere 0 1
  have hSc : IsCompact S := isCompact_sphere 0 1
  obtain ⟨e, he⟩ : ∃ e : V, ‖e‖ = 1 := by
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    exact ⟨‖x‖⁻¹ • x, by simp [norm_smul, hx]⟩
  have hS0 : S.Nonempty := ⟨e, by simpa [S]⟩
  obtain ⟨q, hqS, hqmin⟩ :=
    hSc.exists_isMinOn hS0 (bilin_diagonal_continuous Q).continuousOn
  obtain ⟨p, hpS, hpmax⟩ :=
    hSc.exists_isMaxOn hS0 (bilin_diagonal_continuous P).abs.continuousOn
  have hq0 : q ≠ 0 := by
    have hnorm : ‖q‖ = 1 := by simpa [S] using hqS
    intro hq
    subst q
    norm_num at hnorm
  have hQq : 0 < Q q q := by
    simpa [LinearMap.BilinMap.toQuadraticMap_apply] using hQ q hq0
  let C : ℝ := |P p p| / (Q q q)
  have hC : 0 ≤ C := div_nonneg (abs_nonneg _) (le_of_lt hQq)
  refine ⟨C, hC, ?_⟩
  intro x
  by_cases hx : x = 0
  · subst x
    simp
  let u : V := ‖x‖⁻¹ • x
  have huS : u ∈ S := by
    have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    simp [S, u, norm_smul, hnorm]
  have hQlower : Q q q ≤ Q u u := hqmin huS
  have hPupper : |P u u| ≤ |P p p| := hpmax huS
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hQu : Q x x = ‖x‖ ^ 2 * Q u u := by
    have hxu : x = ‖x‖ • u := by simp [u, hx]
    calc
      Q x x = Q (‖x‖ • u) (‖x‖ • u) := congrArg₂ (fun z w ↦ Q z w) hxu hxu
      _ = ‖x‖ ^ 2 * Q u u := by simp [pow_two]; ring
  have hPu : |P x x| = ‖x‖ ^ 2 * |P u u| := by
    have hxu : x = ‖x‖ • u := by simp [u, hx]
    calc
      |P x x| = |P (‖x‖ • u) (‖x‖ • u)| := congrArg (fun z ↦ |P z z|) hxu
      _ = ‖x‖ ^ 2 * |P u u| := by
        simp [abs_mul, pow_two, abs_of_nonneg (norm_nonneg x)]
        ring
  rw [hPu, hQu]
  have hratio : |P p p| ≤ C * Q u u := by
    calc
      |P p p| = C * Q q q := by dsimp [C]; field_simp [ne_of_gt hQq]
      _ ≤ C * Q u u := mul_le_mul_of_nonneg_left hQlower hC
  have hunit : |P u u| ≤ C * Q u u := hPupper.trans hratio
  calc
    ‖x‖ ^ 2 * |P u u| ≤ ‖x‖ ^ 2 * (C * Q u u) :=
      mul_le_mul_of_nonneg_left hunit (sq_nonneg _)
    _ = C * (‖x‖ ^ 2 * Q u u) := by ring

theorem exists_two_sided_psd_perturbation
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Q P : BilinForm ℝ V) (C : Submodule ℝ V)
    (hQ : Q.IsPosSemidef) (hP : P.IsSymm)
    (hker : LinearMap.ker Q ≤ LinearMap.ker P)
    (hcompl : IsCompl (LinearMap.ker Q) C) :
    ∃ ε : ℝ, 0 < ε ∧ (Q + ε • P).IsPosSemidef ∧
      (Q - ε • P).IsPosSemidef := by
  have hQpos : (Q.restrict C).toQuadraticMap.PosDef := by
    intro x hx
    have hnonneg := hQ.isNonneg.nonneg x.1
    change 0 < Q x.1 x.1
    apply lt_of_le_of_ne hnonneg
    intro hzero
    have hxker : x.1 ∈ LinearMap.ker Q :=
      (psd_eq_zero_iff_mem_ker hQ x.1).mp (Eq.symm hzero)
    have hxbot : x.1 ∈ (LinearMap.ker Q ⊓ C) := ⟨hxker, x.2⟩
    have : x.1 = 0 := by
      have : x.1 ∈ (⊥ : Submodule ℝ V) := by
        rw [← hcompl.disjoint.eq_bot]
        exact hxbot
      simpa using this
    exact hx (Subtype.ext this)
  by_cases hC : Nontrivial C
  · let _ : Nontrivial C := hC
    obtain ⟨M, hM0, hbound⟩ := exists_diagonal_domination_of_posDef
      (Q.restrict C) (P.restrict C) hQpos
    let ε : ℝ := (M + 1)⁻¹
    have hden : 0 < M + 1 := by linarith
    have hε : 0 < ε := inv_pos.mpr hden
    have hεM : ε * M < 1 := by
      dsimp [ε]
      rw [inv_mul_eq_div]
      exact (div_lt_one hden).mpr (by linarith)
    have hrestrictPlus : ((Q + ε • P).restrict C).IsPosSemidef := by
      refine ⟨hQ.isSymm.add (hP.smul ε) |>.restrict C, ?_⟩
      constructor
      intro x
      have hb := hbound x
      have hq := hQ.isNonneg.nonneg x.1
      change 0 ≤ Q x.1 x.1 + ε * P x.1 x.1
      have hpneg : -|P x.1 x.1| ≤ P x.1 x.1 := neg_abs_le _
      have : ε * |P x.1 x.1| ≤ ε * M * Q x.1 x.1 := by
        have := mul_le_mul_of_nonneg_left hb (le_of_lt hε)
        simpa [mul_assoc] using this
      nlinarith
    have hrestrictMinus : ((Q - ε • P).restrict C).IsPosSemidef := by
      refine ⟨?_, ?_⟩
      · rw [show Q - ε • P = Q + (-ε) • P by ext x y; simp; ring]
        exact (hQ.isSymm.add (hP.smul (-ε))).restrict C
      · constructor
        intro x
        have hb := hbound x
        have hq := hQ.isNonneg.nonneg x.1
        change 0 ≤ Q x.1 x.1 - ε * P x.1 x.1
        have hple : P x.1 x.1 ≤ |P x.1 x.1| := le_abs_self _
        have : ε * |P x.1 x.1| ≤ ε * M * Q x.1 x.1 := by
          have := mul_le_mul_of_nonneg_left hb (le_of_lt hε)
          simpa [mul_assoc] using this
        nlinarith
    refine ⟨ε, hε, ?_, ?_⟩
    · refine ⟨hQ.isSymm.add (hP.smul ε), ?_⟩
      constructor
      intro x
      obtain ⟨u, c, hu, hc, huc⟩ :=
        Submodule.codisjoint_iff_exists_add_eq.mp hcompl.codisjoint x
      let cc : C := ⟨c, hc⟩
      have hval := hrestrictPlus.isNonneg.nonneg cc
      change 0 ≤ Q c c + ε * P c c at hval
      have hQu := LinearMap.mem_ker.mp hu
      have hPu := LinearMap.mem_ker.mp (hker hu)
      have hQdiag : Q x x = Q c c := by
        rw [← huc]
        simp only [map_add, LinearMap.add_apply]
        rw [LinearMap.congr_fun hQu u, LinearMap.congr_fun hQu c,
          hQ.isSymm.eq c u, LinearMap.congr_fun hQu c]
        simp
      have hPdiag : P x x = P c c := by
        rw [← huc]
        simp only [map_add, LinearMap.add_apply]
        rw [LinearMap.congr_fun hPu u, LinearMap.congr_fun hPu c,
          hP.eq c u, LinearMap.congr_fun hPu c]
        simp
      change 0 ≤ Q x x + ε * P x x
      rw [hQdiag, hPdiag]
      exact hval
    · refine ⟨?_, ?_⟩
      · rw [show Q - ε • P = Q + (-ε) • P by ext x y; simp; ring]
        exact hQ.isSymm.add (hP.smul (-ε))
      · constructor
        intro x
        obtain ⟨u, c, hu, hc, huc⟩ :=
          Submodule.codisjoint_iff_exists_add_eq.mp hcompl.codisjoint x
        let cc : C := ⟨c, hc⟩
        have hval := hrestrictMinus.isNonneg.nonneg cc
        change 0 ≤ Q c c - ε * P c c at hval
        have hQu := LinearMap.mem_ker.mp hu
        have hPu := LinearMap.mem_ker.mp (hker hu)
        have hQdiag : Q x x = Q c c := by
          rw [← huc]
          simp only [map_add, LinearMap.add_apply]
          rw [LinearMap.congr_fun hQu u, LinearMap.congr_fun hQu c,
            hQ.isSymm.eq c u, LinearMap.congr_fun hQu c]
          simp
        have hPdiag : P x x = P c c := by
          rw [← huc]
          simp only [map_add, LinearMap.add_apply]
          rw [LinearMap.congr_fun hPu u, LinearMap.congr_fun hPu c,
            hP.eq c u, LinearMap.congr_fun hPu c]
          simp
        change 0 ≤ Q x x - ε * P x x
        rw [hQdiag, hPdiag]
        exact hval
  · have hCsub : Subsingleton C := not_nontrivial_iff_subsingleton.mp hC
    have hkerTop : LinearMap.ker Q = ⊤ := by
      rw [eq_top_iff]
      intro x _
      obtain ⟨u, c, hu, hc, huc⟩ :=
        Submodule.codisjoint_iff_exists_add_eq.mp hcompl.codisjoint x
      have hc0 : c = 0 := by
        have : (⟨c, hc⟩ : C) = 0 := Subsingleton.elim _ _
        exact congrArg Subtype.val this
      rw [hc0, add_zero] at huc
      exact huc ▸ hu
    have hQzero : Q = 0 := LinearMap.ker_eq_top.mp hkerTop
    have hPzero : P = 0 := by
      rw [hkerTop] at hker
      have : LinearMap.ker P = ⊤ := top_unique hker
      exact LinearMap.ker_eq_top.mp this
    refine ⟨1, by norm_num, ?_, ?_⟩
    · have hz : Q + (1 : ℝ) • P = 0 := by ext x y; simp [hQzero, hPzero]
      rw [hz]
      exact LinearMap.BilinForm.isPosSemidef_zero
    · have hz : Q - (1 : ℝ) • P = 0 := by ext x y; simp [hQzero, hPzero]
      rw [hz]
      exact LinearMap.BilinForm.isPosSemidef_zero

/-- The formerly missing reverse direction of the kernel-face criterion. -/
theorem kernel_face_unique_of_extreme
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (H : Submodule ℝ (BilinForm ℝ V))
    (hHsymm : ∀ P ∈ H, P.IsSymm)
    (Q : BilinForm ℝ V) (hQext : SpansExtremeRay (psdIn H) Q) :
    ∀ P ∈ H, LinearMap.ker Q ≤ LinearMap.ker P →
      ∃ a : ℝ, P = a • Q := by
  intro P hPH hker
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (LinearMap.ker Q)
  obtain ⟨ε, hε, hplus, hminus⟩ := exists_two_sided_psd_perturbation
    Q P C hQext.1.2 (hHsymm P hPH) hker hC
  exact proportional_of_extreme_and_two_sided_psd
    H Q P hQext hPH hε hplus hminus

/-- Lemma 3.2 in full for a finite-dimensional normed real vector space and a
linear family of symmetric bilinear forms. -/
theorem kernel_face_criterion
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (H : Submodule ℝ (BilinForm ℝ V))
    (hHsymm : ∀ P ∈ H, P.IsSymm)
    (Q : BilinForm ℝ V) (hQH : Q ∈ H)
    (hQpsd : Q.IsPosSemidef) (hQ0 : Q ≠ 0) :
    SpansExtremeRay (psdIn H) Q ↔
      ∀ P ∈ H, LinearMap.ker Q ≤ LinearMap.ker P →
        ∃ a : ℝ, P = a • Q := by
  constructor
  · exact kernel_face_unique_of_extreme H hHsymm Q
  · exact kernel_face_extreme_of_unique H Q hQH hQpsd hQ0

end DelPezzoBlekherman
