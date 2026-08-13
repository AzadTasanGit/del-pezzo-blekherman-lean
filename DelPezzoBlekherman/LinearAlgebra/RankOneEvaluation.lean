/-
Copyright (c) 2026 Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import DelPezzoBlekherman.LinearAlgebra.DiagonalDomination

/-!
# Rank-one evaluation forms

This file proves the reusable linear-algebra statement behind Corollary 3.3:
the square of any nonzero linear functional spans an extreme ray in every linear
space of symmetric bilinear forms which contains it.
-/

open LinearMap (BilinForm)

namespace DelPezzoBlekherman

/-- The rank-one bilinear form `f(x) f(y)`. -/
noncomputable def rankOneBilin {V : Type*} [AddCommGroup V] [Module ℝ V]
    (f : V →ₗ[ℝ] ℝ) : BilinForm ℝ V :=
  LinearMap.mk₂ ℝ (fun x y ↦ f x * f y)
    (by intros; simp; ring)
    (by intros; simp; ring)
    (by intros; simp; ring)
    (by intros; simp; ring)

@[simp] theorem rankOneBilin_apply {V : Type*} [AddCommGroup V] [Module ℝ V]
    (f : V →ₗ[ℝ] ℝ) (x y : V) : rankOneBilin f x y = f x * f y := rfl

theorem rankOneBilin_isPosSemidef {V : Type*} [AddCommGroup V] [Module ℝ V]
    (f : V →ₗ[ℝ] ℝ) : (rankOneBilin f).IsPosSemidef := by
  refine ⟨?_, ?_⟩
  · rw [LinearMap.BilinForm.isSymm_def]
    intro x y
    simp [mul_comm]
  · constructor
    intro x
    simp only [rankOneBilin_apply]
    exact mul_self_nonneg _

theorem rankOneBilin_ne_zero {V : Type*} [AddCommGroup V] [Module ℝ V]
    (f : V →ₗ[ℝ] ℝ) (hf : f ≠ 0) : rankOneBilin f ≠ 0 := by
  intro h
  apply hf
  ext x
  have hx := LinearMap.congr_fun (LinearMap.congr_fun h x) x
  simp only [rankOneBilin_apply, LinearMap.zero_apply] at hx
  exact mul_self_eq_zero.mp hx

theorem ker_rankOneBilin_eq
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (f : V →ₗ[ℝ] ℝ) (hf : f ≠ 0) :
    LinearMap.ker (rankOneBilin f) = LinearMap.ker f := by
  ext v
  constructor
  · intro hv
    obtain ⟨w, hfw⟩ : ∃ w, f w ≠ 0 := by
      by_contra hn
      push Not at hn
      apply hf
      ext x
      exact hn x
    have happ := LinearMap.congr_fun (LinearMap.mem_ker.mp hv) w
    simp only [rankOneBilin_apply, LinearMap.zero_apply] at happ
    apply LinearMap.mem_ker.mpr
    rcases mul_eq_zero.mp happ with hv | hw
    · exact hv
    · exact (hfw hw).elim
  · intro hv
    have hfv := LinearMap.mem_ker.mp hv
    apply LinearMap.mem_ker.mpr
    ext w
    simp [rankOneBilin_apply, hfv]

/-- In a linear space consisting of symmetric forms, every form whose radical
contains the kernel of a nonzero rank-one form is proportional to it. -/
theorem rankOneBilin_unique_of_symmetric_space
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (H : Submodule ℝ (BilinForm ℝ V))
    (hHsymm : ∀ P ∈ H, P.IsSymm)
    (f : V →ₗ[ℝ] ℝ) (hf : f ≠ 0)
    (P : BilinForm ℝ V) (hPH : P ∈ H)
    (hker : LinearMap.ker (rankOneBilin f) ≤ LinearMap.ker P) :
    ∃ a : ℝ, P = a • rankOneBilin f := by
  have hex : ∃ w : V, f w ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hf
    ext w
    exact hn w
  obtain ⟨w, hw⟩ := hex
  let v : V := (f w)⁻¹ • w
  have hv : f v = 1 := by simp [v, hw]
  let a : ℝ := P v v
  refine ⟨a, ?_⟩
  ext x y
  let kx : V := x - f x • v
  let ky : V := y - f y • v
  have hfkx : f kx = 0 := by simp [kx, hv]
  have hfky : f ky = 0 := by simp [ky, hv]
  have hkxQ : kx ∈ LinearMap.ker (rankOneBilin f) := by
    rw [LinearMap.mem_ker]
    ext z
    simp [hfkx]
  have hkyQ : ky ∈ LinearMap.ker (rankOneBilin f) := by
    rw [LinearMap.mem_ker]
    ext z
    simp [hfky]
  have hkxP : P kx = 0 := LinearMap.mem_ker.mp (hker hkxQ)
  have hkyP : P ky = 0 := LinearMap.mem_ker.mp (hker hkyQ)
  have hx : x = f x • v + kx := by simp [kx]
  have hy : y = f y • v + ky := by simp [ky]
  have hPx : P x = f x • P v := by
    calc
      P x = P (f x • v + kx) := congrArg P hx
      _ = f x • P v := by rw [map_add, map_smul, hkxP, add_zero]
  have hPy : P y = f y • P v := by
    calc
      P y = P (f y • v + ky) := congrArg P hy
      _ = f y • P v := by rw [map_add, map_smul, hkyP, add_zero]
  rw [hPx]
  change f x * P v y = _
  rw [(hHsymm P hPH).eq, hPy]
  change f x * (f y * P v v) = a * (f x * f y)
  simp only [a]
  ring

/-- A nonzero rank-one evaluation form spans an extreme ray of the PSD cone in
any symmetric linear family containing it. -/
theorem rankOne_spansExtremeRay
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (H : Submodule ℝ (BilinForm ℝ V))
    (hHsymm : ∀ P ∈ H, P.IsSymm)
    (f : V →ₗ[ℝ] ℝ) (hf : f ≠ 0)
    (hfH : rankOneBilin f ∈ H) :
    SpansExtremeRay (psdIn H) (rankOneBilin f) := by
  apply kernel_face_extreme_of_unique H (rankOneBilin f) hfH
    (rankOneBilin_isPosSemidef f) (rankOneBilin_ne_zero f hf)
  intro P hPH hker
  exact rankOneBilin_unique_of_symmetric_space H hHsymm f hf P hPH hker

/-- The linear-algebra core of Lemma 4.1: if the radical of an extreme PSD
form is contained in the kernel of a rank-one evaluation form in the same
symmetric family, then the extreme form is a positive multiple of that point
evaluation. -/
theorem extreme_psd_eq_pos_smul_rankOne_of_ker_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (H : Submodule ℝ (BilinForm ℝ V))
    (hHsymm : ∀ P ∈ H, P.IsSymm)
    (Q : BilinForm ℝ V)
    (hQext : SpansExtremeRay (psdIn H) Q)
    (f : V →ₗ[ℝ] ℝ) (hf : f ≠ 0)
    (hfH : rankOneBilin f ∈ H)
    (hker : LinearMap.ker Q ≤ LinearMap.ker (rankOneBilin f)) :
    ∃ b : ℝ, 0 < b ∧ Q = b • rankOneBilin f := by
  obtain ⟨a, ha⟩ :=
    (kernel_face_criterion H hHsymm Q hQext.1.1 hQext.1.2 hQext.2.1).mp
      hQext (rankOneBilin f) hfH hker
  have hex : ∃ v : V, f v ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hf
    ext v
    exact hn v
  obtain ⟨v, hfv⟩ := hex
  have hrank_pos : 0 < rankOneBilin f v v := by
    simp [rankOneBilin_apply, mul_self_pos, hfv]
  have hQnonneg : 0 ≤ Q v v := hQext.1.2.isNonneg.nonneg v
  have ha_pos : 0 < a := by
    have happ := LinearMap.congr_fun (LinearMap.congr_fun ha v) v
    simp only [rankOneBilin_apply, LinearMap.smul_apply, smul_eq_mul] at happ
    by_contra hapos
    push Not at hapos
    have hnonpos : a * Q v v ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hapos hQnonneg
    rw [← happ] at hnonpos
    change 0 < f v * f v at hrank_pos
    linarith
  refine ⟨a⁻¹, inv_pos.mpr ha_pos, ?_⟩
  calc
    Q = a⁻¹ • (a • Q) := by simp [ne_of_gt ha_pos]
    _ = a⁻¹ • rankOneBilin f := by rw [← ha]

/-- Abstract extreme-ray dichotomy of Lemma 4.1.  Relative to a family of
nonzero point-evaluation functionals, an extreme PSD form is either a positive
evaluation square or its radical has no basepoint. -/
theorem extreme_psd_evaluation_or_basepointFree
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (H : Submodule ℝ (BilinForm ℝ V))
    (hHsymm : ∀ P ∈ H, P.IsSymm)
    (Q : BilinForm ℝ V)
    (hQext : SpansExtremeRay (psdIn H) Q)
    {X : Type*} (ev : X → V →ₗ[ℝ] ℝ)
    (hev0 : ∀ x, ev x ≠ 0)
    (hevH : ∀ x, rankOneBilin (ev x) ∈ H) :
    (∃ x, ∃ b : ℝ, 0 < b ∧ Q = b • rankOneBilin (ev x)) ∨
      ∀ x, ¬ LinearMap.ker Q ≤ LinearMap.ker (ev x) := by
  by_cases hbase : ∃ x, LinearMap.ker Q ≤ LinearMap.ker (ev x)
  · left
    obtain ⟨x, hx⟩ := hbase
    have hker_rankOne : LinearMap.ker Q ≤ LinearMap.ker (rankOneBilin (ev x)) := by
      intro v hv
      have hev : ev x v = 0 := LinearMap.mem_ker.mp (hx hv)
      apply LinearMap.mem_ker.mpr
      ext y
      simp [rankOneBilin_apply, hev]
    obtain ⟨b, hb, hQ⟩ := extreme_psd_eq_pos_smul_rankOne_of_ker_le
      H hHsymm Q hQext (ev x) (hev0 x) (hevH x) hker_rankOne
    exact ⟨x, b, hb, hQ⟩
  · right
    push Not at hbase
    exact hbase

/-- The two alternatives of the abstract Lemma 4.1 dichotomy are mutually
exclusive. -/
theorem extreme_psd_evaluation_xor_basepointFree
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (H : Submodule ℝ (BilinForm ℝ V))
    (hHsymm : ∀ P ∈ H, P.IsSymm)
    (Q : BilinForm ℝ V)
    (hQext : SpansExtremeRay (psdIn H) Q)
    {X : Type*} (ev : X → V →ₗ[ℝ] ℝ)
    (hev0 : ∀ x, ev x ≠ 0)
    (hevH : ∀ x, rankOneBilin (ev x) ∈ H) :
    Xor (∃ x, ∃ b : ℝ, 0 < b ∧ Q = b • rankOneBilin (ev x))
      (∀ x, ¬ LinearMap.ker Q ≤ LinearMap.ker (ev x)) := by
  rcases extreme_psd_evaluation_or_basepointFree H hHsymm Q hQext ev hev0 hevH with
    heval | hfree
  · refine Or.inl ⟨heval, ?_⟩
    intro hnotfree
    obtain ⟨x, b, hb, hQ⟩ := heval
    apply hnotfree x
    intro v hv
    have hv' : v ∈ LinearMap.ker (rankOneBilin (ev x)) := by
      apply LinearMap.mem_ker.mpr
      have hQv := LinearMap.mem_ker.mp hv
      rw [hQ] at hQv
      simpa [ne_of_gt hb] using hQv
    rwa [ker_rankOneBilin_eq (ev x) (hev0 x)] at hv'
  · refine Or.inr ⟨hfree, ?_⟩
    intro heval
    obtain ⟨x, b, hb, hQ⟩ := heval
    apply hfree x
    intro v hv
    have hv' : v ∈ LinearMap.ker (rankOneBilin (ev x)) := by
      apply LinearMap.mem_ker.mpr
      have hQv := LinearMap.mem_ker.mp hv
      rw [hQ] at hQv
      simpa [ne_of_gt hb] using hQv
    rwa [ker_rankOneBilin_eq (ev x) (hev0 x)] at hv'

end DelPezzoBlekherman
