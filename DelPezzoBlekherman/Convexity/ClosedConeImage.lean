/-
Copyright (c) 2026 Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Closed linear images of cones

This module isolates the properness estimate used in the closedness part of
Proposition 3.1.  A closed subset of a finite-dimensional source has closed
image under a continuous linear map whenever points of the subset have norm
controlled by the norm of their image.
-/

open Set Filter Bornology Metric
open scoped Topology

namespace DelPezzoBlekherman

/-- A closed cone on which a continuous linear map has no nonzero zero admits
a uniform inverse norm estimate.  Compactness of the unit section of the cone
is the finite-dimensional ingredient. -/
theorem exists_norm_le_map_of_closed_cone
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : E →L[ℝ] F) (C : Set E) (hC : IsClosed C)
    (hsmul : ∀ {a : ℝ}, 0 ≤ a → ∀ {x}, x ∈ C → a • x ∈ C)
    (hker : ∀ x ∈ C, T x = 0 → x = 0) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x ∈ C, ‖x‖ ≤ A * ‖T x‖ := by
  by_cases hnonzero : ∃ x ∈ C, x ≠ 0
  · let K : Set E := C ∩ sphere 0 1
    have hKcompact : IsCompact K := by
      rw [Metric.isCompact_iff_isClosed_bounded]
      exact ⟨hC.inter isClosed_sphere, isBounded_sphere.subset inter_subset_right⟩
    have hKnonempty : K.Nonempty := by
      obtain ⟨x, hxC, hx0⟩ := hnonzero
      let q : E := ‖x‖⁻¹ • x
      refine ⟨q, hsmul (inv_nonneg.mpr (norm_nonneg x)) hxC, ?_⟩
      rw [mem_sphere_zero_iff_norm]
      simp [q, norm_smul, hx0]
    obtain ⟨u, huK, humin⟩ := hKcompact.exists_isMinOn hKnonempty
      (T.continuous.norm.continuousOn)
    have hu0 : u ≠ 0 := by
      intro hu
      subst u
      have := huK.2
      simp at this
    have hTu0 : T u ≠ 0 := by
      intro hTu
      exact hu0 (hker u huK.1 hTu)
    have hdelta : 0 < ‖T u‖ := norm_pos_iff.mpr hTu0
    refine ⟨‖T u‖⁻¹, le_of_lt (inv_pos.mpr hdelta), ?_⟩
    intro x hxC
    by_cases hx0 : x = 0
    · subst x
      simp
    let q : E := ‖x‖⁻¹ • x
    have hqK : q ∈ K := by
      refine ⟨hsmul (inv_nonneg.mpr (norm_nonneg x)) hxC, ?_⟩
      rw [mem_sphere_zero_iff_norm]
      simp [q, norm_smul, hx0]
    have hineq := humin hqK
    change ‖T u‖ ≤ ‖T q‖ at hineq
    have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hdelta_x : ‖T u‖ * ‖x‖ ≤ ‖T x‖ := by
      rw [← le_div_iff₀ hxnorm]
      simpa [q, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x),
        div_eq_inv_mul] using hineq
    rw [show ‖T u‖⁻¹ * ‖T x‖ = ‖T x‖ / ‖T u‖ by
      rw [div_eq_inv_mul, mul_comm]]
    exact (le_div_iff₀ hdelta).2 (by simpa [mul_comm] using hdelta_x)
  · refine ⟨0, le_rfl, ?_⟩
    intro x hx
    have hx0 : x = 0 := by
      by_contra h
      exact hnonzero ⟨x, hx, h⟩
    subst x
    simp

/-- A closed subset of a finite-dimensional normed space has closed image when
a uniform norm estimate prevents its points from escaping to infinity inside
bounded image fibers. -/
theorem isClosed_image_of_norm_le_map
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : E →L[ℝ] F) (C : Set E) (hC : IsClosed C)
    (A : ℝ) (hA : 0 ≤ A)
    (hcontrol : ∀ x ∈ C, ‖x‖ ≤ A * ‖T x‖) :
    IsClosed (T '' C) := by
  apply IsSeqClosed.isClosed
  intro ys y hys hy
  choose xs hxsC hxs using hys
  have hybounded : IsBounded (range ys) := Metric.isBounded_range_of_tendsto ys hy
  obtain ⟨M, hM⟩ := hybounded.exists_norm_le
  have hxsbounded : IsBounded (range xs) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨A * M, ?_⟩
    intro x hx
    obtain ⟨n, rfl⟩ := hx
    calc
      ‖xs n‖ ≤ A * ‖T (xs n)‖ := hcontrol (xs n) (hxsC n)
      _ = A * ‖ys n‖ := by rw [hxs n]
      _ ≤ A * M := mul_le_mul_of_nonneg_left (hM (ys n) ⟨n, rfl⟩) hA
  obtain ⟨x, hxclosure, phi, hphi, hxlim⟩ :=
    tendsto_subseq_of_bounded hxsbounded (fun n => ⟨n, rfl⟩)
  have hxC : x ∈ C := by
    apply hC.mem_of_tendsto hxlim
    exact Eventually.of_forall (fun n => hxsC (phi n))
  have hTxlim : Tendsto (fun n => T (xs (phi n))) atTop (𝓝 (T x)) := by
    exact T.continuous.tendsto x |>.comp hxlim
  have hylim : Tendsto (fun n => ys (phi n)) atTop (𝓝 y) :=
    hy.comp hphi.tendsto_atTop
  have hTx : T x = y := by
    apply tendsto_nhds_unique hTxlim
    simpa only [hxs] using hylim
  exact ⟨x, hxC, hTx⟩

/-- A continuous linear image of a closed finite-dimensional cone is closed if
the cone meets the kernel only at zero. -/
theorem isClosed_image_of_closed_cone_ker_eq_zero
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : E →L[ℝ] F) (C : Set E) (hC : IsClosed C)
    (hsmul : ∀ {a : ℝ}, 0 ≤ a → ∀ {x}, x ∈ C → a • x ∈ C)
    (hker : ∀ x ∈ C, T x = 0 → x = 0) :
    IsClosed (T '' C) := by
  obtain ⟨A, hA, hcontrol⟩ :=
    exists_norm_le_map_of_closed_cone T C hC hsmul hker
  exact isClosed_image_of_norm_le_map T C hC A hA hcontrol

end DelPezzoBlekherman
