/-
Copyright (c) 2026 Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import Mathlib.Analysis.Convex.KreinMilman
import DelPezzoBlekherman.LinearAlgebra.KernelFace

/-!
# Extreme minimizers on compact slices

This file isolates the Krein--Milman step in Lemma 8.1: a continuous linear
functional on a nonempty compact slice has a minimizer which is an extreme point of
the whole slice.  The minimizer set is an exposed face, so an extreme point of that
face remains extreme in the ambient slice.
-/

open Set

namespace DelPezzoBlekherman

/-- The affine slice of a cone-like set by a normalizing functional. -/
def normalizedSlice {E : Type*} [AddCommGroup E] [Module ℝ E]
    (C : Set E) (n : E →ₗ[ℝ] ℝ) : Set E := {x | x ∈ C ∧ n x = 1}

/-- An extreme point of a normalized cone slice spans an extreme ray.  Strict
positivity of `n` on nonzero cone elements makes every conical decomposition
normalizable. -/
theorem extremePoint_normalizedSlice_spansExtremeRay
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (C : Set E) (n : E →ₗ[ℝ] ℝ)
    (hsmul : ∀ {a : ℝ}, 0 ≤ a → ∀ {x}, x ∈ C → a • x ∈ C)
    (hnonneg : ∀ x ∈ C, 0 ≤ n x)
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < n x)
    {x : E} (hxext : x ∈ (normalizedSlice C n).extremePoints ℝ) :
    SpansExtremeRay C x := by
  have hxK := extremePoints_subset hxext
  refine ⟨hxK.1, ?_, ?_⟩
  · intro hx0
    subst x
    change (0 : E) ∈ C ∧ n 0 = 1 at hxK
    norm_num at hxK
  · intro y hy z hz hsum
    let a : ℝ := n y
    let b : ℝ := n z
    have ha : 0 ≤ a := hnonneg y hy
    have hb : 0 ≤ b := hnonneg z hz
    have hab : a + b = 1 := by
      dsimp [a, b]
      rw [← map_add, ← hsum]
      exact hxK.2
    by_cases hy0 : y = 0
    · subst y
      simp only [zero_add] at hsum
      subst z
      exact ⟨0, 1, by norm_num, by norm_num, by simp, by simp⟩
    by_cases hz0 : z = 0
    · subst z
      simp only [add_zero] at hsum
      subst y
      exact ⟨1, 0, by norm_num, by norm_num, by simp, by simp⟩
    have ha' : 0 < a := hstrict y hy hy0
    have hb' : 0 < b := hstrict z hz hz0
    let y' : E := a⁻¹ • y
    let z' : E := b⁻¹ • z
    have hyK : y' ∈ normalizedSlice C n := by
      refine ⟨hsmul (inv_nonneg.mpr ha) hy, ?_⟩
      simp [y', a, ne_of_gt ha']
    have hzK : z' ∈ normalizedSlice C n := by
      refine ⟨hsmul (inv_nonneg.mpr hb) hz, ?_⟩
      simp [z', b, ne_of_gt hb']
    have hseg : x ∈ segment ℝ y' z' := by
      refine ⟨a, b, ha, hb, hab, ?_⟩
      dsimp [y', z']
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt ha'), one_smul,
        smul_smul, mul_inv_cancel₀ (ne_of_gt hb'), one_smul]
      exact hsum.symm
    have hext := (mem_extremePoints_iff_forall_segment.mp hxext).2 y' hyK z' hzK hseg
    rcases hext with hyx | hzx
    · refine ⟨a, b, ha, hb, ?_, ?_⟩
      · have : y = a • y' := by simp [y', ne_of_gt ha']
        rw [this, hyx]
      · have hyEq : y = a • x := by
          have : y = a • y' := by simp [y', ne_of_gt ha']
          rw [this, hyx]
        have haxz : a • x + z = x := by rw [← hyEq]; exact hsum.symm
        have hbcoef : b = 1 - a := by linarith
        calc
          z = x - a • x := eq_sub_of_add_eq (by simpa [add_comm] using haxz)
          _ = (1 - a) • x := by rw [sub_smul, one_smul]
          _ = b • x := by rw [hbcoef]
    · refine ⟨a, b, ha, hb, ?_, ?_⟩
      · have hzEq : z = b • x := by
          have : z = b • z' := by simp [z', ne_of_gt hb']
          rw [this, hzx]
        have hybx : y + b • x = x := by rw [← hzEq]; exact hsum.symm
        have hacoef : a = 1 - b := by linarith
        calc
          y = x - b • x := eq_sub_of_add_eq hybx
          _ = (1 - b) • x := by rw [sub_smul, one_smul]
          _ = a • x := by rw [hacoef]
      · have : z = b • z' := by simp [z', ne_of_gt hb']
        rw [this, hzx]

/-- Conversely, a generator of an extreme ray which lies in a normalized slice
is an extreme point of that slice. -/
theorem spansExtremeRay_extremePoint_normalizedSlice
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (C : Set E) (n : E →ₗ[ℝ] ℝ)
    (hsmul : ∀ {a : ℝ}, 0 ≤ a → ∀ {x}, x ∈ C → a • x ∈ C)
    {x : E} (hxK : x ∈ normalizedSlice C n)
    (hxray : SpansExtremeRay C x) :
    x ∈ (normalizedSlice C n).extremePoints ℝ := by
  apply mem_extremePoints_iff_forall_segment.mpr
  refine ⟨hxK, ?_⟩
  intro y hy z hz hseg
  rcases hseg with ⟨a, b, ha, hb, hab, hsum⟩
  obtain ⟨c, d, hc, hd, hay, hbz⟩ :=
    hxray.2.2 (a • y) (hsmul ha hy.1) (b • z) (hsmul hb hz.1) hsum.symm
  by_cases ha0 : a = 0
  · right
    have hb1 : b = 1 := by linarith
    simpa [ha0, hb1] using hsum
  by_cases hb0 : b = 0
  · left
    have ha1 : a = 1 := by linarith
    simpa [ha1, hb0] using hsum
  have hac : a = c := by
    have := congrArg n hay
    simp only [map_smul, hy.2, hxK.2, smul_eq_mul, mul_one] at this
    exact this
  have hbd : b = d := by
    have := congrArg n hbz
    simp only [map_smul, hz.2, hxK.2, smul_eq_mul, mul_one] at this
    exact this
  left
  calc
    y = a⁻¹ • (a • y) := by simp [ha0]
    _ = a⁻¹ • (c • x) := by rw [hay]
    _ = x := by simp [← hac, ha0]

theorem exists_extremePoint_isMinOn
    {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [T2Space E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
    {s : Set E} (hs : IsCompact s) (hs0 : s.Nonempty)
    (f : E →L[ℝ] ℝ) :
    ∃ x ∈ s.extremePoints ℝ, IsMinOn f s x := by
  obtain ⟨z, hz, hzmin⟩ := hs.exists_isMinOn hs0 f.continuous.continuousOn
  let t : Set E := (-f).toExposed s
  have hzt : z ∈ t := by
    refine ⟨hz, ?_⟩
    intro y hy
    simp only [neg_apply, neg_le_neg_iff]
    exact hzmin hy
  have htcompact : IsCompact t := ContinuousLinearMap.toExposed.isExposed.isCompact hs
  obtain ⟨x, hx⟩ := htcompact.extremePoints_nonempty ⟨z, hzt⟩
  have hxext :=
    ContinuousLinearMap.toExposed.isExposed.isExtreme.extremePoints_subset_extremePoints hx
  refine ⟨x, hxext, ?_⟩
  intro y hy
  have hxt := extremePoints_subset hx
  exact neg_le_neg_iff.mp (hxt.2 y hy)

end DelPezzoBlekherman
