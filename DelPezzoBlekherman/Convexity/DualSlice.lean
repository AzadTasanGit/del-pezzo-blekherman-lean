/-
Copyright (c) 2026 Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import DelPezzoBlekherman.Convexity.ExtremeSupport
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Bornology.Basic
/-!
# Compact normalized dual slices

The normalized slice of the dual cone is closed and, when the normalizing vector
is interior to the primal cone, bounded by an explicit interior-ball estimate.
Finite dimensionality then makes it compact. This is the compactness step of
Lemma 8.1.
-/


open Set Metric Bornology

namespace DelPezzoBlekherman

def dualConeSet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E) : Set (E →L[ℝ] ℝ) := {ℓ | ∀ x ∈ C, 0 ≤ ℓ x}

def normalizedDualSlice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E) (rho : E) : Set (E →L[ℝ] ℝ) :=
  {ℓ | ℓ ∈ dualConeSet C ∧ ℓ rho = 1}

theorem normalizedDualSlice_isClosed
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E) (rho : E) : IsClosed (normalizedDualSlice C rho) := by
  have hdual : IsClosed (dualConeSet C) := by
    rw [show dualConeSet C = ⋂ x, ⋂ (_ : x ∈ C), {ℓ | 0 ≤ ℓ x} by
      ext ℓ
      simp [dualConeSet]]
    apply isClosed_iInter
    intro x
    apply isClosed_iInter
    intro hx
    exact isClosed_Ici.preimage (ContinuousLinearMap.apply ℝ ℝ x).continuous
  have heq : IsClosed {ℓ : E →L[ℝ] ℝ | ℓ rho = 1} :=
    isClosed_singleton.preimage (ContinuousLinearMap.apply ℝ ℝ rho).continuous
  exact hdual.inter heq

theorem normalizedDualSlice_isBounded_of_mem_interior
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E) (rho : E) (hrho : rho ∈ interior C) :
    IsBounded (normalizedDualSlice C rho) := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior rho hrho
  let t : ℝ := r / 2
  have ht : 0 < t := by dsimp [t]; linarith
  apply (Metric.isBounded_closedBall (x := (0 : E →L[ℝ] ℝ)) (r := t⁻¹)).subset
  intro ℓ hℓ
  rw [mem_closedBall_zero_iff]
  apply ℓ.opNorm_le_bound (le_of_lt (inv_pos.mpr ht))
  intro x
  by_cases hx : x = 0
  · subst x
    simp
  let u : E := ‖x‖⁻¹ • x
  have hu : ‖u‖ = 1 := by simp [u, norm_smul, hx]
  have hplusC : rho + t • u ∈ C := by
    apply interior_subset
    apply hball
    rw [mem_ball, dist_eq_norm]
    simp [hu, norm_smul, abs_of_pos ht]
    dsimp [t]
    linarith
  have hminusC : rho - t • u ∈ C := by
    apply interior_subset
    apply hball
    rw [mem_ball, dist_eq_norm]
    simp [hu, norm_smul, abs_of_pos ht]
    dsimp [t]
    linarith
  have hp := hℓ.1 _ hplusC
  have hm := hℓ.1 _ hminusC
  have hn : ℓ rho = 1 := hℓ.2
  simp only [map_add, map_sub, map_smul, hn] at hp hm
  change 0 ≤ 1 + t * ℓ u at hp
  change 0 ≤ 1 - t * ℓ u at hm
  have huabs : |ℓ u| ≤ t⁻¹ := by
    rw [abs_le, inv_eq_one_div]
    constructor
    · rw [show -(1 / t) = (-1) / t by ring, div_le_iff₀ ht]
      nlinarith
    · rw [le_div_iff₀ ht]
      nlinarith
  have hxu : x = ‖x‖ • u := by simp [u, hx]
  calc
    ‖ℓ x‖ = ‖ℓ (‖x‖ • u)‖ := congrArg (fun z ↦ ‖ℓ z‖) hxu
    _ = ‖x‖ * |ℓ u| := by simp [Real.norm_eq_abs]
    _ ≤ ‖x‖ * t⁻¹ := mul_le_mul_of_nonneg_left huabs (norm_nonneg x)
    _ = t⁻¹ * ‖x‖ := mul_comm _ _

theorem normalizedDualSlice_isCompact_of_mem_interior
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (C : Set E) (rho : E) (hrho : rho ∈ interior C) :
    IsCompact (normalizedDualSlice C rho) := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  exact ⟨normalizedDualSlice_isClosed C rho,
    normalizedDualSlice_isBounded_of_mem_interior C rho hrho⟩

/-- Every nonzero dual-cone functional is strictly positive at an interior point
of the primal cone. -/
theorem dualCone_apply_pos_of_mem_interior
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E) (rho : E) (hrho : rho ∈ interior C)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ∈ dualConeSet C) (hℓ0 : ℓ ≠ 0) :
    0 < ℓ rho := by
  have hnonneg : 0 ≤ ℓ rho := hℓ rho (interior_subset hrho)
  apply lt_of_le_of_ne hnonneg
  intro hrho0
  apply hℓ0
  ext x
  by_cases hx : x = 0
  · subst x
    simp
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior rho hrho
  let s : ℝ := r / (2 * ‖x‖)
  have hs : 0 < s := div_pos hr (mul_pos two_pos (norm_pos_iff.mpr hx))
  have hsx : ‖s • x‖ < r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs]
    dsimp [s]
    have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
    field_simp [ne_of_gt hxnorm]
    nlinarith
  have hplus : rho + s • x ∈ C := by
    apply interior_subset
    apply hball
    rw [mem_ball, dist_eq_norm]
    simpa using hsx
  have hminus : rho - s • x ∈ C := by
    apply interior_subset
    apply hball
    rw [mem_ball, dist_eq_norm]
    simpa [norm_neg] using hsx
  have hp := hℓ _ hplus
  have hm := hℓ _ hminus
  simp only [map_add, map_sub, map_smul, smul_eq_mul] at hp hm
  rw [← hrho0] at hp hm
  change 0 ≤ 0 + s * ℓ x at hp
  change 0 ≤ 0 - s * ℓ x at hm
  have : ℓ x = 0 := by nlinarith
  simpa using this

/-- A nonzero dual functional can be uniquely normalized into the slice by
scaling with the inverse of its positive value at the interior point. -/
theorem normalizedDualSlice_nonempty_of_nonzero_dual
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E) (rho : E) (hrho : rho ∈ interior C)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ∈ dualConeSet C) (hℓ0 : ℓ ≠ 0) :
    normalizedDualSlice C rho |>.Nonempty := by
  have hp := dualCone_apply_pos_of_mem_interior C rho hrho ℓ hℓ hℓ0
  refine ⟨(ℓ rho)⁻¹ • ℓ, ?_, ?_⟩
  · intro x hx
    simp only [smul_apply, smul_eq_mul]
    exact mul_nonneg (le_of_lt (inv_pos.mpr hp)) (hℓ x hx)
  · simp [ne_of_gt hp]

/-- On the slice normalized at an interior point, generators of extreme dual
rays are exactly the extreme points. -/
theorem spansExtremeRay_dual_iff_extremePoint_normalizedDualSlice
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E) (rho : E) (hrho : rho ∈ interior C)
    {ℓ : E →L[ℝ] ℝ} (hℓK : ℓ ∈ normalizedDualSlice C rho) :
    SpansExtremeRay (dualConeSet C) ℓ ↔
      ℓ ∈ (normalizedDualSlice C rho).extremePoints ℝ := by
  let n : (E →L[ℝ] ℝ) →ₗ[ℝ] ℝ :=
    (ContinuousLinearMap.apply ℝ ℝ rho).toLinearMap
  have hslice : normalizedDualSlice C rho = normalizedSlice (dualConeSet C) n := by
    ext x
    simp [normalizedDualSlice, normalizedSlice, n]
  have hdual_smul :
      ∀ {a : ℝ}, 0 ≤ a → ∀ {x : E →L[ℝ] ℝ}, x ∈ dualConeSet C →
        a • x ∈ dualConeSet C := by
    intro a ha x hx y hy
    simp only [smul_apply, smul_eq_mul]
    exact mul_nonneg ha (hx y hy)
  constructor
  · intro hℓray
    rw [hslice] at hℓK ⊢
    exact spansExtremeRay_extremePoint_normalizedSlice
      (dualConeSet C) n hdual_smul hℓK hℓray
  · intro hℓext
    have hdual_nonneg : ∀ x ∈ dualConeSet C, 0 ≤ n x := by
      intro x hx
      exact hx rho (interior_subset hrho)
    have hdual_strict : ∀ x ∈ dualConeSet C, x ≠ 0 → 0 < n x := by
      intro x hx hx0
      exact dualCone_apply_pos_of_mem_interior C rho hrho x hx hx0
    rw [hslice] at hℓext
    exact extremePoint_normalizedSlice_spansExtremeRay
      (dualConeSet C) n hdual_smul hdual_nonneg hdual_strict hℓext

/-- Strong separation of a point outside a closed convex cone, oriented as a
nonzero dual-cone functional which is negative on that point. -/
theorem exists_dual_neg_of_not_mem_closed_convex_cone
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E) (hCconv : Convex ℝ C) (hCclosed : IsClosed C)
    (hzero : (0 : E) ∈ C)
    (hsmul : ∀ {a : ℝ}, 0 ≤ a → ∀ {x}, x ∈ C → a • x ∈ C)
    {v : E} (hv : v ∉ C) :
    ∃ ℓ : E →L[ℝ] ℝ, ℓ ∈ dualConeSet C ∧ ℓ ≠ 0 ∧ ℓ v < 0 := by
  obtain ⟨f, u, hfu, huv⟩ := geometric_hahn_banach_closed_point hCconv hCclosed hv
  have hu0 : 0 < u := by simpa using hfu 0 hzero
  have hfv : 0 < f v := hu0.trans huv
  let ℓ : E →L[ℝ] ℝ := -f
  have hℓdual : ℓ ∈ dualConeSet C := by
    intro x hx
    change 0 ≤ -(f x)
    by_contra hfx
    push Not at hfx
    have hfxpos : 0 < f x := by linarith
    let a : ℝ := (|u| + 1) / f x
    have ha : 0 ≤ a := le_of_lt (div_pos (by positivity) hfxpos)
    have hax := hfu (a • x) (hsmul ha hx)
    rw [map_smul] at hax
    change a * f x < u at hax
    have hfx0 : f x ≠ 0 := ne_of_gt hfxpos
    dsimp [a] at hax
    field_simp [hfx0] at hax
    linarith [le_abs_self u]
  have hℓ0 : ℓ ≠ 0 := by
    intro hzeroℓ
    have hvzero := congrArg (fun g : E →L[ℝ] ℝ => g v) hzeroℓ
    simp [ℓ] at hvzero
    linarith
  refine ⟨ℓ, hℓdual, hℓ0, ?_⟩
  change -(f v) < 0
  exact neg_lt_zero.mpr hfv

/-- A point outside a closed convex cone is strictly separated by a functional
spanning an extreme ray of the dual cone.  The extreme functional is selected
by minimizing evaluation on the compact slice normalized at an interior
point. -/
theorem exists_extreme_dual_neg_of_not_mem_closed_convex_cone
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (C : Set E) (hCconv : Convex ℝ C) (hCclosed : IsClosed C)
    (hzero : (0 : E) ∈ C)
    (hsmul : ∀ {a : ℝ}, 0 ≤ a → ∀ {x}, x ∈ C → a • x ∈ C)
    (rho : E) (hrho : rho ∈ interior C)
    {v : E} (hv : v ∉ C) :
    ∃ ℓ : E →L[ℝ] ℝ, SpansExtremeRay (dualConeSet C) ℓ ∧ ℓ v < 0 := by
  obtain ⟨s, hsdual, hs0, hsv⟩ :=
    exists_dual_neg_of_not_mem_closed_convex_cone C hCconv hCclosed hzero hsmul hv
  have hspos := dualCone_apply_pos_of_mem_interior C rho hrho s hsdual hs0
  let s' : E →L[ℝ] ℝ := (s rho)⁻¹ • s
  have hs'K : s' ∈ normalizedDualSlice C rho := by
    refine ⟨?_, ?_⟩
    · intro x hx
      simp only [s', smul_apply, smul_eq_mul]
      exact mul_nonneg (le_of_lt (inv_pos.mpr hspos)) (hsdual x hx)
    · simp [s', ne_of_gt hspos]
  have hs'v : s' v < 0 := by
    simp only [s', smul_apply, smul_eq_mul]
    exact mul_neg_of_pos_of_neg (inv_pos.mpr hspos) hsv
  have hcompact := normalizedDualSlice_isCompact_of_mem_interior C rho hrho
  have hnonempty : (normalizedDualSlice C rho).Nonempty := ⟨s', hs'K⟩
  let ev : (E →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ v
  obtain ⟨ℓ, hℓext, hℓmin⟩ := exists_extremePoint_isMinOn hcompact hnonempty ev
  have hℓv : ℓ v < 0 := by
    have := hℓmin hs'K
    change ℓ v ≤ s' v at this
    exact this.trans_lt hs'v
  let n : (E →L[ℝ] ℝ) →ₗ[ℝ] ℝ :=
    (ContinuousLinearMap.apply ℝ ℝ rho).toLinearMap
  have hℓext' : ℓ ∈ (normalizedSlice (dualConeSet C) n).extremePoints ℝ := by
    simpa [normalizedDualSlice, normalizedSlice, n] using hℓext
  have hdual_smul :
      ∀ {a : ℝ}, 0 ≤ a → ∀ {x : E →L[ℝ] ℝ}, x ∈ dualConeSet C →
        a • x ∈ dualConeSet C := by
    intro a ha x hx y hy
    simp only [smul_apply, smul_eq_mul]
    exact mul_nonneg ha (hx y hy)
  have hdual_nonneg : ∀ x ∈ dualConeSet C, 0 ≤ n x := by
    intro x hx
    exact hx rho (interior_subset hrho)
  have hdual_strict : ∀ x ∈ dualConeSet C, x ≠ 0 → 0 < n x := by
    intro x hx hx0
    exact dualCone_apply_pos_of_mem_interior C rho hrho x hx hx0
  refine ⟨ℓ, ?_, hℓv⟩
  exact extremePoint_normalizedSlice_spansExtremeRay
    (dualConeSet C) n hdual_smul hdual_nonneg hdual_strict hℓext'

/-- A boundary point of a closed convex cone has a nonzero supporting
dual-cone functional which vanishes there. -/
theorem exists_dual_eq_zero_of_mem_frontier_closed_convex_cone
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E) (hCconv : Convex ℝ C) (hCclosed : IsClosed C)
    (hzero : (0 : E) ∈ C)
    (hsmul : ∀ {a : ℝ}, 0 ≤ a → ∀ {x}, x ∈ C → a • x ∈ C)
    (rho : E) (hrho : rho ∈ interior C)
    {v : E} (hv : v ∈ frontier C) :
    ∃ ℓ : E →L[ℝ] ℝ, ℓ ∈ dualConeSet C ∧ ℓ ≠ 0 ∧ ℓ v = 0 := by
  have hv_not_int : v ∉ interior C := by
    change v ∈ closure C \ interior C at hv
    exact hv.2
  obtain ⟨f, hf⟩ :=
    geometric_hahn_banach_open_point (hCconv.interior) isOpen_interior hv_not_int
  have hinter_nonempty : (interior C).Nonempty := ⟨rho, hrho⟩
  have hclosure_int : closure (interior C) = C := by
    rw [hCconv.closure_interior_eq_closure_of_nonempty_interior hinter_nonempty,
      hCclosed.closure_eq]
  have hinter_half : interior C ⊆ {x | f x ≤ f v} := by
    intro x hx
    exact (hf x hx).le
  have hhalf_closed : IsClosed {x | f x ≤ f v} :=
    isClosed_Iic.preimage f.continuous
  have hC_half : C ⊆ {x | f x ≤ f v} := by
    rw [← hclosure_int]
    exact closure_minimal hinter_half hhalf_closed
  have hvC : v ∈ C := by
    have hvclosure := frontier_subset_closure hv
    rw [hCclosed.closure_eq] at hvclosure
    exact hvclosure
  have hfv_nonneg : 0 ≤ f v := by
    simpa using hC_half hzero
  have htwo_v := hC_half (hsmul (show (0 : ℝ) ≤ 2 by norm_num) hvC)
  have hfv_zero : f v = 0 := by
    change f (2 • v) ≤ f v at htwo_v
    simp only [map_smul, smul_eq_mul] at htwo_v
    linarith
  let ℓ : E →L[ℝ] ℝ := -f
  have hℓdual : ℓ ∈ dualConeSet C := by
    intro x hx
    change 0 ≤ -(f x)
    have := hC_half hx
    rw [hfv_zero] at this
    change f x ≤ 0 at this
    linarith
  have hf0 : f ≠ 0 := by
    intro hfzero
    have hr := hf rho hrho
    rw [hfzero] at hr
    simp at hr
  have hℓ0 : ℓ ≠ 0 := by
    intro hℓzero
    apply hf0
    simpa [ℓ] using congrArg Neg.neg hℓzero
  refine ⟨ℓ, hℓdual, hℓ0, ?_⟩
  simp [ℓ, hfv_zero]

/-- A boundary point of a closed convex cone is supported by a functional
spanning an extreme ray of the dual cone. -/
theorem exists_extreme_dual_eq_zero_of_mem_frontier_closed_convex_cone
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (C : Set E) (hCconv : Convex ℝ C) (hCclosed : IsClosed C)
    (hzero : (0 : E) ∈ C)
    (hsmul : ∀ {a : ℝ}, 0 ≤ a → ∀ {x}, x ∈ C → a • x ∈ C)
    (rho : E) (hrho : rho ∈ interior C)
    {v : E} (hv : v ∈ frontier C) :
    ∃ ℓ : E →L[ℝ] ℝ, SpansExtremeRay (dualConeSet C) ℓ ∧ ℓ v = 0 := by
  obtain ⟨s, hsdual, hs0, hsv⟩ :=
    exists_dual_eq_zero_of_mem_frontier_closed_convex_cone
      C hCconv hCclosed hzero hsmul rho hrho hv
  have hspos := dualCone_apply_pos_of_mem_interior C rho hrho s hsdual hs0
  let s' : E →L[ℝ] ℝ := (s rho)⁻¹ • s
  have hs'K : s' ∈ normalizedDualSlice C rho := by
    refine ⟨?_, ?_⟩
    · intro x hx
      simp only [s', smul_apply, smul_eq_mul]
      exact mul_nonneg (le_of_lt (inv_pos.mpr hspos)) (hsdual x hx)
    · simp [s', ne_of_gt hspos]
  have hs'v : s' v = 0 := by simp [s', hsv]
  have hcompact := normalizedDualSlice_isCompact_of_mem_interior C rho hrho
  have hnonempty : (normalizedDualSlice C rho).Nonempty := ⟨s', hs'K⟩
  let ev : (E →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ v
  obtain ⟨ℓ, hℓext, hℓmin⟩ := exists_extremePoint_isMinOn hcompact hnonempty ev
  have hvC : v ∈ C := by
    have hvclosure := frontier_subset_closure hv
    rw [hCclosed.closure_eq] at hvclosure
    exact hvclosure
  have hℓK := extremePoints_subset hℓext
  have hℓv_nonneg : 0 ≤ ℓ v := hℓK.1 v hvC
  have hℓv_le : ℓ v ≤ 0 := by
    have hmin := hℓmin hs'K
    change ℓ v ≤ s' v at hmin
    rwa [hs'v] at hmin
  have hℓv : ℓ v = 0 := le_antisymm hℓv_le hℓv_nonneg
  let n : (E →L[ℝ] ℝ) →ₗ[ℝ] ℝ :=
    (ContinuousLinearMap.apply ℝ ℝ rho).toLinearMap
  have hℓext' : ℓ ∈ (normalizedSlice (dualConeSet C) n).extremePoints ℝ := by
    simpa [normalizedDualSlice, normalizedSlice, n] using hℓext
  have hdual_smul :
      ∀ {a : ℝ}, 0 ≤ a → ∀ {x : E →L[ℝ] ℝ}, x ∈ dualConeSet C →
        a • x ∈ dualConeSet C := by
    intro a ha x hx y hy
    simp only [smul_apply, smul_eq_mul]
    exact mul_nonneg ha (hx y hy)
  have hdual_nonneg : ∀ x ∈ dualConeSet C, 0 ≤ n x := by
    intro x hx
    exact hx rho (interior_subset hrho)
  have hdual_strict : ∀ x ∈ dualConeSet C, x ≠ 0 → 0 < n x := by
    intro x hx hx0
    exact dualCone_apply_pos_of_mem_interior C rho hrho x hx hx0
  refine ⟨ℓ, ?_, hℓv⟩
  exact extremePoint_normalizedSlice_spansExtremeRay
    (dualConeSet C) n hdual_smul hdual_nonneg hdual_strict hℓext'

end DelPezzoBlekherman
