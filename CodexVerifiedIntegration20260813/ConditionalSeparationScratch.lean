import ExtremeRayBaseScratch

noncomputable section

universe u v

open Set

namespace ConditionalSeparation

variable {Q : Type u} [AddCommGroup Q] [Module ℝ Q] [TopologicalSpace Q]
  [T2Space Q] [IsTopologicalAddGroup Q] [ContinuousSMul ℝ Q] [LocallyConvexSpace ℝ Q]
variable {D : Type v} [AddCommGroup D] [Module ℝ D] [TopologicalSpace D]
  [T2Space D] [IsTopologicalAddGroup D] [ContinuousSMul ℝ D] [LocallyConvexSpace ℝ D]

/-- Abstract but fully checked separation theorem.  Its inputs isolate the exact finite-dimensional
dual representation and compact-base facts needed to turn Farkas separation into an extreme
Hankel separator. -/
theorem exists_normalized_extreme_separator
    (Sigma : ProperCone ℝ Q) (Dcone : ConvexCone ℝ D)
    (repr : D ≃ₗ[ℝ] StrongDual ℝ Q)
    (hdual : ∀ d : D, d ∈ Dcone ↔ ∀ q ∈ Sigma, 0 ≤ repr d q)
    (tau : D →ₗ[ℝ] ℝ)
    (htau : ∀ d ∈ Dcone, d ≠ 0 → 0 < tau d)
    (hcompact : IsCompact {d : D | d ∈ Dcone ∧ tau d = 1})
    (p : Q) (hp : p ∉ Sigma)
    (evalP : StrongDual ℝ D) (hevalP : ∀ d, evalP d = repr d p) :
    ∃ d : D, ExtremeRayBase.IsExtremeRay Dcone d ∧ tau d = 1 ∧
      (∀ q ∈ Sigma, 0 ≤ repr d q) ∧ repr d p < 0 := by
  obtain ⟨f, hfSigma, hfp⟩ := ExtremeSeparator.properCone_separates Sigma hp
  let d₀ : D := repr.symm f
  have hrepr : repr d₀ = f := repr.apply_symm_apply f
  have hd₀cone : d₀ ∈ Dcone := by
    apply (hdual d₀).mpr
    intro q hq
    rw [hrepr]
    exact hfSigma q hq
  have hd₀0 : d₀ ≠ 0 := by
    intro hd₀
    have hf0 : f = 0 := by
      rw [← hrepr, hd₀]
      simp
    rw [hf0] at hfp
    simp at hfp
  have htaupos : 0 < tau d₀ := htau d₀ hd₀cone hd₀0
  let b : D := (tau d₀)⁻¹ • d₀
  have hbcone : b ∈ Dcone := Dcone.smul_mem (inv_pos.mpr htaupos) hd₀cone
  have hbtau : tau b = 1 := by
    simp [b, htaupos.ne']
  have hevalneg : evalP b < 0 := by
    rw [hevalP]
    change repr ((tau d₀)⁻¹ • d₀) p < 0
    rw [LinearEquiv.map_smul, hrepr]
    simp only [smul_apply, smul_eq_mul]
    exact mul_neg_of_pos_of_neg (inv_pos.mpr htaupos) hfp
  obtain ⟨d, hdRay, hdtau, hdeval⟩ :=
    ExtremeRayBase.exists_extremeRay_apply_neg_of_compact_base
      Dcone tau htau hcompact evalP hbcone hbtau hevalneg
  have hddual : ∀ q ∈ Sigma, 0 ≤ repr d q :=
    (hdual d).mp hdRay.1
  have hdp : repr d p < 0 := by
    rw [← hevalP]
    exact hdeval
  exact ⟨d, hdRay, hdtau, hddual, hdp⟩

/-- Logical last step of the Del Pezzo--Blekherman separation argument: an extreme separator of a
nonnegative target cannot be a positive point evaluation, so the dichotomy places it in the
basepoint-free branch. -/
theorem exists_basepointFree_extreme_separator
    (Sigma : ProperCone ℝ Q) (Dcone : ConvexCone ℝ D)
    (repr : D ≃ₗ[ℝ] StrongDual ℝ Q)
    (hdual : ∀ d : D, d ∈ Dcone ↔ ∀ q ∈ Sigma, 0 ≤ repr d q)
    (tau : D →ₗ[ℝ] ℝ)
    (htau : ∀ d ∈ Dcone, d ≠ 0 → 0 < tau d)
    (hcompact : IsCompact {d : D | d ∈ Dcone ∧ tau d = 1})
    (p : Q) (hp : p ∉ Sigma)
    (evalP : StrongDual ℝ D) (hevalP : ∀ d, evalP d = repr d p)
    (IsPointEvaluation BasepointFree : D → Prop)
    (hpoint_nonneg : ∀ d, IsPointEvaluation d → 0 ≤ repr d p)
    (hdichotomy : ∀ d, ExtremeRayBase.IsExtremeRay Dcone d →
      IsPointEvaluation d ∨ BasepointFree d) :
    ∃ d : D, ExtremeRayBase.IsExtremeRay Dcone d ∧ BasepointFree d ∧
      (∀ q ∈ Sigma, 0 ≤ repr d q) ∧ repr d p < 0 := by
  obtain ⟨d, hdRay, hdtau, hddual, hdp⟩ :=
    exists_normalized_extreme_separator Sigma Dcone repr hdual tau htau hcompact
      p hp evalP hevalP
  have hdBase : BasepointFree d := by
    rcases hdichotomy d hdRay with hdPoint | hdBase
    · exact False.elim ((not_lt_of_ge (hpoint_nonneg d hdPoint)) hdp)
    · exact hdBase
  exact ⟨d, hdRay, hdBase, hddual, hdp⟩

end ConditionalSeparation
