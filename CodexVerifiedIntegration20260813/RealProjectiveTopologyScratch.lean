import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.GroupTheory.GroupAction.SubMulAction

noncomputable section

open Set Metric

namespace RealProjectiveTopology

variable (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The unit sphere, regarded as stable under the two integer units `±1`. -/
def unitSphereAction : SubMulAction ℤˣ V where
  carrier := sphere (0 : V) 1
  smul_mem' g x hx := by
    rcases Int.units_eq_one_or g with rfl | rfl
    · simpa using hx
    · simpa using hx

/-- Real projective directions, modeled as the compact unit sphere modulo the antipodal action. -/
abbrev Direction := Quotient (MulAction.orbitRel ℤˣ (unitSphereAction V))

instance [FiniteDimensional ℝ V] : CompactSpace (unitSphereAction V) :=
  inferInstanceAs (CompactSpace (sphere (0 : V) 1))

instance : T2Space (unitSphereAction V) := inferInstance

instance [FiniteDimensional ℝ V] : LocallyCompactSpace (unitSphereAction V) := inferInstance

instance : ContinuousConstSMul ℤˣ (unitSphereAction V) := inferInstance

instance : ProperlyDiscontinuousSMul ℤˣ (unitSphereAction V) := inferInstance

instance [FiniteDimensional ℝ V] : CompactSpace (Direction V) := Quotient.compactSpace

instance [FiniteDimensional ℝ V] : T2Space (Direction V) := inferInstance

/-- Normalize a nonzero vector to the unit sphere. -/
def normalize (v : {v : V // v ≠ 0}) : unitSphereAction V :=
  ⟨‖(v : V)‖⁻¹ • (v : V), by
    change dist (‖(v : V)‖⁻¹ • (v : V)) 0 = 1
    rw [dist_zero_right, norm_smul]
    simp [norm_ne_zero_iff.mpr v.2]⟩

/-- Send a nonzero vector to its normalized antipodal direction. -/
def directionOf (v : {v : V // v ≠ 0}) : Direction V :=
  Quotient.mk (MulAction.orbitRel ℤˣ (unitSphereAction V)) (normalize V v)

theorem continuous_normalize : Continuous (normalize V) := by
  apply Continuous.subtype_mk
  exact ((continuous_norm.comp continuous_subtype_val).inv₀
    (fun v ↦ norm_ne_zero_iff.mpr v.2)).smul continuous_subtype_val

theorem continuous_directionOf : Continuous (directionOf V) :=
  continuous_quot_mk.comp (continuous_normalize V)

theorem normalize_surjective : Function.Surjective (normalize V) := by
  intro x
  have hxnorm : ‖(x : V)‖ = 1 := by
    have hxmem := x.2
    change dist (x : V) 0 = 1 at hxmem
    simpa [dist_zero_right] using hxmem
  have hxzero : (x : V) ≠ 0 := by
    intro hx
    rw [hx, norm_zero] at hxnorm
    norm_num at hxnorm
  refine ⟨⟨x, hxzero⟩, ?_⟩
  apply Subtype.ext
  change ‖(x : V)‖⁻¹ • (x : V) = x
  rw [hxnorm]
  simp

theorem directionOf_surjective : Function.Surjective (directionOf V) := by
  intro y
  obtain ⟨x, rfl⟩ := Quotient.exists_rep y
  obtain ⟨v, hv⟩ := normalize_surjective V x
  exact ⟨v, congr_arg (Quotient.mk (MulAction.orbitRel ℤˣ (unitSphereAction V))) hv⟩

/-- The projective directions represented by a Euclidean-dense set of vectors are dense. -/
theorem dense_image_directionOf_of_dense {S : Set V} (hS : Dense S) :
    Dense (directionOf V '' {v : {v : V // v ≠ 0} | (v : V) ∈ S}) := by
  have hpunctured : Dense {v : {v : V // v ≠ 0} | (v : V) ∈ S} :=
    hS.preimage (isOpen_ne.isOpenMap_subtype_val)
  exact (directionOf_surjective V).denseRange.dense_image
    (continuous_directionOf V) hpunctured

variable {V} {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- A continuous linear coordinate equivalence transports a dense vector locus to a dense locus
of projective directions in the target. -/
theorem dense_image_directionOf_continuousLinearEquiv
    (e : V ≃L[ℝ] W) {S : Set V} (hS : Dense S) :
    Dense (directionOf W ''
      {w : {w : W // w ≠ 0} | (w : W) ∈ e '' S}) := by
  have himage : Dense (e '' S) :=
    e.surjective.denseRange.dense_image e.continuous hS
  exact dense_image_directionOf_of_dense W himage

/-- A finite basis supplies the continuous linear coordinate equivalence used to transport
projective density. -/
def basisContinuousLinearEquiv
    {I : Type*} [Finite I] [FiniteDimensional ℝ W] (b : Module.Basis I ℝ W) :
    (I → ℝ) ≃L[ℝ] W :=
  b.equivFun.symm.toContinuousLinearEquiv

/-- Equality of real projective directions is exactly equality after one of the two antipodal
unit actions. -/
theorem directionOf_eq_iff (v w : {v : V // v ≠ 0}) :
    directionOf V v = directionOf V w ↔
      ∃ g : ℤˣ, g • normalize V w = normalize V v := by
  rw [directionOf, directionOf, Quotient.eq_iff_equiv]
  change (MulAction.orbitRel ℤˣ (unitSphereAction V)) (normalize V v) (normalize V w) ↔ _
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]

/-- Equality in the compact antipodal model agrees with the usual nonzero-scalar relation. -/
theorem directionOf_eq_iff_exists_smul (v w : {v : V // v ≠ 0}) :
    directionOf V v = directionOf V w ↔
      ∃ a : ℝ, a ≠ 0 ∧ (v : V) = a • (w : V) := by
  constructor
  · rw [directionOf_eq_iff]
    rintro ⟨g, hg⟩
    have hvnorm : ‖(v : V)‖ ≠ 0 := norm_ne_zero_iff.mpr v.2
    have hwnorm : ‖(w : V)‖ ≠ 0 := norm_ne_zero_iff.mpr w.2
    rcases Int.units_eq_one_or g with rfl | rfl
    · have h : ‖(w : V)‖⁻¹ • (w : V) = ‖(v : V)‖⁻¹ • (v : V) := by
        simpa [normalize, SubMulAction.val_smul, Units.smul_def] using
          congr_arg Subtype.val hg
      refine ⟨‖(v : V)‖ * ‖(w : V)‖⁻¹, mul_ne_zero hvnorm (inv_ne_zero hwnorm), ?_⟩
      calc
        (v : V) = ‖(v : V)‖ • (‖(v : V)‖⁻¹ • (v : V)) := by
          rw [smul_smul, mul_inv_cancel₀ hvnorm, one_smul]
        _ = ‖(v : V)‖ • (‖(w : V)‖⁻¹ • (w : V)) := congr_arg _ h.symm
        _ = (‖(v : V)‖ * ‖(w : V)‖⁻¹) • (w : V) := by rw [smul_smul]
    · have h : - (‖(w : V)‖⁻¹ • (w : V)) = ‖(v : V)‖⁻¹ • (v : V) := by
        simpa [normalize, SubMulAction.val_smul, Units.smul_def] using
          congr_arg Subtype.val hg
      refine ⟨-(‖(v : V)‖ * ‖(w : V)‖⁻¹),
        neg_ne_zero.mpr (mul_ne_zero hvnorm (inv_ne_zero hwnorm)), ?_⟩
      calc
        (v : V) = ‖(v : V)‖ • (‖(v : V)‖⁻¹ • (v : V)) := by
          rw [smul_smul, mul_inv_cancel₀ hvnorm, one_smul]
        _ = ‖(v : V)‖ • (-(‖(w : V)‖⁻¹ • (w : V))) := congr_arg _ h.symm
        _ = -(‖(v : V)‖ * ‖(w : V)‖⁻¹) • (w : V) := by
          rw [smul_neg, smul_smul, neg_smul]
  · rintro ⟨a, ha, hva⟩
    rw [directionOf_eq_iff]
    rcases lt_or_gt_of_ne ha with haNeg | haPos
    · refine ⟨(-1 : ℤˣ), ?_⟩
      apply Subtype.ext
      simp only [SubMulAction.val_smul]
      simp only [Units.smul_def, Units.val_neg, Units.val_one, neg_smul, one_smul]
      change - (‖(w : V)‖⁻¹ • (w : V)) = ‖(v : V)‖⁻¹ • (v : V)
      rw [hva, norm_smul, Real.norm_eq_abs, abs_of_neg haNeg, smul_smul]
      have hcoeff : (-(a) * ‖(w : V)‖)⁻¹ * a = -‖(w : V)‖⁻¹ := by
        field_simp
      rw [hcoeff, neg_smul]
    · refine ⟨(1 : ℤˣ), ?_⟩
      apply Subtype.ext
      simp only [SubMulAction.val_smul]
      simp only [one_smul]
      change ‖(w : V)‖⁻¹ • (w : V) = ‖(v : V)‖⁻¹ • (v : V)
      rw [hva, norm_smul, Real.norm_eq_abs, abs_of_pos haPos, smul_smul]
      have hcoeff : (a * ‖(w : V)‖)⁻¹ * a = ‖(w : V)‖⁻¹ := by
        field_simp
      rw [hcoeff]

end RealProjectiveTopology
