import NonrealPairInertiaScratch
import Mathlib.LinearAlgebra.Matrix.ToLin

noncomputable section

universe u v

open scoped BigOperators
open Finset Matrix

namespace LinearMap

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

/-- Two linear functionals with nested kernels are scalar multiples. -/
theorem exists_smul_of_ker_le_ker (f g : Module.Dual K V)
    (h : LinearMap.ker f ≤ LinearMap.ker g) : ∃ a : K, a • f = g := by
  have hm : g ∈ Submodule.span K (Set.range (fun _ : Unit ↦ f)) :=
    mem_span_of_iInf_ker_le_ker (L := fun _ : Unit ↦ f) (K := g) (by simpa)
  rw [Set.range_const, Submodule.mem_span_singleton] at hm
  exact hm

end LinearMap

namespace ReciprocalHyperplane

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- The unique-relation functional with coefficient vector `u`. -/
def relation (u : ι → ℝ) : Module.Dual ℝ (ι → ℝ) :=
  dotProductBilin ℝ ℝ u

/-- The functional obtained by pairing `x` with `z` using diagonal coefficients `μ`. -/
def diagonalPairing (μ z : ι → ℝ) : Module.Dual ℝ (ι → ℝ) :=
  dotProductBilin ℝ ℝ (fun i ↦ μ i * z i)

@[simp]
theorem relation_apply (u x : ι → ℝ) : relation u x = ∑ i, u i * x i :=
  rfl

@[simp]
theorem diagonalPairing_apply (μ z x : ι → ℝ) :
    diagonalPairing μ z x = ∑ i, (μ i * z i) * x i :=
  rfl

/-- A nonzero radical vector for the diagonal form restricted to the relation hyperplane forces
the reciprocal coefficient identity. -/
theorem reciprocal_identity_of_radical
    (u μ z : ι → ℝ)
    (hμ : ∀ i, μ i ≠ 0) (hz : z ≠ 0)
    (hzH : relation u z = 0)
    (hrad : ∀ x, relation u x = 0 → diagonalPairing μ z x = 0) :
    ∑ i, u i ^ 2 / μ i = 0 := by
  have hker : LinearMap.ker (relation u) ≤ LinearMap.ker (diagonalPairing μ z) := by
    intro x hx
    exact LinearMap.mem_ker.mpr (hrad x (LinearMap.mem_ker.mp hx))
  obtain ⟨a, ha⟩ := LinearMap.exists_smul_of_ker_le_ker
    (relation u) (diagonalPairing μ z) hker
  have hcoord (i : ι) : μ i * z i = a * u i := by
    have hi := LinearMap.congr_fun ha (Pi.single i 1)
    simpa [relation, diagonalPairing, dotProduct, Pi.single_apply,
      mul_comm, mul_left_comm, mul_assoc] using hi.symm
  have ha0 : a ≠ 0 := by
    intro ha0
    apply hz
    funext i
    apply (mul_eq_zero.mp ?_).resolve_left (hμ i)
    simpa [ha0] using hcoord i
  have hzH' : ∑ i, u i * z i = 0 := by
    simpa only [relation_apply] using hzH
  have hzsum : a * ∑ i, u i ^ 2 / μ i = 0 := by
    rw [Finset.mul_sum]
    calc
      ∑ i, a * (u i ^ 2 / μ i) = ∑ i, u i * z i := by
        apply Finset.sum_congr rfl
        intro i _
        calc
          a * (u i ^ 2 / μ i) = (a * u i) * u i / μ i := by ring
          _ = (μ i * z i) * u i / μ i := by rw [hcoord i]
          _ = u i * z i := by field_simp [hμ i]
      _ = 0 := hzH'
  exact (mul_eq_zero.mp hzsum).resolve_left ha0

/-- Conversely, the reciprocal identity explicitly constructs a nonzero radical vector
`zᵢ = uᵢ/μᵢ` for the diagonal form on the relation hyperplane. -/
theorem radical_of_reciprocal_identity
    (u μ : ι → ℝ) (hu : u ≠ 0) (hμ : ∀ i, μ i ≠ 0)
    (hrecip : ∑ i, u i ^ 2 / μ i = 0) :
    let z := fun i ↦ u i / μ i
    z ≠ 0 ∧ relation u z = 0 ∧
      ∀ x, relation u x = 0 → diagonalPairing μ z x = 0 := by
  let z := fun i ↦ u i / μ i
  have hz : z ≠ 0 := by
    intro hz0
    apply hu
    funext i
    have : z i = 0 := congrFun hz0 i
    exact (div_eq_zero_iff.mp this).resolve_right (hμ i)
  refine ⟨hz, ?_, ?_⟩
  · simpa [z, relation_apply, pow_two, mul_div_assoc] using hrecip
  · intro x hx
    simpa [z, diagonalPairing_apply, hμ, mul_div_cancel₀] using hx

/-- Under nonnegativity on the relation hyperplane, the reciprocal identity forces exactly one
negative diagonal coefficient.  This is the sign assertion in the fully-real fiber formula. -/
theorem ncard_negative_eq_one_of_reciprocal_identity
    (u μ : ι → ℝ) (hu : u ≠ 0) (hμ : ∀ i, μ i ≠ 0)
    (hrecip : ∑ i, u i ^ 2 / μ i = 0)
    (hnonneg : ∀ x, relation u x = 0 →
      0 ≤ QuadraticMap.weightedSumSquares ℝ μ x) :
    Set.ncard {i | μ i < 0} = 1 := by
  have hrelation : relation u ≠ 0 := by
    intro hzero
    apply hu
    funext i
    have hi := LinearMap.congr_fun hzero (Pi.single i 1)
    simpa [relation, dotProduct, Pi.single_apply] using hi
  have hupper : Set.ncard {i | μ i < 0} ≤ 1 := by
    have hs := QuadraticForm.sigNeg_le_one_of_nonneg_ker
      (QuadraticMap.weightedSumSquares ℝ μ) (relation u) hrelation hnonneg
    rwa [QuadraticForm.sigNeg_weightedSumSquares] at hs
  have hlower : 0 < Set.ncard {i | μ i < 0} := by
    rw [Set.ncard_pos]
    by_contra hnone
    have hμpos : ∀ i, 0 < μ i := by
      intro i
      have hnonnegμ : 0 ≤ μ i := le_of_not_gt fun hi ↦ hnone ⟨i, hi⟩
      exact lt_of_le_of_ne hnonnegμ (Ne.symm (hμ i))
    have hu_exists : ∃ i, u i ≠ 0 := by
      by_contra hall
      apply hu
      funext i
      exact not_ne_iff.mp (fun hi ↦ hall ⟨i, hi⟩)
    obtain ⟨i, hui⟩ := hu_exists
    have hsumpos : 0 < ∑ j, u j ^ 2 / μ j := by
      apply Finset.sum_pos'
      · intro j _
        exact div_nonneg (sq_nonneg _) (hμpos j).le
      · exact ⟨i, Finset.mem_univ i, div_pos (sq_pos_of_ne_zero hui) (hμpos i)⟩
    linarith
  omega

end ReciprocalHyperplane
