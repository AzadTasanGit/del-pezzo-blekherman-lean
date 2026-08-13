import NegativeDirectionsBuilderScratch
import MixedReciprocalHyperplaneScratch
import RealFiberInertiaBridgeScratch

noncomputable section

universe u

open scoped BigOperators
open Finset

namespace QuadraticForm.NonrealPairNegativeDirections

variable {P : Type u} [Fintype P] [DecidableEq P]

/-- The real quadratic form contributed by a family of complex-conjugate evaluation blocks. -/
def complexBlockBilin (b : P → ℂ) : LinearMap.BilinForm ℝ (P → ℂ) :=
  LinearMap.mk₂ ℝ (fun z x ↦ ∑ p, 2 * (b p * z p * x p).re)
    (by
      intro z z' x
      simp only [Pi.add_apply, add_mul, Complex.add_re, mul_add, Finset.sum_add_distrib]
      )
    (by
      intro r z x
      simp only [Pi.smul_apply, Complex.real_smul]
      simp only [smul_eq_mul]
      conv_rhs => rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, add_zero]
      ring)
    (by
      intro z x x'
      simp only [Pi.add_apply, mul_add, Complex.add_re, Finset.sum_add_distrib]
      )
    (by
      intro r z x
      simp only [Pi.smul_apply, Complex.real_smul]
      simp only [smul_eq_mul]
      conv_rhs => rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, add_zero]
      ring)

def complexBlockForm (b : P → ℂ) : QuadraticForm ℝ (P → ℂ) :=
  (complexBlockBilin b).toQuadraticMap

@[simp]
theorem complexBlockForm_apply (b : P → ℂ) (z : P → ℂ) :
    complexBlockForm b z = ∑ p, 2 * (b p * z p ^ 2).re := by
  simp only [complexBlockForm, complexBlockBilin,
    LinearMap.BilinMap.toQuadraticMap_apply, LinearMap.mk₂_apply]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [pow_two]
  ring

/-- Coordinatewise inclusion of the real axes into the complex evaluation blocks. -/
def realAxisLinear : (P → ℝ) →ₗ[ℝ] (P → ℂ) where
  toFun x p := x p
  map_add' x y := by ext p <;> simp
  map_smul' r x := by ext p <;> simp

theorem realAxisLinear_injective : Function.Injective (realAxisLinear :
    (P → ℝ) →ₗ[ℝ] (P → ℂ)) := by
  intro x y h
  funext p
  have hp := congrFun h p
  exact Complex.ofReal_injective hp

/-- The normalized relation on a family of complex-conjugate blocks. -/
def complexRelationOne : Module.Dual ℝ (P → ℂ) where
  toFun z := ∑ p, 2 * (z p).re
  map_add' z z' := by
    simp only [Pi.add_apply, Complex.add_re, mul_add, Finset.sum_add_distrib]
  map_smul' r z := by
    simp only [Pi.smul_apply, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, smul_eq_mul, RingHom.id_apply]
    conv_rhs => rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    ring

@[simp]
theorem complexRelationOne_apply (z : P → ℂ) :
    complexRelationOne z = ∑ p, 2 * (z p).re := rfl

@[simp]
theorem complexRelationOne_single (p : P) (z : ℂ) :
    complexRelationOne (Pi.single p z) = 2 * z.re := by
  rw [complexRelationOne_apply, Finset.sum_eq_single p]
  · simp [Pi.single_apply]
  · intro q hq hqp
    simp [Pi.single_apply, hqp]
  · simp

@[simp]
theorem complexBlockForm_single (b : P → ℂ) (p : P) (z : ℂ) :
    complexBlockForm b (Pi.single p z) = 2 * (b p * z ^ 2).re := by
  rw [complexBlockForm_apply, Finset.sum_eq_single p]
  · simp [Pi.single_apply]
  · intro q hq hqp
    simp [Pi.single_apply, hqp]
  · simp

/-- If every normalized complex block has negative real coefficient, its real axis supplies one
independent negative direction.  Thus the whole family supplies exactly one direction per
conjugate pair. -/
def ofComplexBlocks (b : P → ℂ) (hb : ∀ p, (b p).re < 0) :
    NonrealPairNegativeDirections (complexBlockForm b) P := by
  let W : Submodule ℝ (P → ℂ) := LinearMap.range realAxisLinear
  let e : (P → ℝ) ≃ₗ[ℝ] W := LinearEquiv.ofInjective realAxisLinear realAxisLinear_injective
  apply ofWeightedCoordinates (complexBlockForm b) W e (fun p ↦ 2 * (b p).re)
  · intro p
    exact mul_neg_of_pos_of_neg (by norm_num) (hb p)
  · intro x
    simp only [complexBlockForm_apply]
    apply Finset.sum_congr rfl
    intro p hp
    change 2 * (b p * (x p : ℂ) ^ 2).re = 2 * (b p).re * x p ^ 2
    simp [pow_two, Complex.mul_re]
    ring

/-- In the normalized complex-block model, relation-kernel nonnegativity and non-isotropy of
each block already imply that there is at most one block.  This is the direct linear-algebraic
form of the paper's at-most-one-conjugate-pair argument. -/
theorem card_le_one_of_nonnegative_relationOne
    (b : P → ℂ)
    (hnonneg : ∀ z, complexRelationOne z = 0 → 0 ≤ complexBlockForm b z)
    (hnonisotropic : ∀ p,
      complexBlockForm b (Pi.single p Complex.I) ≠ 0) :
    Nat.card P ≤ 1 := by
  classical
  cases isEmpty_or_nonempty P with
  | inl hempty =>
      haveI := hempty
      simp [Nat.card_eq_fintype_card]
  | inr hnonempty =>
      haveI := hnonempty
      have hrelation : (complexRelationOne : Module.Dual ℝ (P → ℂ)) ≠ 0 := by
        intro hzero
        let p : P := Classical.choice inferInstance
        have hp := LinearMap.congr_fun hzero (Pi.single p 1)
        have hp' : (2 : ℝ) = 0 := by
          simpa only [complexRelationOne_single, Complex.one_re, mul_one,
            LinearMap.zero_apply] using hp
        norm_num at hp'
      have hb : ∀ p, (b p).re < 0 := by
        intro p
        let z : P → ℂ := Pi.single p Complex.I
        have hzrel : complexRelationOne z = 0 := by
          simp only [z, complexRelationOne_single, Complex.I_re, mul_zero]
        have hznonneg := hnonneg z hzrel
        have hzvalue : complexBlockForm b z = -2 * (b p).re := by
          simp only [z, complexBlockForm_single, pow_two, Complex.I_mul_I,
            mul_neg, mul_one, Complex.neg_re]
          ring
        have hle : (b p).re ≤ 0 := by
          rw [hzvalue] at hznonneg
          linarith
        have hne : (b p).re ≠ 0 := by
          intro hre
          apply hnonisotropic p
          rw [hzvalue]
          simp [hre]
        exact lt_of_le_of_ne hle hne
      exact (ofComplexBlocks b hb).card_le_one_of_nonneg_ker
        complexRelationOne hrelation hnonneg

end QuadraticForm.NonrealPairNegativeDirections

namespace IsArtinianRing

/-- End-to-end pair-count theorem for the actual complex diagonal block model: negative real
block coefficients construct the independent pair directions, while nonnegativity on the
evaluation-relation kernel supplies the index-one bound. -/
theorem real_reduced_fiber_rational_point_dichotomy_of_complexBlocks
    {A : Type u} [CommRing A] [Algebra ℝ A] [Module.Finite ℝ A] [IsReduced A]
    [Fintype (QuadraticClosedPoint ℝ A)] [DecidableEq (QuadraticClosedPoint ℝ A)]
    (b : QuadraticClosedPoint ℝ A → ℂ) (hb : ∀ p, (b p).re < 0)
    (relation : Module.Dual ℝ (QuadraticClosedPoint ℝ A → ℂ))
    (hrelation : relation ≠ 0)
    (hnonneg : ∀ x, relation x = 0 →
      0 ≤ QuadraticForm.NonrealPairNegativeDirections.complexBlockForm b x)
    {c : ℕ} (hrank : Module.finrank ℝ A = c + 2) :
    (Nat.card (QuadraticClosedPoint ℝ A) = 0 ∧
        Nat.card (RationalClosedPoint ℝ A) = c + 2) ∨
      (Nat.card (QuadraticClosedPoint ℝ A) = 1 ∧
        Nat.card (RationalClosedPoint ℝ A) = c) := by
  exact IsArtinianRing.real_reduced_fiber_rational_point_dichotomy_of_nonneg_relationKernel
    (QuadraticForm.NonrealPairNegativeDirections.complexBlockForm b)
    (QuadraticForm.NonrealPairNegativeDirections.ofComplexBlocks b hb)
    relation hrelation hnonneg hrank

/-- Fully normalized version: nonnegativity on the complex evaluation-relation kernel and
non-isotropy automatically force both the block signs and the at-most-one-pair conclusion. -/
theorem real_reduced_fiber_rational_point_dichotomy_of_normalizedComplexBlocks
    {A : Type u} [CommRing A] [Algebra ℝ A] [Module.Finite ℝ A] [IsReduced A]
    [Fintype (QuadraticClosedPoint ℝ A)] [DecidableEq (QuadraticClosedPoint ℝ A)]
    (b : QuadraticClosedPoint ℝ A → ℂ)
    (hnonneg : ∀ z,
      QuadraticForm.NonrealPairNegativeDirections.complexRelationOne z = 0 →
      0 ≤ QuadraticForm.NonrealPairNegativeDirections.complexBlockForm b z)
    (hnonisotropic : ∀ p,
      QuadraticForm.NonrealPairNegativeDirections.complexBlockForm b
        (Pi.single p Complex.I) ≠ 0)
    {c : ℕ} (hrank : Module.finrank ℝ A = c + 2) :
    (Nat.card (QuadraticClosedPoint ℝ A) = 0 ∧
        Nat.card (RationalClosedPoint ℝ A) = c + 2) ∨
      (Nat.card (QuadraticClosedPoint ℝ A) = 1 ∧
        Nat.card (RationalClosedPoint ℝ A) = c) :=
  real_reduced_fiber_rational_point_dichotomy hrank
    (QuadraticForm.NonrealPairNegativeDirections.card_le_one_of_nonnegative_relationOne
      b hnonneg hnonisotropic)

end IsArtinianRing
