import RealFiberFamilyCountScratch
import SOSLengthContinuousDenseScratch

noncomputable section

universe u v w z t

open scoped BigOperators
open Finset

namespace SOSKernelLength

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable {Q : Type w} [AddCommGroup Q] [Module ℝ Q]

/-- Exact minimal SOS length from an actual family of reduced finite real fiber algebras. The
abstract numerical count functions are discharged by rational/quadratic closed-point cardinalities,
and the real-image condition is discharged by lifting rational fiber points to the real source. -/
theorem boundary_sos_has_exact_minimal_length_of_real_fiber_family
    {X : Type z} [TopologicalSpace X] [CompactSpace X]
    (evalV : X → Module.Dual ℝ V) (evalQ : X → Q →ₗ[ℝ] ℝ)
    (mul : LinearMap.BilinMap ℝ V Q)
    (hevalMul : ∀ x f, evalQ x (mul f f) = (evalV x f) ^ 2)
    (ell : Q →ₗ[ℝ] ℝ) (B : LinearMap.BilinForm ℝ V)
    (hPSD : LinearMap.IsPosSemidef B) (hB : ∀ x y, B x y = ell (mul x y))
    (p : Q) (hpositive : ∀ x, 0 < evalQ x p) (hsupport : ell p = 0)
    {κ : Type v} [Fintype κ] [DecidableEq κ] (f : κ → V)
    (hrep : p = ∑ i, mul (f i) (f i))
    (hEvalContinuous : Continuous (fun x ↦ LinearMap.toContinuousLinearMap (evalV x)))
    (Omega : Set (RealProjectiveTopology.Direction ((LinearMap.ker B) →L[ℝ] ℝ)))
    (hOmega : Dense Omega)
    (A : RealProjectiveTopology.Direction ((LinearMap.ker B) →L[ℝ] ℝ) → Type t)
    [∀ y, CommRing (A y)] [∀ y, Algebra ℝ (A y)] [∀ y, Module.Finite ℝ (A y)]
    {c : ℕ} (hc : 1 ≤ c)
    (hReduced : ∀ y ∈ Omega, IsReduced (A y))
    (hRank : ∀ y ∈ Omega, Module.finrank ℝ (A y) = c + 2)
    (hpairs : ∀ y ∈ Omega, Nat.card (QuadraticClosedPoint ℝ (A y)) ≤ 1)
    (lift : ∀ y, y ∈ Omega → RationalClosedPoint ℝ (A y) → X)
    (hlift :
      let hEvalNonzero := restrictedEval_ne_zero_of_strictlyPositive_sos
        evalV evalQ mul hevalMul ell B hPSD hB p hpositive hsupport f hrep
      ∀ y hy q, realProjectiveEval evalV B hEvalNonzero (lift y hy q) = y)
    {m : ℕ} (hker : Module.finrank ℝ (LinearMap.ker B) = m + 1) :
    ∃ (s : Finset κ) (q : s → V),
      s.card = m + 1 ∧
      p = ∑ i, mul (q i) (q i) ∧
      ∀ {ι : Type v} [Fintype ι] (q' : ι → V),
        p = ∑ i, mul (q' i) (q' i) → m + 1 ≤ Fintype.card ι := by
  let hEvalNonzero := restrictedEval_ne_zero_of_strictlyPositive_sos
    evalV evalQ mul hevalMul ell B hPSD hB p hpositive hsupport f hrep
  apply boundary_sos_has_exact_minimal_length_of_ordinary_continuity_and_dense_locus
    evalV evalQ mul hevalMul ell B hPSD hB p hpositive hsupport f hrep
    hEvalContinuous Omega hOmega (RealFiberFamily.realCount A) (RealFiberFamily.pairCount A) hc
  · exact RealFiberFamily.count_eq_add_two_on A hReduced hRank
  · exact RealFiberFamily.pairCount_le_one_on A hpairs
  · dsimp only
    intro y hyOmega hy
    exact RealFiberFamily.realCount_eq_zero_of_not_mem_range_of_lift A
      (realProjectiveEval evalV B hEvalNonzero) Omega lift hlift y hyOmega hy
  · exact hker

end SOSKernelLength
