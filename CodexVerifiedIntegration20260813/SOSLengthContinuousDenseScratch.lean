import SOSLengthRealProjectiveScratch

noncomputable section

universe u v w z

open scoped BigOperators
open Finset

namespace SOSKernelLength

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable {Q : Type w} [AddCommGroup Q] [Module ℝ Q]

/-- Exact minimal SOS length from ordinary evaluation continuity and any supplied dense reduced
fiber locus. Strict positivity automatically supplies nowhere-zero radical evaluation, so the
compact real projective map and its continuity are derived rather than assumed. -/
theorem boundary_sos_has_exact_minimal_length_of_ordinary_continuity_and_dense_locus
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
    (realCount pairCount :
      RealProjectiveTopology.Direction ((LinearMap.ker B) →L[ℝ] ℝ) → ℕ)
    {c : ℕ} (hc : 1 ≤ c)
    (hcount : ∀ y ∈ Omega, c + 2 = realCount y + 2 * pairCount y)
    (hpairs : ∀ y ∈ Omega, pairCount y ≤ 1)
    (hrealCountZero :
      let hEvalNonzero := restrictedEval_ne_zero_of_strictlyPositive_sos
        evalV evalQ mul hevalMul ell B hPSD hB p hpositive hsupport f hrep
      ∀ y ∈ Omega, y ∉ Set.range (realProjectiveEval evalV B hEvalNonzero) →
        realCount y = 0)
    {m : ℕ} (hker : Module.finrank ℝ (LinearMap.ker B) = m + 1) :
    ∃ (s : Finset κ) (q : s → V),
      s.card = m + 1 ∧
      p = ∑ i, mul (q i) (q i) ∧
      ∀ {ι : Type v} [Fintype ι] (q' : ι → V),
        p = ∑ i, mul (q' i) (q' i) → m + 1 ≤ Fintype.card ι := by
  let hEvalNonzero := restrictedEval_ne_zero_of_strictlyPositive_sos
    evalV evalQ mul hevalMul ell B hPSD hB p hpositive hsupport f hrep
  have hphi : Continuous (realProjectiveEval evalV B hEvalNonzero) :=
    continuous_realProjectiveEval evalV B hEvalNonzero hEvalContinuous
  apply boundary_sos_has_exact_minimal_length_of_real_projective_perturbation
    evalV evalQ mul hevalMul ell B hPSD hB p hpositive hsupport
    hEvalNonzero hphi Omega hOmega realCount pairCount hc hcount hpairs
  · simpa [hEvalNonzero] using hrealCountZero
  · exact hker
  · exact hrep

end SOSKernelLength
