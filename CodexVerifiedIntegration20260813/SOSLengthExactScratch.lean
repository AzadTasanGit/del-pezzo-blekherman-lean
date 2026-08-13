import SOSCompressionScratch
import SOSKernelLengthScratch

noncomputable section

universe u v w z

open scoped BigOperators
open Finset

namespace SOSKernelLength

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [Module.Finite ℝ V]
variable {Q : Type w} [AddCommGroup Q] [Module ℝ Q]

/-- A strictly positive boundary SOS automatically has a representation by exactly `m+1`
squares, and every representation has at least that many squares.  Unlike
`supplied_add_one_representation_is_minimal`, this theorem derives the upper-bound representation
from an arbitrary finite SOS representation by the checked Gram-compression argument.  Its sole
geometric interface is the proper-subspace basepoint property of the Hankel radical. -/
theorem boundary_sos_has_exact_minimal_length
    {X : Type z} (evalV : X → Module.Dual ℝ V) (evalQ : X → Q →ₗ[ℝ] ℝ)
    (mul : LinearMap.BilinMap ℝ V Q)
    (hevalMul : ∀ x f, evalQ x (mul f f) = (evalV x f) ^ 2)
    (ell : Q →ₗ[ℝ] ℝ) (B : LinearMap.BilinForm ℝ V)
    (hPSD : B.IsPosSemidef) (hB : ∀ x y, B x y = ell (mul x y))
    (p : Q) (hpositive : ∀ x, 0 < evalQ x p) (hsupport : ell p = 0)
    (hproper : ∀ U : Submodule ℝ V, U < LinearMap.ker B →
      ∃ x : X, ∀ g ∈ U, evalV x g = 0)
    {m : ℕ} (hker : Module.finrank ℝ (LinearMap.ker B) = m + 1)
    {κ : Type v} [Fintype κ] [DecidableEq κ] (f : κ → V)
    (hrep : p = ∑ i, mul (f i) (f i)) :
    ∃ (s : Finset κ) (g : s → V),
      s.card = m + 1 ∧
      p = ∑ i, mul (g i) (g i) ∧
      ∀ {ι : Type v} [Fintype ι] (h : ι → V),
        p = ∑ i, mul (h i) (h i) → m + 1 ≤ Fintype.card ι := by
  have hsum : ∑ i, B (f i) (f i) = 0 := by
    apply hankel_sum_eq_zero (fun x y ↦ mul x y) ell B hB f
    rw [← hrep]
    exact hsupport
  have hfker : ∀ i, f i ∈ LinearMap.ker B :=
    each_mem_ker_of_sum_apply_self_eq_zero B hPSD f hsum
  have hnoCommonZero : ∀ x : X, ∃ i, evalV x (f i) ≠ 0 :=
    no_common_zero_of_strictlyPositive_sos evalV evalQ (fun x y ↦ mul x y)
      hevalMul p hpositive f hrep
  have hspanEq : Submodule.span ℝ (Set.range f) = LinearMap.ker B :=
    span_eq_of_no_common_zero evalV (LinearMap.ker B) f hfker hproper hnoCommonZero
  obtain ⟨s, g, hcard, hcompress⟩ :=
    SOSCompression.exists_compression_to_finrank_span mul f
  have hcard' : s.card = m + 1 := by
    rw [hcard, hspanEq, hker]
  have hrep' : p = ∑ i, mul (g i) (g i) := by
    rw [hrep]
    exact hcompress.symm
  refine ⟨s, g, hcard', hrep', ?_⟩
  intro ι inst h hrepr
  have hsupport' : ell (∑ i, mul (h i) (h i)) = 0 := by
    rw [← hrepr]
    exact hsupport
  exact boundary_sos_length_ge_add_one_of_basepoints evalV (fun x y ↦ mul x y)
    ell B hPSD hB h hsupport' hproper
      (no_common_zero_of_strictlyPositive_sos evalV evalQ (fun x y ↦ mul x y)
        hevalMul p hpositive h hrepr) hker

end SOSKernelLength
