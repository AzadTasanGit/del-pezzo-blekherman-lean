import DelPezzoBlekherman.SOS.ProjectiveBasepoint
import DelPezzoBlekherman.SOS.ExactLength

noncomputable section

universe u v w z

open scoped BigOperators
open Finset

namespace SOSKernelLength

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [Module.Finite ℝ V]
variable {Q : Type w} [AddCommGroup Q] [Module ℝ Q]

/-- Exact minimal SOS length with the proper-subspace basepoint interface discharged by
surjectivity on projective evaluation directions of the Hankel radical. -/
theorem boundary_sos_has_exact_minimal_length_of_projective_surjective
    {X : Type z} (evalV : X → Module.Dual ℝ V) (evalQ : X → Q →ₗ[ℝ] ℝ)
    (mul : LinearMap.BilinMap ℝ V Q)
    (hevalMul : ∀ x f, evalQ x (mul f f) = (evalV x f) ^ 2)
    (ell : Q →ₗ[ℝ] ℝ) (B : LinearMap.BilinForm ℝ V)
    (hPSD : B.IsPosSemidef) (hB : ∀ x y, B x y = ell (mul x y))
    (p : Q) (hpositive : ∀ x, 0 < evalQ x p) (hsupport : ell p = 0)
    (hprojective : ∀ phi : Module.Dual ℝ (LinearMap.ker B), phi ≠ 0 →
      ∃ x : X, ∃ a : ℝ, a ≠ 0 ∧
        ProjectiveBasepoint.restrictedEval evalV (LinearMap.ker B) x = a • phi)
    {m : ℕ} (hker : Module.finrank ℝ (LinearMap.ker B) = m + 1)
    {κ : Type v} [Fintype κ] [DecidableEq κ] (f : κ → V)
    (hrep : p = ∑ i, mul (f i) (f i)) :
    ∃ (s : Finset κ) (g : s → V),
      s.card = m + 1 ∧
      p = ∑ i, mul (g i) (g i) ∧
      ∀ {ι : Type v} [Fintype ι] (h : ι → V),
        p = ∑ i, mul (h i) (h i) → m + 1 ≤ Fintype.card ι := by
  exact boundary_sos_has_exact_minimal_length evalV evalQ mul hevalMul ell B
    hPSD hB p hpositive hsupport
      (ProjectiveBasepoint.proper_subspace_has_common_zero_of_projective_surjective
        evalV (LinearMap.ker B) hprojective)
      (hker := hker) (f := f) hrep

end SOSKernelLength
