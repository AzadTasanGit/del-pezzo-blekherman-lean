import SOSLengthPerturbationScratch
import RealProjectiveTopologyScratch

noncomputable section

universe u v w z

open scoped BigOperators
open Finset

namespace SOSKernelLength

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable {Q : Type w} [AddCommGroup Q] [Module ℝ Q]

/-- Restriction of continuous linear functionals to a submodule, as a continuous linear map. -/
def restrictContinuousDual (W : Submodule ℝ V) :
    (V →L[ℝ] ℝ) →L[ℝ] (W →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ W V ℝ).flip (Submodule.subtypeL W)

omit [FiniteDimensional ℝ V] in
@[simp]
theorem restrictContinuousDual_apply (W : Submodule ℝ V) (psi : V →L[ℝ] ℝ) (x : W) :
    restrictContinuousDual W psi x = psi x := rfl

/-- Strict positivity of a supported SOS makes evaluation on the Hankel radical nonzero at every
real point. This is the basepoint-freeness input used to define the kernel morphism. -/
theorem restrictedEval_ne_zero_of_strictlyPositive_sos
    {X : Type z} (evalV : X → Module.Dual ℝ V) (evalQ : X → Q →ₗ[ℝ] ℝ)
    (mul : LinearMap.BilinMap ℝ V Q)
    (hevalMul : ∀ x f, evalQ x (mul f f) = (evalV x f) ^ 2)
    (ell : Q →ₗ[ℝ] ℝ) (B : LinearMap.BilinForm ℝ V)
    (hPSD : B.IsPosSemidef) (hB : ∀ x y, B x y = ell (mul x y))
    (p : Q) (hpositive : ∀ x, 0 < evalQ x p) (hsupport : ell p = 0)
    {κ : Type v} [Fintype κ] (f : κ → V)
    (hrep : p = ∑ i, mul (f i) (f i)) :
    ∀ x, ProjectiveBasepoint.restrictedEval evalV (LinearMap.ker B) x ≠ 0 := by
  have hsupport' : ell (∑ i, mul (f i) (f i)) = 0 := by
    rw [← hrep]
    exact hsupport
  have hsum : ∑ i, B (f i) (f i) = 0 :=
    hankel_sum_eq_zero (fun x y ↦ mul x y) ell B hB f hsupport'
  have hfker : ∀ i, f i ∈ LinearMap.ker B :=
    each_mem_ker_of_sum_apply_self_eq_zero B hPSD f hsum
  have hnoCommonZero : ∀ x : X, ∃ i, evalV x (f i) ≠ 0 :=
    no_common_zero_of_strictlyPositive_sos evalV evalQ (fun x y ↦ mul x y)
      hevalMul p hpositive f hrep
  intro x hzero
  obtain ⟨i, hi⟩ := hnoCommonZero x
  apply hi
  have happ := LinearMap.congr_fun hzero (⟨f i, hfker i⟩ : LinearMap.ker B)
  simpa [ProjectiveBasepoint.restrictedEval] using happ

/-- The continuous real projective evaluation direction associated to a nowhere-zero restricted
evaluation functional. -/
def realProjectiveEval
    {X : Type z} (evalV : X → Module.Dual ℝ V) (B : LinearMap.BilinForm ℝ V)
    (hEvalNonzero : ∀ x,
      ProjectiveBasepoint.restrictedEval evalV (LinearMap.ker B) x ≠ 0) :
    X → RealProjectiveTopology.Direction ((LinearMap.ker B) →L[ℝ] ℝ) :=
  fun x ↦ RealProjectiveTopology.directionOf _
    ⟨LinearMap.toContinuousLinearMap
        (ProjectiveBasepoint.restrictedEval evalV (LinearMap.ker B) x),
      (LinearMap.toContinuousLinearMap.injective.ne (hEvalNonzero x))⟩

/-- Continuity of the ordinary continuous-dual evaluation map implies continuity of its
normalized real-projective restriction to the Hankel radical. -/
theorem continuous_realProjectiveEval
    {X : Type z} [TopologicalSpace X]
    (evalV : X → Module.Dual ℝ V) (B : LinearMap.BilinForm ℝ V)
    (hEvalNonzero : ∀ x,
      ProjectiveBasepoint.restrictedEval evalV (LinearMap.ker B) x ≠ 0)
    (hEvalContinuous : Continuous (fun x ↦ LinearMap.toContinuousLinearMap (evalV x))) :
    Continuous (realProjectiveEval evalV B hEvalNonzero) := by
  apply (RealProjectiveTopology.continuous_directionOf
    ((LinearMap.ker B) →L[ℝ] ℝ)).comp
  apply Continuous.subtype_mk
  have hrestrict : Continuous (fun x ↦
      restrictContinuousDual (LinearMap.ker B)
        (LinearMap.toContinuousLinearMap (evalV x))) :=
    (restrictContinuousDual (LinearMap.ker B)).continuous.comp hEvalContinuous
  have heq : (fun x ↦ LinearMap.toContinuousLinearMap
      (ProjectiveBasepoint.restrictedEval evalV (LinearMap.ker B) x)) =
      (fun x ↦ restrictContinuousDual (LinearMap.ker B)
        (LinearMap.toContinuousLinearMap (evalV x))) := by
    funext x
    apply ContinuousLinearMap.ext
    intro y
    rfl
  rw [heq]
  exact hrestrict

theorem realProjectiveEval_eq_directionOf_iff
    {X : Type z} (evalV : X → Module.Dual ℝ V) (B : LinearMap.BilinForm ℝ V)
    (hEvalNonzero : ∀ x,
      ProjectiveBasepoint.restrictedEval evalV (LinearMap.ker B) x ≠ 0)
    (x : X) (psi : {psi : Module.Dual ℝ (LinearMap.ker B) // psi ≠ 0}) :
    realProjectiveEval evalV B hEvalNonzero x =
        RealProjectiveTopology.directionOf _
          ⟨LinearMap.toContinuousLinearMap psi.1,
            LinearMap.toContinuousLinearMap.injective.ne psi.2⟩ ↔
      ∃ a : ℝ, a ≠ 0 ∧
        ProjectiveBasepoint.restrictedEval evalV (LinearMap.ker B) x = a • psi.1 := by
  rw [realProjectiveEval, RealProjectiveTopology.directionOf_eq_iff_exists_smul]
  constructor
  · rintro ⟨a, ha, heq⟩
    refine ⟨a, ha, ?_⟩
    apply LinearMap.toContinuousLinearMap.injective
    simpa using heq
  · rintro ⟨a, ha, heq⟩
    refine ⟨a, ha, ?_⟩
    simpa using congr_arg LinearMap.toContinuousLinearMap heq

/-- The PDF's perturbation lower bound with the projective target instantiated by the compact
Hausdorff antipodal quotient of the dual unit sphere. -/
theorem boundary_sos_length_ge_add_one_of_real_projective_perturbation
    {X : Type z} [TopologicalSpace X] [CompactSpace X]
    (evalV : X → Module.Dual ℝ V) (evalQ : X → Q →ₗ[ℝ] ℝ)
    (mul : LinearMap.BilinMap ℝ V Q)
    (hevalMul : ∀ x f, evalQ x (mul f f) = (evalV x f) ^ 2)
    (ell : Q →ₗ[ℝ] ℝ) (B : LinearMap.BilinForm ℝ V)
    (hPSD : B.IsPosSemidef) (hB : ∀ x y, B x y = ell (mul x y))
    (p : Q) (hpositive : ∀ x, 0 < evalQ x p) (hsupport : ell p = 0)
    (hEvalNonzero : ∀ x,
      ProjectiveBasepoint.restrictedEval evalV (LinearMap.ker B) x ≠ 0)
    (hphi : Continuous (realProjectiveEval evalV B hEvalNonzero))
    (Omega : Set (RealProjectiveTopology.Direction ((LinearMap.ker B) →L[ℝ] ℝ)))
    (hOmega : Dense Omega)
    (realCount pairCount :
      RealProjectiveTopology.Direction ((LinearMap.ker B) →L[ℝ] ℝ) → ℕ)
    {c : ℕ} (hc : 1 ≤ c)
    (hcount : ∀ y ∈ Omega, c + 2 = realCount y + 2 * pairCount y)
    (hpairs : ∀ y ∈ Omega, pairCount y ≤ 1)
    (hrealCountZero : ∀ y ∈ Omega,
      y ∉ Set.range (realProjectiveEval evalV B hEvalNonzero) → realCount y = 0)
    {m : ℕ} (hker : Module.finrank ℝ (LinearMap.ker B) = m + 1)
    {ι : Type v} [Fintype ι] (f : ι → V)
    (hrep : p = ∑ i, mul (f i) (f i)) :
    m + 1 ≤ Fintype.card ι := by
  apply boundary_sos_length_ge_add_one_of_reduced_fiber_perturbation
    evalV evalQ mul hevalMul ell B hPSD hB p hpositive hsupport
    (realProjectiveEval evalV B hEvalNonzero) hphi
    (fun psi ↦ RealProjectiveTopology.directionOf _
      ⟨LinearMap.toContinuousLinearMap psi.1,
        LinearMap.toContinuousLinearMap.injective.ne psi.2⟩)
    (realProjectiveEval_eq_directionOf_iff evalV B hEvalNonzero)
    Omega hOmega realCount pairCount hc hcount hpairs hrealCountZero
    hker f hrep

/-- Exact minimal SOS length after replacing the abstract projective-ray target by the concrete
compact Hausdorff antipodal quotient. -/
theorem boundary_sos_has_exact_minimal_length_of_real_projective_perturbation
    {X : Type z} [TopologicalSpace X] [CompactSpace X]
    (evalV : X → Module.Dual ℝ V) (evalQ : X → Q →ₗ[ℝ] ℝ)
    (mul : LinearMap.BilinMap ℝ V Q)
    (hevalMul : ∀ x f, evalQ x (mul f f) = (evalV x f) ^ 2)
    (ell : Q →ₗ[ℝ] ℝ) (B : LinearMap.BilinForm ℝ V)
    (hPSD : B.IsPosSemidef) (hB : ∀ x y, B x y = ell (mul x y))
    (p : Q) (hpositive : ∀ x, 0 < evalQ x p) (hsupport : ell p = 0)
    (hEvalNonzero : ∀ x,
      ProjectiveBasepoint.restrictedEval evalV (LinearMap.ker B) x ≠ 0)
    (hphi : Continuous (realProjectiveEval evalV B hEvalNonzero))
    (Omega : Set (RealProjectiveTopology.Direction ((LinearMap.ker B) →L[ℝ] ℝ)))
    (hOmega : Dense Omega)
    (realCount pairCount :
      RealProjectiveTopology.Direction ((LinearMap.ker B) →L[ℝ] ℝ) → ℕ)
    {c : ℕ} (hc : 1 ≤ c)
    (hcount : ∀ y ∈ Omega, c + 2 = realCount y + 2 * pairCount y)
    (hpairs : ∀ y ∈ Omega, pairCount y ≤ 1)
    (hrealCountZero : ∀ y ∈ Omega,
      y ∉ Set.range (realProjectiveEval evalV B hEvalNonzero) → realCount y = 0)
    {m : ℕ} (hker : Module.finrank ℝ (LinearMap.ker B) = m + 1)
    {κ : Type v} [Fintype κ] [DecidableEq κ] (f : κ → V)
    (hrep : p = ∑ i, mul (f i) (f i)) :
    ∃ (s : Finset κ) (g : s → V),
      s.card = m + 1 ∧
      p = ∑ i, mul (g i) (g i) ∧
      ∀ {ι : Type v} [Fintype ι] (h : ι → V),
        p = ∑ i, mul (h i) (h i) → m + 1 ≤ Fintype.card ι := by
  apply boundary_sos_has_exact_minimal_length_of_reduced_fiber_perturbation
    evalV evalQ mul hevalMul ell B hPSD hB p hpositive hsupport
    (realProjectiveEval evalV B hEvalNonzero) hphi
    (fun psi ↦ RealProjectiveTopology.directionOf _
      ⟨LinearMap.toContinuousLinearMap psi.1,
        LinearMap.toContinuousLinearMap.injective.ne psi.2⟩)
    (realProjectiveEval_eq_directionOf_iff evalV B hEvalNonzero)
    Omega hOmega realCount pairCount hc hcount hpairs hrealCountZero
    hker f hrep

end SOSKernelLength
