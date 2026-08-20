/-
Copyright (c) 2026 Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import DelPezzoBlekherman.Algebra.NativeGorenstein
import DelPezzoBlekherman.Convexity.DualSlice
import DelPezzoBlekherman.LinearAlgebra.RankOneEvaluation
import DelPezzoBlekherman.SOS.ClosedCone
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Paper-facing statements of Theorem 1.1

This file begins the final composition layer.  Its declarations use the actual graded
coordinate ring and its real points, rather than the proof-only certificates used by some of
the internal algebra modules.
-/

noncomputable section

open Set
open LinearMap (BilinForm)
open ArtinianGorensteinDegreeOneCertificate

namespace DelPezzoBlekherman

universe u v

variable {A : Type u} {X : Type v}
variable [CommRing A] [Algebra ℝ A]

/-- Restriction of a real point evaluation to a homogeneous component. -/
def gradedEvaluation
    {B : Type*} [NormedCommRing B] [NormedAlgebra ℝ B]
    (𝒜 : ℕ → Submodule ℝ B) (e : B →ₐ[ℝ] ℝ) (d : ℕ)
    [Module.Finite ℝ (𝒜 d)] :
    𝒜 d →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (e.toLinearMap.comp (𝒜 d).subtype)

@[simp]
theorem gradedEvaluation_apply
    {B : Type*} [NormedCommRing B] [NormedAlgebra ℝ B]
    (𝒜 : ℕ → Submodule ℝ B) (e : B →ₐ[ℝ] ℝ) (d : ℕ)
    [Module.Finite ℝ (𝒜 d)] (q : 𝒜 d) :
    gradedEvaluation 𝒜 e d q = e q := by
  rfl

/-- The linear map which sends a degree-two functional to its Hankel bilinear form on degree
one. -/
def gradedHankelMap
    {B : Type*} [CommRing B] [Algebra ℝ B]
    (𝒜 : ℕ → Submodule ℝ B) [SetLike.GradedMonoid 𝒜] :
    ((𝒜 2) →ₗ[ℝ] ℝ) →ₗ[ℝ] BilinForm ℝ (𝒜 1) where
  toFun ell := (gradedDegreeOneMultiplication 𝒜).compr₂ ell
  map_add' ell eta := by ext u v; rfl
  map_smul' a ell := by ext u v; rfl

@[simp]
theorem gradedHankelMap_apply
    {B : Type*} [CommRing B] [Algebra ℝ B]
    (𝒜 : ℕ → Submodule ℝ B) [SetLike.GradedMonoid 𝒜]
    (ell : (𝒜 2) →ₗ[ℝ] ℝ) (u v : 𝒜 1) :
    gradedHankelMap 𝒜 ell u v = ell (gradedDegreeOneMultiplication 𝒜 u v) := rfl

/-- Standard gradedness in degree two makes the Hankel realization of degree-two functionals
injective. -/
theorem gradedHankelMap_injective_of_degreeTwoGeneratedByDegreeOne
    {B : Type*} [CommRing B] [Algebra ℝ B]
    (𝒜 : ℕ → Submodule ℝ B) [SetLike.GradedMonoid 𝒜]
    (hgenerated : DegreeTwoGeneratedByDegreeOne 𝒜) :
    Function.Injective (gradedHankelMap 𝒜) := by
  intro ell eta h
  apply LinearMap.ext
  intro q
  obtain ⟨t, rfl⟩ :=
    (tensorProduct_lift_surjective_of_symmetricSquareMultiplication_surjective
      (gradedDegreeOneMultiplication 𝒜)
      (gradedDegreeOneMultiplication_symmetric 𝒜) hgenerated) q
  have ht := LinearMap.congr_fun (congrArg TensorProduct.lift h) t
  change
    TensorProduct.lift ((gradedDegreeOneMultiplication 𝒜).compr₂ ell) t =
      TensorProduct.lift ((gradedDegreeOneMultiplication 𝒜).compr₂ eta) t at ht
  simpa only [TensorProduct.lift_compr₂, LinearMap.comp_apply] using ht

/-- Hankel forms arising from degree-two functionals. -/
def gradedHankelSubmodule
    {B : Type*} [CommRing B] [Algebra ℝ B]
    (𝒜 : ℕ → Submodule ℝ B) [SetLike.GradedMonoid 𝒜] :
    Submodule ℝ (BilinForm ℝ (𝒜 1)) :=
  LinearMap.range (gradedHankelMap 𝒜)

/-- Every form in the concrete graded Hankel space is symmetric. -/
theorem gradedHankelSubmodule_isSymm
    {B : Type*} [CommRing B] [Algebra ℝ B]
    (𝒜 : ℕ → Submodule ℝ B) [SetLike.GradedMonoid 𝒜]
    (P : BilinForm ℝ (𝒜 1)) (hP : P ∈ gradedHankelSubmodule 𝒜) :
    P.IsSymm := by
  obtain ⟨ell, rfl⟩ := hP
  rw [LinearMap.BilinForm.isSymm_def]
  intro u v
  exact congrArg ell (gradedDegreeOneMultiplication_symmetric 𝒜 u v)

/-- Restricting an algebra evaluation to degrees one and two identifies its Hankel form with
the rank-one square of its degree-one evaluation. -/
theorem gradedHankelMap_gradedEvaluation_eq_rankOne
    {B : Type*} [NormedCommRing B] [NormedAlgebra ℝ B]
    (𝒜 : ℕ → Submodule ℝ B) [SetLike.GradedMonoid 𝒜]
    [Module.Finite ℝ (𝒜 1)] [Module.Finite ℝ (𝒜 2)]
    (e : B →ₐ[ℝ] ℝ) :
    gradedHankelMap 𝒜 (gradedEvaluation 𝒜 e 2).toLinearMap =
      rankOneBilin (gradedEvaluation 𝒜 e 1).toLinearMap := by
  ext u v
  change e ((gradedDegreeOneMultiplication 𝒜 u v : 𝒜 2) : B) = e u * e v
  calc
    e ((gradedDegreeOneMultiplication 𝒜 u v : 𝒜 2) : B) =
        e ((u : B) * (v : B)) := congrArg e (gradedDegreeOneMultiplication_apply 𝒜 u v)
    _ = e u * e v := map_mul e (u : B) (v : B)

/-- The prime of the coordinate ring determined by a real point evaluation. -/
def realEvaluationPrime (e : A →ₐ[ℝ] ℝ) : PrimeSpectrum A :=
  ⟨RingHom.ker e.toRingHom, RingHom.ker_isPrime e.toRingHom⟩

/-- Actual Zariski density in the spectrum of a reduced coordinate ring implies that its real
point evaluations detect every coordinate-ring element. -/
theorem eq_zero_of_vanishes_on_zariskiDense_realEvaluations
    [IsReduced A] (eval : X → A →ₐ[ℝ] ℝ)
    (hDense : Dense (Set.range fun x ↦ realEvaluationPrime (eval x)))
    (a : A) (ha : ∀ x, eval x a = 0) :
    a = 0 := by
  have haVanishing :
      a ∈ PrimeSpectrum.vanishingIdeal
        (Set.range fun x ↦ realEvaluationPrime (eval x)) := by
    rw [PrimeSpectrum.mem_vanishingIdeal]
    rintro _ ⟨x, rfl⟩
    change eval x a = 0
    exact ha x
  have haUniv : a ∈ PrimeSpectrum.vanishingIdeal (Set.univ : Set (PrimeSpectrum A)) := by
    rw [← hDense.closure_eq, PrimeSpectrum.vanishingIdeal_closure]
    exact haVanishing
  simpa using haUniv

/-- The degree-one separation consequence used in the compact normalized-square proof follows
from genuine Zariski density of the real evaluation primes. -/
theorem gradedDegreeOneEvaluations_separate_of_zariskiDense
    [IsReduced A] (eval : X → A →ₐ[ℝ] ℝ)
    (hDense : Dense (Set.range fun x ↦ realEvaluationPrime (eval x)))
    (A₁ : Submodule ℝ A) (u : A₁)
    (hu : ∀ x, eval x u = 0) :
    u = 0 := by
  apply Subtype.ext
  exact eq_zero_of_vanishes_on_zariskiDense_realEvaluations eval hDense u hu

/-- The dual of the concrete graded SOS cone is exactly the cone of positive-semidefinite
Hankel forms.  This is the second assertion of Theorem 1.1(i). -/
theorem dualCone_gradedSOSCone_eq_psdHankel
    {B : Type*} [NormedCommRing B] [NormedAlgebra ℝ B]
    (𝒜 : ℕ → Submodule ℝ B) [SetLike.GradedMonoid 𝒜]
    :
    dualConeSet
        (SOSConeDual.sosCone (fun u ↦ gradedDegreeOneMultiplication 𝒜 u u) :
          Set (𝒜 2)) =
      {ell : (𝒜 2) →L[ℝ] ℝ |
        ((gradedDegreeOneMultiplication 𝒜).compr₂ ell.toLinearMap).IsPosSemidef} := by
  ext ell
  change
    (∀ q ∈ SOSConeDual.sosCone (fun u ↦ gradedDegreeOneMultiplication 𝒜 u u),
      0 ≤ ell q) ↔
      ((gradedDegreeOneMultiplication 𝒜).compr₂ ell.toLinearMap).IsPosSemidef
  constructor
  · intro h
    have hsquares : ∀ u, 0 ≤ ell (gradedDegreeOneMultiplication 𝒜 u u) :=
      (SOSConeDual.nonnegative_on_sosCone_iff
        (fun u ↦ gradedDegreeOneMultiplication 𝒜 u u) ell.toLinearMap).mp (by
          simpa using h)
    refine ⟨⟨?_⟩, ⟨hsquares⟩⟩
    intro u v
    change ell (gradedDegreeOneMultiplication 𝒜 u v) =
      ell (gradedDegreeOneMultiplication 𝒜 v u)
    rw [gradedDegreeOneMultiplication_symmetric]
  · intro h
    have hsquares : ∀ u, 0 ≤ ell (gradedDegreeOneMultiplication 𝒜 u u) :=
      fun u ↦ h.isNonneg.nonneg u
    have hcone := (SOSConeDual.nonnegative_on_sosCone_iff
      (fun u ↦ gradedDegreeOneMultiplication 𝒜 u u) ell.toLinearMap).mpr hsquares
    simpa using hcone

/-- Theorem 1.1(i), under the paper's literal Hilbert-series and Zariski-density hypotheses.
The finite-dimensional topology on each homogeneous component is arbitrary, as the conclusion
is independent of that choice. -/
theorem theorem1_1_i
    {B Y : Type*} [NormedCommRing B] [NormedAlgebra ℝ B] [IsReduced B]
    (𝒜 : ℕ → Submodule ℝ B) [SetLike.GradedMonoid 𝒜]
    (eval : Y → B →ₐ[ℝ] ℝ)
    (hDense : Dense (Set.range fun x ↦ realEvaluationPrime (eval x)))
    {m c : ℕ}
    (hHilbert : ∀ d,
      (Module.finrank ℝ (𝒜 d) : ℤ) =
        PowerSeries.coeff d (delPezzoHilbertSeries m c)) :
    IsClosed
        (SOSConeDual.sosCone (fun u ↦ gradedDegreeOneMultiplication 𝒜 u u) :
          Set (𝒜 2)) ∧
      dualConeSet
          (SOSConeDual.sosCone (fun u ↦ gradedDegreeOneMultiplication 𝒜 u u) :
            Set (𝒜 2)) =
        {ell : (𝒜 2) →L[ℝ] ℝ |
          ((gradedDegreeOneMultiplication 𝒜).compr₂ ell.toLinearMap).IsPosSemidef} := by
  let _ : Module.Finite ℝ (𝒜 1) :=
    moduleFinite_degreeOne_of_delPezzoHilbertSeries 𝒜 hHilbert
  refine ⟨?_, dualCone_gradedSOSCone_eq_psdHankel 𝒜⟩
  exact SOSConeDual.gradedSOSCone_isClosed_of_separating_evaluations
    𝒜 eval (by
      intro u hu
      exact gradedDegreeOneEvaluations_separate_of_zariskiDense eval hDense (𝒜 1) u hu)

/-- Under degree-two generation, an extreme ray of the functional dual cone remains extreme
after its faithful realization as a Hankel bilinear form. -/
theorem gradedHankel_extreme_of_functional_extreme
    {B : Type*} [NormedCommRing B] [NormedAlgebra ℝ B]
    (𝒜 : ℕ → Submodule ℝ B) [SetLike.GradedMonoid 𝒜]
    [Module.Finite ℝ (𝒜 1)] [Module.Finite ℝ (𝒜 2)]
    (hgenerated : DegreeTwoGeneratedByDegreeOne 𝒜)
    (ell : (𝒜 2) →L[ℝ] ℝ)
    (hell : SpansExtremeRay
      (dualConeSet
        (SOSConeDual.sosCone (fun u ↦ gradedDegreeOneMultiplication 𝒜 u u) :
          Set (𝒜 2))) ell) :
    SpansExtremeRay (psdIn (gradedHankelSubmodule 𝒜))
      (gradedHankelMap 𝒜 ell.toLinearMap) := by
  let hankel := gradedHankelMap 𝒜
  have hinj := gradedHankelMap_injective_of_degreeTwoGeneratedByDegreeOne 𝒜 hgenerated
  have hPSD : (hankel ell.toLinearMap).IsPosSemidef := by
    refine ⟨⟨?_⟩, ⟨?_⟩⟩
    · intro u v
      exact congrArg ell (gradedDegreeOneMultiplication_symmetric 𝒜 u v)
    · exact (SOSConeDual.nonnegative_on_sosCone_iff
        (fun u ↦ gradedDegreeOneMultiplication 𝒜 u u) ell.toLinearMap).mp hell.1
  refine ⟨⟨⟨ell.toLinearMap, rfl⟩, hPSD⟩, ?_, ?_⟩
  · intro hzero
    apply hell.2.1
    apply ContinuousLinearMap.coe_injective
    apply hinj
    simpa using hzero
  · intro P hP R hR hsum
    obtain ⟨Pmem, Ppsd⟩ := hP
    obtain ⟨Rmem, Rpsd⟩ := hR
    obtain ⟨p, hp⟩ := Pmem
    obtain ⟨r, hr⟩ := Rmem
    let pL : (𝒜 2) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap p
    let rL : (𝒜 2) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap r
    have hpdual : pL ∈ dualConeSet
        (SOSConeDual.sosCone (fun u ↦ gradedDegreeOneMultiplication 𝒜 u u) :
          Set (𝒜 2)) :=
      (SOSConeDual.nonnegative_on_sosCone_iff
        (fun u ↦ gradedDegreeOneMultiplication 𝒜 u u) p).mpr (by
          intro u
          have hu := Ppsd.isNonneg.nonneg u
          rw [← hp] at hu
          exact hu)
    have hrdual : rL ∈ dualConeSet
        (SOSConeDual.sosCone (fun u ↦ gradedDegreeOneMultiplication 𝒜 u u) :
          Set (𝒜 2)) :=
      (SOSConeDual.nonnegative_on_sosCone_iff
        (fun u ↦ gradedDegreeOneMultiplication 𝒜 u u) r).mpr (by
          intro u
          have hu := Rpsd.isNonneg.nonneg u
          rw [← hr] at hu
          exact hu)
    have hellsum : ell = pL + rL := by
      apply ContinuousLinearMap.coe_injective
      apply hinj
      simpa [pL, rL, hp, hr] using hsum
    obtain ⟨a, b, ha, hb, hpa, hrb⟩ :=
      hell.2.2 pL hpdual rL hrdual hellsum
    refine ⟨a, b, ha, hb, ?_, ?_⟩
    · rw [← hp]
      exact congrArg (gradedHankelMap 𝒜) (congrArg ContinuousLinearMap.toLinearMap hpa)
    · rw [← hr]
      exact congrArg (gradedHankelMap 𝒜) (congrArg ContinuousLinearMap.toLinearMap hrb)

/-- The point-evaluation assertion of Theorem 1.1(ii): every nonzero projective real-point
evaluation spans an extreme ray of the concrete dual SOS cone. -/
theorem theorem1_1_ii_pointEvaluation
    {B : Type*} [NormedCommRing B] [NormedAlgebra ℝ B]
    (𝒜 : ℕ → Submodule ℝ B) [SetLike.GradedMonoid 𝒜]
    [Module.Finite ℝ (𝒜 1)] [Module.Finite ℝ (𝒜 2)]
    (hgenerated : DegreeTwoGeneratedByDegreeOne 𝒜)
    (e : B →ₐ[ℝ] ℝ)
    (he₁ : gradedEvaluation 𝒜 e 1 ≠ 0) :
    SpansExtremeRay
      (dualConeSet
        (SOSConeDual.sosCone (fun u ↦ gradedDegreeOneMultiplication 𝒜 u u) :
          Set (𝒜 2)))
      (gradedEvaluation 𝒜 e 2) := by
  let H := gradedHankelSubmodule 𝒜
  let f : (𝒜 1) →ₗ[ℝ] ℝ := (gradedEvaluation 𝒜 e 1).toLinearMap
  let ell : (𝒜 2) →L[ℝ] ℝ := gradedEvaluation 𝒜 e 2
  have hf : f ≠ 0 := by
    intro hf0
    apply he₁
    ext u
    exact LinearMap.congr_fun hf0 u
  have hrankH : rankOneBilin f ∈ H := by
    refine ⟨ell.toLinearMap, ?_⟩
    exact gradedHankelMap_gradedEvaluation_eq_rankOne 𝒜 e
  have hrankExtreme : SpansExtremeRay (psdIn H) (rankOneBilin f) :=
    rankOne_spansExtremeRay H (gradedHankelSubmodule_isSymm 𝒜) f hf hrankH
  have hinj := gradedHankelMap_injective_of_degreeTwoGeneratedByDegreeOne 𝒜 hgenerated
  have hellHankel : gradedHankelMap 𝒜 ell.toLinearMap = rankOneBilin f :=
    gradedHankelMap_gradedEvaluation_eq_rankOne 𝒜 e
  refine ⟨?_, ?_, ?_⟩
  · exact (SOSConeDual.nonnegative_on_sosCone_iff
      (fun u ↦ gradedDegreeOneMultiplication 𝒜 u u) ell.toLinearMap).mpr (by
        intro u
        change 0 ≤ e ((gradedDegreeOneMultiplication 𝒜 u u : 𝒜 2) : B)
        rw [gradedDegreeOneMultiplication_apply, map_mul]
        exact mul_self_nonneg (e u))
  · intro hell0
    apply rankOneBilin_ne_zero f hf
    rw [← hellHankel]
    change gradedHankelMap 𝒜 ell.toLinearMap = 0
    rw [show ell = 0 from hell0]
    rfl
  · intro y hy z hz hsum
    have hyPSD : (gradedHankelMap 𝒜 y.toLinearMap).IsPosSemidef := by
      refine ⟨⟨?_⟩, ⟨?_⟩⟩
      · intro u v
        exact congrArg y (gradedDegreeOneMultiplication_symmetric 𝒜 u v)
      · exact (SOSConeDual.nonnegative_on_sosCone_iff
          (fun u ↦ gradedDegreeOneMultiplication 𝒜 u u) y.toLinearMap).mp hy
    have hzPSD : (gradedHankelMap 𝒜 z.toLinearMap).IsPosSemidef := by
      refine ⟨⟨?_⟩, ⟨?_⟩⟩
      · intro u v
        exact congrArg z (gradedDegreeOneMultiplication_symmetric 𝒜 u v)
      · exact (SOSConeDual.nonnegative_on_sosCone_iff
          (fun u ↦ gradedDegreeOneMultiplication 𝒜 u u) z.toLinearMap).mp hz
    have hyH : gradedHankelMap 𝒜 y.toLinearMap ∈ H :=
      ⟨y.toLinearMap, rfl⟩
    have hzH : gradedHankelMap 𝒜 z.toLinearMap ∈ H :=
      ⟨z.toLinearMap, rfl⟩
    have hformSum : rankOneBilin f =
        gradedHankelMap 𝒜 y.toLinearMap + gradedHankelMap 𝒜 z.toLinearMap := by
      rw [← hellHankel]
      simpa using congrArg
        (fun L : (𝒜 2) →L[ℝ] ℝ ↦ gradedHankelMap 𝒜 L.toLinearMap) hsum
    obtain ⟨a, b, ha, hb, hya, hzb⟩ :=
      hrankExtreme.2.2 _ ⟨hyH, hyPSD⟩ _ ⟨hzH, hzPSD⟩ hformSum
    refine ⟨a, b, ha, hb, ?_, ?_⟩
    · apply ContinuousLinearMap.coe_injective
      apply hinj
      rw [← hellHankel] at hya
      exact hya
    · apply ContinuousLinearMap.coe_injective
      apply hinj
      rw [← hellHankel] at hzb
      exact hzb

/-- The exclusive evaluation/basepoint-free assertion of Theorem 1.1(ii), stated for the
actual graded coordinate-ring evaluations and the actual Hankel radical. -/
theorem theorem1_1_ii_dichotomy
    {B Y : Type*} [NormedCommRing B] [NormedAlgebra ℝ B]
    (𝒜 : ℕ → Submodule ℝ B) [SetLike.GradedMonoid 𝒜]
    [Module.Finite ℝ (𝒜 1)] [Module.Finite ℝ (𝒜 2)]
    (hgenerated : DegreeTwoGeneratedByDegreeOne 𝒜)
    (eval : Y → B →ₐ[ℝ] ℝ)
    (heval₁ : ∀ x, gradedEvaluation 𝒜 (eval x) 1 ≠ 0)
    (ell : (𝒜 2) →L[ℝ] ℝ)
    (hell : SpansExtremeRay
      (dualConeSet
        (SOSConeDual.sosCone (fun u ↦ gradedDegreeOneMultiplication 𝒜 u u) :
          Set (𝒜 2))) ell) :
    Xor
      (∃ x, ∃ b : ℝ, 0 < b ∧ ell = b • gradedEvaluation 𝒜 (eval x) 2)
      (∀ x, ¬ LinearMap.ker (gradedHankelMap 𝒜 ell.toLinearMap) ≤
        LinearMap.ker (gradedEvaluation 𝒜 (eval x) 1).toLinearMap) := by
  let H := gradedHankelSubmodule 𝒜
  let Q := gradedHankelMap 𝒜 ell.toLinearMap
  let ev₁ : Y → (𝒜 1) →ₗ[ℝ] ℝ :=
    fun x ↦ (gradedEvaluation 𝒜 (eval x) 1).toLinearMap
  have hQext : SpansExtremeRay (psdIn H) Q :=
    gradedHankel_extreme_of_functional_extreme 𝒜 hgenerated ell hell
  have hev₁0 : ∀ x, ev₁ x ≠ 0 := by
    intro x hx
    apply heval₁ x
    ext u
    exact LinearMap.congr_fun hx u
  have hevH : ∀ x, rankOneBilin (ev₁ x) ∈ H := by
    intro x
    refine ⟨(gradedEvaluation 𝒜 (eval x) 2).toLinearMap, ?_⟩
    exact gradedHankelMap_gradedEvaluation_eq_rankOne 𝒜 (eval x)
  have hx := extreme_psd_evaluation_xor_basepointFree
    H (gradedHankelSubmodule_isSymm 𝒜) Q hQext ev₁ hev₁0 hevH
  rcases hx with heval | hfree
  · refine Or.inl ⟨?_, ?_⟩
    · obtain ⟨x, b, hb, hQ⟩ := heval.1
      refine ⟨x, b, hb, ?_⟩
      apply ContinuousLinearMap.coe_injective
      apply gradedHankelMap_injective_of_degreeTwoGeneratedByDegreeOne 𝒜 hgenerated
      calc
        gradedHankelMap 𝒜 ell.toLinearMap = Q := rfl
        _ = b • rankOneBilin (ev₁ x) := hQ
        _ = b • gradedHankelMap 𝒜
              (gradedEvaluation 𝒜 (eval x) 2).toLinearMap := by
                rw [gradedHankelMap_gradedEvaluation_eq_rankOne]
        _ = gradedHankelMap 𝒜
              (b • gradedEvaluation 𝒜 (eval x) 2).toLinearMap := by
                change b • gradedHankelMap 𝒜
                    (gradedEvaluation 𝒜 (eval x) 2).toLinearMap =
                  gradedHankelMap 𝒜
                    (b • (gradedEvaluation 𝒜 (eval x) 2).toLinearMap)
                exact ((gradedHankelMap 𝒜).map_smul
                  b (gradedEvaluation 𝒜 (eval x) 2).toLinearMap).symm
    · exact heval.2
  · refine Or.inr ⟨hfree.1, ?_⟩
    intro heval
    apply hfree.2
    obtain ⟨x, b, hb, hellEval⟩ := heval
    refine ⟨x, b, hb, ?_⟩
    calc
      Q = gradedHankelMap 𝒜 ell.toLinearMap := rfl
      _ = gradedHankelMap 𝒜
          (b • gradedEvaluation 𝒜 (eval x) 2).toLinearMap := by rw [hellEval]
      _ = b • gradedHankelMap 𝒜
          (gradedEvaluation 𝒜 (eval x) 2).toLinearMap := by
            change gradedHankelMap 𝒜
                (b • (gradedEvaluation 𝒜 (eval x) 2).toLinearMap) =
              b • gradedHankelMap 𝒜
                (gradedEvaluation 𝒜 (eval x) 2).toLinearMap
            exact (gradedHankelMap 𝒜).map_smul
              b (gradedEvaluation 𝒜 (eval x) 2).toLinearMap
      _ = b • rankOneBilin (ev₁ x) := by
            rw [gradedHankelMap_gradedEvaluation_eq_rankOne]

/-- Restriction of a complex point evaluation to a homogeneous component, regarded as a
real-linear map. -/
def gradedComplexEvaluation
    {B : Type*} [CommRing B] [Algebra ℝ B]
    (𝒜 : ℕ → Submodule ℝ B) (e : B →ₐ[ℝ] ℂ) (d : ℕ) :
    𝒜 d →ₗ[ℝ] ℂ :=
  e.toLinearMap.comp (𝒜 d).subtype

@[simp]
theorem gradedComplexEvaluation_apply
    {B : Type*} [CommRing B] [Algebra ℝ B]
    (𝒜 : ℕ → Submodule ℝ B) (e : B →ₐ[ℝ] ℂ) (d : ℕ) (q : 𝒜 d) :
    gradedComplexEvaluation 𝒜 e d q = e q := by
  rfl

/-- The real part of a complex point evaluation on a homogeneous component. -/
def gradedComplexRealPartEvaluation
    {B : Type*} [CommRing B] [Algebra ℝ B]
    (𝒜 : ℕ → Submodule ℝ B) (e : B →ₐ[ℝ] ℂ) (d : ℕ) :
    𝒜 d →ₗ[ℝ] ℝ :=
  Complex.reCLM.toLinearMap.comp (gradedComplexEvaluation 𝒜 e d)

@[simp]
theorem gradedComplexRealPartEvaluation_apply
    {B : Type*} [CommRing B] [Algebra ℝ B]
    (𝒜 : ℕ → Submodule ℝ B) (e : B →ₐ[ℝ] ℂ) (d : ℕ) (q : 𝒜 d) :
    gradedComplexRealPartEvaluation 𝒜 e d q = (e q).re := by
  rfl

/-- The Hankel form obtained from the real part of a complex point evaluation is the form
`(u,v) ↦ Re(e(u)e(v))` used in the proof of Lemma 4.1. -/
@[simp]
theorem gradedHankelMap_complexRealPartEvaluation_apply
    {B : Type*} [CommRing B] [Algebra ℝ B]
    (𝒜 : ℕ → Submodule ℝ B) [SetLike.GradedMonoid 𝒜]
    (e : B →ₐ[ℝ] ℂ) (u v : 𝒜 1) :
    gradedHankelMap 𝒜 (gradedComplexRealPartEvaluation 𝒜 e 2) u v =
      (e u * e v).re := by
  change (e ((gradedDegreeOneMultiplication 𝒜 u v : 𝒜 2) : B)).re = _
  rw [gradedDegreeOneMultiplication_apply, map_mul]

/-- A complex-valued real-linear evaluation is projectively real when its image is a single
real line in `ℂ`.  Equivalently, after choosing a nonzero complex representative `a`, it is
`a` times a real-valued functional.  This is the coordinate-free degree-one condition that a
complex projective point is fixed by conjugation. -/
def IsProjectivelyReal
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (f : V →ₗ[ℝ] ℂ) : Prop :=
  ∃ a : ℂ, a ≠ 0 ∧ ∃ g : V →ₗ[ℝ] ℝ,
    f = (LinearMap.toSpanSingleton ℝ ℂ a).comp g

/-- The elementary real/nonreal projective dichotomy.  A nonzero real-linear map to `ℂ`
either has one-dimensional real image, hence is projectively real, or has two-dimensional
image and is surjective. -/
theorem isProjectivelyReal_or_surjective
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (f : V →ₗ[ℝ] ℂ) (hf : f ≠ 0) :
    IsProjectivelyReal f ∨ Function.Surjective f := by
  by_cases hs : Function.Surjective f
  · exact Or.inr hs
  left
  have hrange : LinearMap.range f ≠ ⊤ := by
    intro htop
    exact hs (LinearMap.range_eq_top.mp htop)
  have hlt : Module.finrank ℝ (LinearMap.range f) < 2 := by
    simpa [Complex.finrank_real_complex] using Submodule.finrank_lt hrange
  have hex : ∃ u : V, f u ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hf
    ext u
    simpa using hn u
  obtain ⟨u, hu⟩ := hex
  have hpos : 0 < Module.finrank ℝ (LinearMap.range f) := by
    rw [Module.finrank_pos_iff_exists_ne_zero]
    refine ⟨⟨f u, ⟨u, rfl⟩⟩, ?_⟩
    intro hzero
    apply hu
    exact Subtype.ext_iff.mp hzero
  have hfin : Module.finrank ℝ (LinearMap.range f) = 1 := by omega
  have hRange : LinearMap.range f = ℝ ∙ f u :=
    eq_span_singleton_of_mem_of_finrank_eq_one hfin ⟨u, rfl⟩ hu
  let g : V →ₗ[ℝ] ℝ :=
    Complex.reCLM.toLinearMap.comp
      ((Algebra.lmul ℝ ℂ (f u)⁻¹).comp f)
  refine ⟨f u, hu, g, ?_⟩
  ext v
  have hv : f v ∈ ℝ ∙ f u := by
    rw [← hRange]
    exact ⟨v, rfl⟩
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv
  change f v = ((f u)⁻¹ * f v).re • f u
  conv_rhs => rw [← hc]
  have hinv : (f u)⁻¹ * (c • f u) = (c : ℂ) := by
    rw [Complex.real_smul]
    calc
      (f u)⁻¹ * ((c : ℂ) * f u) = (c : ℂ) * ((f u)⁻¹ * f u) := by ring
      _ = c := by simp [hu]
  rw [hinv]
  simpa using hc.symm

/-- The nonreal-point exclusion in Lemma 4.1.  If complex evaluation on degree one has
real rank two (equivalently, is onto `ℂ`), it cannot vanish on the radical of an extreme
positive-semidefinite Hankel form.  The proof is the paper's indefinite-form argument:
`Re(e(u)e(v))` takes the diagonal values `1` and `-1`, whereas the kernel-face criterion
would force it to be proportional to the positive-semidefinite extreme form. -/
theorem extreme_hankel_no_complex_basepoint_of_surjective_evaluation
    {B : Type*} [NormedCommRing B] [NormedAlgebra ℝ B]
    (𝒜 : ℕ → Submodule ℝ B) [SetLike.GradedMonoid 𝒜]
    [Module.Finite ℝ (𝒜 1)] [Module.Finite ℝ (𝒜 2)]
    (hgenerated : DegreeTwoGeneratedByDegreeOne 𝒜)
    (ell : (𝒜 2) →L[ℝ] ℝ)
    (hell : SpansExtremeRay
      (dualConeSet
        (SOSConeDual.sosCone (fun u ↦ gradedDegreeOneMultiplication 𝒜 u u) :
          Set (𝒜 2))) ell)
    (e : B →ₐ[ℝ] ℂ)
    (heSurj : Function.Surjective (gradedComplexEvaluation 𝒜 e 1)) :
    ¬ LinearMap.ker (gradedHankelMap 𝒜 ell.toLinearMap) ≤
      LinearMap.ker (gradedComplexEvaluation 𝒜 e 1) := by
  let H := gradedHankelSubmodule 𝒜
  let Q := gradedHankelMap 𝒜 ell.toLinearMap
  let f := gradedComplexEvaluation 𝒜 e 1
  let rho := gradedComplexRealPartEvaluation 𝒜 e 2
  let P := gradedHankelMap 𝒜 rho
  have hQext : SpansExtremeRay (psdIn H) Q :=
    gradedHankel_extreme_of_functional_extreme 𝒜 hgenerated ell hell
  intro hbase
  have hPH : P ∈ H := ⟨rho, rfl⟩
  have hkerQP : LinearMap.ker Q ≤ LinearMap.ker P := by
    intro w hw
    have hfw : f w = 0 := LinearMap.mem_ker.mp (hbase hw)
    apply LinearMap.mem_ker.mpr
    ext v
    dsimp [P, rho]
    change (e ((gradedDegreeOneMultiplication 𝒜 w v : 𝒜 2) : B)).re = 0
    rw [gradedDegreeOneMultiplication_apply, map_mul]
    have hew : e w = 0 := by simpa [f, gradedComplexEvaluation] using hfw
    simp [hew]
  obtain ⟨a, ha⟩ := kernel_face_unique_of_extreme
    H (gradedHankelSubmodule_isSymm 𝒜) Q hQext P hPH hkerQP
  obtain ⟨u, hu⟩ := heSurj 1
  obtain ⟨v, hv⟩ := heSurj Complex.I
  have hPu : P u u = 1 := by
    dsimp [P, rho]
    change (e ((gradedDegreeOneMultiplication 𝒜 u u : 𝒜 2) : B)).re = 1
    rw [gradedDegreeOneMultiplication_apply, map_mul]
    have heu : e u = 1 := by simpa [f, gradedComplexEvaluation] using hu
    rw [heu]
    norm_num
  have hPv : P v v = -1 := by
    dsimp [P, rho]
    change (e ((gradedDegreeOneMultiplication 𝒜 v v : 𝒜 2) : B)).re = -1
    rw [gradedDegreeOneMultiplication_apply, map_mul]
    have hev : e v = Complex.I := by simpa [f, gradedComplexEvaluation] using hv
    rw [hev]
    norm_num
  have hQu : 0 ≤ Q u u := hQext.1.2.isNonneg.nonneg u
  have hQv : 0 ≤ Q v v := hQext.1.2.isNonneg.nonneg v
  have hEqU : 1 = a * Q u u := by
    rw [← hPu]
    exact LinearMap.congr_fun (LinearMap.congr_fun ha u) u
  have hEqV : -1 = a * Q v v := by
    rw [← hPv]
    exact LinearMap.congr_fun (LinearMap.congr_fun ha v) v
  have haPos : 0 < a := by nlinarith
  nlinarith

/-- Paper-facing nonreal-point form of the complex basepoint exclusion.  Surjectivity is no
longer an input: it follows from the intrinsic assertion that the nonzero degree-one
evaluation is not projectively real. -/
theorem extreme_hankel_no_nonreal_complex_basepoint
    {B : Type*} [NormedCommRing B] [NormedAlgebra ℝ B]
    (𝒜 : ℕ → Submodule ℝ B) [SetLike.GradedMonoid 𝒜]
    [Module.Finite ℝ (𝒜 1)] [Module.Finite ℝ (𝒜 2)]
    (hgenerated : DegreeTwoGeneratedByDegreeOne 𝒜)
    (ell : (𝒜 2) →L[ℝ] ℝ)
    (hell : SpansExtremeRay
      (dualConeSet
        (SOSConeDual.sosCone (fun u ↦ gradedDegreeOneMultiplication 𝒜 u u) :
          Set (𝒜 2))) ell)
    (e : B →ₐ[ℝ] ℂ)
    (he : gradedComplexEvaluation 𝒜 e 1 ≠ 0)
    (heNonreal : ¬ IsProjectivelyReal (gradedComplexEvaluation 𝒜 e 1)) :
    ¬ LinearMap.ker (gradedHankelMap 𝒜 ell.toLinearMap) ≤
      LinearMap.ker (gradedComplexEvaluation 𝒜 e 1) := by
  obtain hreal | hsurj :=
    isProjectivelyReal_or_surjective (gradedComplexEvaluation 𝒜 e 1) he
  · exact False.elim (heNonreal hreal)
  · exact extreme_hankel_no_complex_basepoint_of_surjective_evaluation
      𝒜 hgenerated ell hell e hsurj

/-- The real/complex form of the exclusive dichotomy in Theorem 1.1(ii).  Once the
projectively real complex evaluations are identified with the kernels of the supplied real
evaluations, the basepoint-free branch has no complex projective basepoints: real ones are
excluded by the real dichotomy, and nonreal ones by the indefinite-form argument above. -/
theorem theorem1_1_ii_complexDichotomy_of_realLocus
    {B Y Z : Type*} [NormedCommRing B] [NormedAlgebra ℝ B]
    (𝒜 : ℕ → Submodule ℝ B) [SetLike.GradedMonoid 𝒜]
    [Module.Finite ℝ (𝒜 1)] [Module.Finite ℝ (𝒜 2)]
    (hgenerated : DegreeTwoGeneratedByDegreeOne 𝒜)
    (realEval : Y → B →ₐ[ℝ] ℝ)
    (complexEval : Z → B →ₐ[ℝ] ℂ)
    (hrealEval₁ : ∀ x, gradedEvaluation 𝒜 (realEval x) 1 ≠ 0)
    (hcomplexEval₁ : ∀ z, gradedComplexEvaluation 𝒜 (complexEval z) 1 ≠ 0)
    (hrealLocus : ∀ z,
      IsProjectivelyReal (gradedComplexEvaluation 𝒜 (complexEval z) 1) →
        ∃ x, LinearMap.ker (gradedComplexEvaluation 𝒜 (complexEval z) 1) =
          LinearMap.ker (gradedEvaluation 𝒜 (realEval x) 1).toLinearMap)
    (hcomplexifies : ∀ x, ∃ z,
      LinearMap.ker (gradedComplexEvaluation 𝒜 (complexEval z) 1) =
        LinearMap.ker (gradedEvaluation 𝒜 (realEval x) 1).toLinearMap)
    (ell : (𝒜 2) →L[ℝ] ℝ)
    (hell : SpansExtremeRay
      (dualConeSet
        (SOSConeDual.sosCone (fun u ↦ gradedDegreeOneMultiplication 𝒜 u u) :
          Set (𝒜 2))) ell) :
    Xor
      (∃ x, ∃ b : ℝ, 0 < b ∧ ell = b • gradedEvaluation 𝒜 (realEval x) 2)
      (∀ z, ¬ LinearMap.ker (gradedHankelMap 𝒜 ell.toLinearMap) ≤
        LinearMap.ker (gradedComplexEvaluation 𝒜 (complexEval z) 1)) := by
  rcases theorem1_1_ii_dichotomy 𝒜 hgenerated realEval hrealEval₁ ell hell with
    heval | hfree
  · refine Or.inl ⟨heval.1, ?_⟩
    intro hcomplexFree
    apply heval.2
    intro x
    obtain ⟨z, hz⟩ := hcomplexifies x
    intro hbase
    apply hcomplexFree z
    intro w hw
    have hreal := hbase hw
    rw [← hz] at hreal
    exact hreal
  · refine Or.inr ⟨?_, hfree.2⟩
    intro z hz
    by_cases hreal :
        IsProjectivelyReal (gradedComplexEvaluation 𝒜 (complexEval z) 1)
    · obtain ⟨x, hx⟩ := hrealLocus z hreal
      apply hfree.1 x
      intro w hw
      have hzw := hz hw
      rw [hx] at hzw
      exact hzw
    · exact (extreme_hankel_no_nonreal_complex_basepoint
        𝒜 hgenerated ell hell (complexEval z) (hcomplexEval₁ z) hreal) hz

/-- The dimension-and-rank assertion in the basepoint-free branch of Theorem 1.1(ii), once the
regular degree-one parameters in the actual Hankel kernel have been chosen.  This is the
continuous-functional adapter to the native arithmetically Gorenstein rank theorem; no legacy
Hilbert, reduction, parameter-product, or free-module certificate occurs in its signature. -/
theorem theorem1_1_ii_kernelRank_of_arithmeticallyGorensteinParameters
    {B : Type*} [NormedCommRing B] [NormedAlgebra ℝ B]
    (𝒜 : ℕ → Submodule ℝ B) [SetLike.GradedMonoid 𝒜]
    [Module.Finite ℝ (𝒜 1)] [Module.Finite ℝ (𝒜 2)]
    (hgenerated : DegreeTwoGeneratedByDegreeOne 𝒜)
    {m c : ℕ}
    (ell : (𝒜 2) →L[ℝ] ℝ) (hell : ell ≠ 0)
    (parameters : Fin (m + 1) → 𝒜 1)
    (hparameters : LinearIndependent ℝ parameters)
    (hparametersKernel : ∀ i,
      parameters i ∈ LinearMap.ker (gradedHankelMap 𝒜 ell.toLinearMap))
    (hHilbert : ∀ d,
      (Module.finrank ℝ (𝒜 d) : ℤ) =
        PowerSeries.coeff d (delPezzoHilbertSeries m c))
    (hAG : IsArithmeticallyGorenstein 𝒜 parameters) :
    LinearMap.ker (gradedHankelMap 𝒜 ell.toLinearMap) =
        Submodule.span ℝ (Set.range parameters) ∧
      Module.finrank ℝ
          (LinearMap.ker (gradedHankelMap 𝒜 ell.toLinearMap)) = m + 1 ∧
      (gradedHankelMap 𝒜 ell.toLinearMap).finiteRank = c := by
  exact hankelKernel_eq_parameterSpan_and_rank_of_arithmeticallyGorenstein
    𝒜 hgenerated ell.toLinearMap (by
      intro hellLinear
      apply hell
      apply ContinuousLinearMap.coe_injective
      exact hellLinear)
    parameters hparameters hparametersKernel hHilbert hAG

end DelPezzoBlekherman
