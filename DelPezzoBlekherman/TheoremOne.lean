/-
Copyright (c) 2026 Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import DelPezzoBlekherman.Algebra.NativeGorenstein
import DelPezzoBlekherman.Convexity.DualSlice
import DelPezzoBlekherman.SOS.ClosedCone
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

end DelPezzoBlekherman
