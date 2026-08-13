import HVectorGoodFiberFamilyScratch
import RealFiberComplexBlockFamilyScratch

noncomputable section

universe u

namespace RealProjectiveCoordinateFiber

variable {C I : Type} {W : Type u} [Fintype I]
variable [CommRing C] [IsDomain C] [Algebra ℝ C]
variable [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

/-- For the concrete `(1,c,1)` coordinate fibers, the normalized complex-block calculation
reduces the quadratic closed-point bound to nonnegativity on the normalized relation kernel and
non-isotropy of each individual block. -/
theorem hVectorGoodFiber_pairCount_le_one_of_normalizedComplexBlocks
    (b : Module.Basis I ℝ W)
    (CC : ℕ → Submodule ℝ C) [GradedRing CC]
    (g : I → C) (hg : ∀ i, g i ∈ CC 1) {c : ℕ}
    (h : let f := MvPolynomial.standardGradedAevalHom CC g hg
      letI := f.toRingHom.toAlgebra
      HVectorOneCOneFreeCertificate ℝ (MvPolynomial I ℝ) C CC c)
    [∀ y, Fintype (QuadraticClosedPoint ℝ (hVectorGoodFiber b CC g hg h y))]
    [∀ y, DecidableEq (QuadraticClosedPoint ℝ (hVectorGoodFiber b CC g hg h y))]
    (coeff : ∀ y, QuadraticClosedPoint ℝ (hVectorGoodFiber b CC g hg h y) → ℂ)
    (hnonneg : ∀ y ∈ hVectorGoodOmega b CC g hg h, ∀ z,
      QuadraticForm.NonrealPairNegativeDirections.complexRelationOne z = 0 →
      0 ≤ QuadraticForm.NonrealPairNegativeDirections.complexBlockForm (coeff y) z)
    (hnonisotropic : ∀ y ∈ hVectorGoodOmega b CC g hg h, ∀ p,
      QuadraticForm.NonrealPairNegativeDirections.complexBlockForm (coeff y)
        (Pi.single p Complex.I) ≠ 0) :
    ∀ y ∈ hVectorGoodOmega b CC g hg h,
      RealFiberFamily.pairCount (hVectorGoodFiber b CC g hg h) y ≤ 1 :=
  RealFiberFamily.pairCount_le_one_of_normalizedComplexBlocks
    (hVectorGoodFiber b CC g hg h) (hVectorGoodOmega b CC g hg h)
    coeff hnonneg hnonisotropic

end RealProjectiveCoordinateFiber
