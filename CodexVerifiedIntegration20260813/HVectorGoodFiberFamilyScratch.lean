import RealProjectiveCoordinateFiberScratch

noncomputable section

universe u

open Set

namespace RealProjectiveCoordinateFiber

variable {C I : Type} {W : Type u} [Fintype I]
variable [CommRing C] [IsDomain C] [Algebra ℝ C]
variable [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

/-- The projective directions admitting coordinates where the `(1,c,1)` certificate
discriminant does not vanish. -/
def hVectorGoodOmega
    (b : Module.Basis I ℝ W)
    (CC : ℕ → Submodule ℝ C) [GradedRing CC]
    (g : I → C) (hg : ∀ i, g i ∈ CC 1) {c : ℕ}
    (h : let f := MvPolynomial.standardGradedAevalHom CC g hg
      letI := f.toRingHom.toAlgebra
      HVectorOneCOneFreeCertificate ℝ (MvPolynomial I ℝ) C CC c) :
    Set (RealProjectiveTopology.Direction W) :=
  {y | MvPolynomial.HasGoodCoordinates
    (RealProjectiveTopology.basisContinuousLinearEquiv b)
    (AlgebraicGeometry.Proj.realHVectorDiscr CC g hg h) y}

/-- The fiber family evaluated at the chosen good coordinates; outside the good locus the
coordinates are an irrelevant zero fallback. -/
abbrev hVectorGoodFiber
    (b : Module.Basis I ℝ W)
    (CC : ℕ → Submodule ℝ C) [GradedRing CC]
    (g : I → C) (hg : ∀ i, g i ∈ CC 1) {c : ℕ}
    (h : let f := MvPolynomial.standardGradedAevalHom CC g hg
      letI := f.toRingHom.toAlgebra
      HVectorOneCOneFreeCertificate ℝ (MvPolynomial I ℝ) C CC c)
    (y : RealProjectiveTopology.Direction W) : Type :=
  let f := MvPolynomial.standardGradedAevalHom CC g hg
  letI := f.toRingHom.toAlgebra
  fiberAt (C := C) (MvPolynomial.goodCoordinates
    (RealProjectiveTopology.basisContinuousLinearEquiv b)
    (AlgebraicGeometry.Proj.realHVectorDiscr CC g hg h) y)

/-- Basepoint-freeness makes the good-coordinate locus dense. -/
theorem dense_hVectorGoodOmega
    (b : Module.Basis I ℝ W)
    (CC : ℕ → Submodule ℝ C) [GradedRing CC]
    (g : I → C) (hg : ∀ i, g i ∈ CC 1)
    (hbasepointFree : (HomogeneousIdeal.irrelevant CC).toIdeal ≤
      (Ideal.span (Set.range g)).radical)
    {c : ℕ}
    (h : let f := MvPolynomial.standardGradedAevalHom CC g hg
      letI := f.toRingHom.toAlgebra
      HVectorOneCOneFreeCertificate ℝ (MvPolynomial I ℝ) C CC c) :
    Dense (hVectorGoodOmega b CC g hg h) := by
  apply MvPolynomial.dense_setOf_hasGoodCoordinates
  exact AlgebraicGeometry.Proj.realHVectorDiscr_ne_zero
    CC g hg hbasepointFree h

/-- Every good-coordinate fiber has rank `c+2`, including outside the dense locus. -/
theorem hVectorGoodFiber_finrank_eq_add_two
    (b : Module.Basis I ℝ W)
    (CC : ℕ → Submodule ℝ C) [GradedRing CC]
    (g : I → C) (hg : ∀ i, g i ∈ CC 1) {c : ℕ}
    (h : let f := MvPolynomial.standardGradedAevalHom CC g hg
      letI := f.toRingHom.toAlgebra
      HVectorOneCOneFreeCertificate ℝ (MvPolynomial I ℝ) C CC c)
    (y : RealProjectiveTopology.Direction W) :
    Module.finrank ℝ (hVectorGoodFiber b CC g hg h y) = c + 2 := by
  let f := MvPolynomial.standardGradedAevalHom CC g hg
  let _ : Algebra (MvPolynomial I ℝ) C := f.toRingHom.toAlgebra
  simpa using fiberAt_finrank_eq_card h.finBasis
    (MvPolynomial.goodCoordinates
      (RealProjectiveTopology.basisContinuousLinearEquiv b)
      (AlgebraicGeometry.Proj.realHVectorDiscr CC g hg h) y)

/-- Fibers over the dense good-coordinate locus are reduced. -/
theorem hVectorGoodFiber_isReduced
    (b : Module.Basis I ℝ W)
    (CC : ℕ → Submodule ℝ C) [GradedRing CC]
    (g : I → C) (hg : ∀ i, g i ∈ CC 1) {c : ℕ}
    (h : let f := MvPolynomial.standardGradedAevalHom CC g hg
      letI := f.toRingHom.toAlgebra
      HVectorOneCOneFreeCertificate ℝ (MvPolynomial I ℝ) C CC c)
    (y : RealProjectiveTopology.Direction W) (hy : y ∈ hVectorGoodOmega b CC g hg h) :
    IsReduced (hVectorGoodFiber b CC g hg h y) := by
  let f := MvPolynomial.standardGradedAevalHom CC g hg
  let _ : Algebra (MvPolynomial I ℝ) C := f.toRingHom.toAlgebra
  apply fiberAt_isReduced_of_eval_discr_ne_zero h.finBasis
  exact MvPolynomial.eval_goodCoordinates_ne_zero
    (RealProjectiveTopology.basisContinuousLinearEquiv b)
    (AlgebraicGeometry.Proj.realHVectorDiscr CC g hg h) hy

end RealProjectiveCoordinateFiber
