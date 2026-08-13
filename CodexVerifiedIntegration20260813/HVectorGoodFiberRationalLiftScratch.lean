import HVectorGoodFiberFamilyScratch
import CoordinateFiberRationalLiftScratch

noncomputable section

universe u

namespace RealProjectiveCoordinateFiber

variable {C I : Type} {W : Type u} [Fintype I]
variable [CommRing C] [IsDomain C] [Algebra ℝ C]
variable [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

/-- A rational point of a good `(1,c,1)` fiber canonically yields a real algebra point of its
source coordinate ring. -/
noncomputable def hVectorSourceAlgHomOfRationalFiberPoint
    (b : Module.Basis I ℝ W)
    (CC : ℕ → Submodule ℝ C) [GradedRing CC]
    (g : I → C) (hg : ∀ i, g i ∈ CC 1) {c : ℕ}
    (h : let f := MvPolynomial.standardGradedAevalHom CC g hg
      letI := f.toRingHom.toAlgebra
      HVectorOneCOneFreeCertificate ℝ (MvPolynomial I ℝ) C CC c)
    (y : RealProjectiveTopology.Direction W)
    (q : RationalClosedPoint ℝ (hVectorGoodFiber b CC g hg h y)) : C →ₐ[ℝ] ℝ := by
  let f := MvPolynomial.standardGradedAevalHom CC g hg
  let _ : Algebra (MvPolynomial I ℝ) C := f.toRingHom.toAlgebra
  let _ : Module.Finite (MvPolynomial I ℝ) C := Module.Finite.of_basis h.finBasis
  let _ : IsScalarTower ℝ (MvPolynomial I ℝ) C :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      change algebraMap ℝ C r = f.toRingHom (MvPolynomial.C r)
      simp [f, MvPolynomial.standardGradedAevalHom, MvPolynomial.gradedAevalHom,
        MvPolynomial.gradedEval₂Hom]
  exact sourceAlgHomOfRationalFiberPoint
    (MvPolynomial.goodCoordinates
      (RealProjectiveTopology.basisContinuousLinearEquiv b)
      (AlgebraicGeometry.Proj.realHVectorDiscr CC g hg h) y) q

/-- The induced source point lies over the chosen good coordinates. -/
theorem hVectorSourceAlgHomOfRationalFiberPoint_algebraMap
    (b : Module.Basis I ℝ W)
    (CC : ℕ → Submodule ℝ C) [GradedRing CC]
    (g : I → C) (hg : ∀ i, g i ∈ CC 1) {c : ℕ}
    (h : let f := MvPolynomial.standardGradedAevalHom CC g hg
      letI := f.toRingHom.toAlgebra
      HVectorOneCOneFreeCertificate ℝ (MvPolynomial I ℝ) C CC c)
    (y : RealProjectiveTopology.Direction W)
    (q : RationalClosedPoint ℝ (hVectorGoodFiber b CC g hg h y))
    (p : MvPolynomial I ℝ) :
    let f := MvPolynomial.standardGradedAevalHom CC g hg
    hVectorSourceAlgHomOfRationalFiberPoint b CC g hg h y q (f.toRingHom p) =
      MvPolynomial.eval
        (MvPolynomial.goodCoordinates
          (RealProjectiveTopology.basisContinuousLinearEquiv b)
          (AlgebraicGeometry.Proj.realHVectorDiscr CC g hg h) y) p := by
  let f := MvPolynomial.standardGradedAevalHom CC g hg
  let _ : Algebra (MvPolynomial I ℝ) C := f.toRingHom.toAlgebra
  let _ : Module.Finite (MvPolynomial I ℝ) C := Module.Finite.of_basis h.finBasis
  let _ : IsScalarTower ℝ (MvPolynomial I ℝ) C :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      change algebraMap ℝ C r = f.toRingHom (MvPolynomial.C r)
      simp [f, MvPolynomial.standardGradedAevalHom, MvPolynomial.gradedAevalHom,
        MvPolynomial.gradedEval₂Hom]
  exact sourceAlgHomOfRationalFiberPoint_algebraMap
    (MvPolynomial.goodCoordinates
      (RealProjectiveTopology.basisContinuousLinearEquiv b)
      (AlgebraicGeometry.Proj.realHVectorDiscr CC g hg h) y) q p

/-- On the chosen degree-one generators, the induced source point has exactly the affine
coordinates selected for the projective direction. -/
theorem hVectorSourceAlgHomOfRationalFiberPoint_generator
    (b : Module.Basis I ℝ W)
    (CC : ℕ → Submodule ℝ C) [GradedRing CC]
    (g : I → C) (hg : ∀ i, g i ∈ CC 1) {c : ℕ}
    (h : let f := MvPolynomial.standardGradedAevalHom CC g hg
      letI := f.toRingHom.toAlgebra
      HVectorOneCOneFreeCertificate ℝ (MvPolynomial I ℝ) C CC c)
    (y : RealProjectiveTopology.Direction W)
    (q : RationalClosedPoint ℝ (hVectorGoodFiber b CC g hg h y)) (i : I) :
    hVectorSourceAlgHomOfRationalFiberPoint b CC g hg h y q (g i) =
      MvPolynomial.goodCoordinates
        (RealProjectiveTopology.basisContinuousLinearEquiv b)
        (AlgebraicGeometry.Proj.realHVectorDiscr CC g hg h) y i := by
  simpa [MvPolynomial.standardGradedAevalHom, MvPolynomial.gradedAevalHom,
    MvPolynomial.gradedEval₂Hom] using
    hVectorSourceAlgHomOfRationalFiberPoint_algebraMap
      b CC g hg h y q (MvPolynomial.X i)

/-- On the good locus, the generator-value vector of every rational fiber point is nonzero. -/
theorem hVectorSourceAlgHomOfRationalFiberPoint_generator_ne_zero
    (b : Module.Basis I ℝ W)
    (CC : ℕ → Submodule ℝ C) [GradedRing CC]
    (g : I → C) (hg : ∀ i, g i ∈ CC 1) {c : ℕ}
    (h : let f := MvPolynomial.standardGradedAevalHom CC g hg
      letI := f.toRingHom.toAlgebra
      HVectorOneCOneFreeCertificate ℝ (MvPolynomial I ℝ) C CC c)
    {y : RealProjectiveTopology.Direction W} (hy : y ∈ hVectorGoodOmega b CC g hg h)
    (q : RationalClosedPoint ℝ (hVectorGoodFiber b CC g hg h y)) :
    RealProjectiveTopology.basisContinuousLinearEquiv b
      (fun i ↦ hVectorSourceAlgHomOfRationalFiberPoint b CC g hg h y q (g i)) ≠ 0 := by
  have hcoords :
      (fun i ↦ hVectorSourceAlgHomOfRationalFiberPoint b CC g hg h y q (g i)) =
        MvPolynomial.goodCoordinates
          (RealProjectiveTopology.basisContinuousLinearEquiv b)
          (AlgebraicGeometry.Proj.realHVectorDiscr CC g hg h) y := by
    funext i
    exact hVectorSourceAlgHomOfRationalFiberPoint_generator b CC g hg h y q i
  rw [hcoords]
  exact MvPolynomial.goodCoordinates_ne_zero
    (RealProjectiveTopology.basisContinuousLinearEquiv b)
    (AlgebraicGeometry.Proj.realHVectorDiscr CC g hg h) hy

/-- Consequently the generator values recover exactly the original projective direction. -/
theorem directionOf_hVectorSourceAlgHomOfRationalFiberPoint_generators
    (b : Module.Basis I ℝ W)
    (CC : ℕ → Submodule ℝ C) [GradedRing CC]
    (g : I → C) (hg : ∀ i, g i ∈ CC 1) {c : ℕ}
    (h : let f := MvPolynomial.standardGradedAevalHom CC g hg
      letI := f.toRingHom.toAlgebra
      HVectorOneCOneFreeCertificate ℝ (MvPolynomial I ℝ) C CC c)
    {y : RealProjectiveTopology.Direction W} (hy : y ∈ hVectorGoodOmega b CC g hg h)
    (q : RationalClosedPoint ℝ (hVectorGoodFiber b CC g hg h y)) :
    RealProjectiveTopology.directionOf W
      ⟨RealProjectiveTopology.basisContinuousLinearEquiv b
          (fun i ↦ hVectorSourceAlgHomOfRationalFiberPoint b CC g hg h y q (g i)),
        hVectorSourceAlgHomOfRationalFiberPoint_generator_ne_zero b CC g hg h hy q⟩ = y := by
  have hcoords :
      (fun i ↦ hVectorSourceAlgHomOfRationalFiberPoint b CC g hg h y q (g i)) =
        MvPolynomial.goodCoordinates
          (RealProjectiveTopology.basisContinuousLinearEquiv b)
          (AlgebraicGeometry.Proj.realHVectorDiscr CC g hg h) y := by
    funext i
    exact hVectorSourceAlgHomOfRationalFiberPoint_generator b CC g hg h y q i
  simpa only [hcoords] using
    MvPolynomial.directionOf_goodCoordinates
      (RealProjectiveTopology.basisContinuousLinearEquiv b)
      (AlgebraicGeometry.Proj.realHVectorDiscr CC g hg h) hy

end RealProjectiveCoordinateFiber
