import HVectorRealDensityScratch
import ProjectiveGoodCoordinatesScratch
import Mathlib.RingTheory.QuasiFinite.Basic

noncomputable section

universe u

namespace RealProjectiveCoordinateFiber

variable {I W C : Type} [Fintype I]
variable [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
variable (b : Module.Basis I ℝ W)

/-- The real evaluation homomorphism at arbitrary affine coordinates. -/
def evaluationHomAt (x : I → ℝ) : MvPolynomial I ℝ →+* ℝ :=
  MvPolynomial.eval₂Hom (RingHom.id ℝ) x

/-- The coordinate-ring fiber algebra formed by base change at arbitrary affine coordinates. -/
abbrev fiberAt
    [CommRing C] [Algebra (MvPolynomial I ℝ) C]
    (x : I → ℝ) : Type :=
  letI := (evaluationHomAt x).toAlgebra
  TensorProduct (MvPolynomial I ℝ) ℝ C

/-- Coordinates of the chosen unit representative of a real projective direction. -/
def coordinates (y : RealProjectiveTopology.Direction W) : I → ℝ :=
  b.equivFun ((Quotient.out y : RealProjectiveTopology.unitSphereAction W) : W)

/-- The real evaluation homomorphism at the chosen representative. -/
def evaluationHom (y : RealProjectiveTopology.Direction W) : MvPolynomial I ℝ →+* ℝ :=
  evaluationHomAt (coordinates b y)

/-- The coordinate-ring fiber algebra over a chosen real projective direction, formed by base
change along its evaluation homomorphism. -/
abbrev fiber
    [CommRing C] [Algebra (MvPolynomial I ℝ) C]
    (y : RealProjectiveTopology.Direction W) : Type :=
  letI := (evaluationHom b y).toAlgebra
  TensorProduct (MvPolynomial I ℝ) ℝ C

section Instances

variable [CommRing C] [Algebra (MvPolynomial I ℝ) C]

example (y : RealProjectiveTopology.Direction W) : CommRing (fiber (C := C) b y) := inferInstance

example (y : RealProjectiveTopology.Direction W) : Algebra ℝ (fiber (C := C) b y) := inferInstance

example [Module.Finite (MvPolynomial I ℝ) C]
    (y : RealProjectiveTopology.Direction W) : Module.Finite ℝ (fiber (C := C) b y) := inferInstance

end Instances

section ArbitraryCoordinates

variable [CommRing C] [Algebra (MvPolynomial I ℝ) C]
variable {iota : Type*} [Fintype iota] [DecidableEq iota]

/-- Base change transports a polynomial-module basis to the fiber at arbitrary coordinates. -/
def fiberBasisAt (basisC : Module.Basis iota (MvPolynomial I ℝ) C)
    (x : I → ℝ) : Module.Basis iota ℝ (fiberAt (C := C) x) := by
  let _ : Algebra (MvPolynomial I ℝ) ℝ := (evaluationHomAt x).toAlgebra
  exact Algebra.TensorProduct.basis ℝ basisC

omit [Fintype I] [FiniteDimensional ℝ W] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [DecidableEq iota] in
/-- Every arbitrary-coordinate fiber has the rank of the supplied polynomial-module basis. -/
theorem fiberAt_finrank_eq_card (basisC : Module.Basis iota (MvPolynomial I ℝ) C)
    (x : I → ℝ) :
    Module.finrank ℝ (fiberAt (C := C) x) = Fintype.card iota :=
  Module.finrank_eq_card_basis (fiberBasisAt basisC x)

omit [Fintype I] [FiniteDimensional ℝ W] [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- A nonzero evaluated discriminant makes an arbitrary-coordinate fiber reduced. -/
theorem fiberAt_isReduced_of_eval_discr_ne_zero
    (basisC : Module.Basis iota (MvPolynomial I ℝ) C) (x : I → ℝ)
    (hdisc : evaluationHomAt x (Algebra.discr (MvPolynomial I ℝ) basisC) ≠ 0) :
    IsReduced (fiberAt (C := C) x) := by
  let _ : Algebra (MvPolynomial I ℝ) ℝ := (evaluationHomAt x).toAlgebra
  apply Algebra.isReduced_of_det_traceForm_ne_zero (fiberBasisAt basisC x)
  rw [← Algebra.traceMatrix_of_basis, ← Algebra.discr_def]
  change Algebra.discr ℝ (Algebra.TensorProduct.basis ℝ basisC) ≠ 0
  rw [← Algebra.map_discr_eq_discr_tensorProduct_basis basisC]
  exact hdisc

end ArbitraryCoordinates

section Basis

variable [CommRing C] [Algebra (MvPolynomial I ℝ) C]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Base change transports a polynomial-module basis to every real projective coordinate fiber. -/
def fiberBasis (basisC : Module.Basis ι (MvPolynomial I ℝ) C)
    (y : RealProjectiveTopology.Direction W) : Module.Basis ι ℝ (fiber (C := C) b y) := by
  let _ : Algebra (MvPolynomial I ℝ) ℝ := (evaluationHom b y).toAlgebra
  exact Algebra.TensorProduct.basis ℝ basisC

omit [FiniteDimensional ℝ W] [DecidableEq ι] in
/-- Every coordinate fiber has the same rank as the supplied polynomial-module basis. -/
theorem fiber_finrank_eq_card (basisC : Module.Basis ι (MvPolynomial I ℝ) C)
    (y : RealProjectiveTopology.Direction W) :
    Module.finrank ℝ (fiber (C := C) b y) = Fintype.card ι :=
  Module.finrank_eq_card_basis (fiberBasis b basisC y)

omit [FiniteDimensional ℝ W] in
/-- Nonvanishing of the evaluated algebra discriminant makes the corresponding real coordinate
fiber reduced. -/
theorem fiber_isReduced_of_eval_discr_ne_zero
    (basisC : Module.Basis ι (MvPolynomial I ℝ) C)
    (y : RealProjectiveTopology.Direction W)
    (hdisc : evaluationHom b y (Algebra.discr (MvPolynomial I ℝ) basisC) ≠ 0) :
    IsReduced (fiber (C := C) b y) := by
  let _ : Algebra (MvPolynomial I ℝ) ℝ := (evaluationHom b y).toAlgebra
  apply Algebra.isReduced_of_det_traceForm_ne_zero (fiberBasis b basisC y)
  rw [← Algebra.traceMatrix_of_basis, ← Algebra.discr_def]
  change Algebra.discr ℝ (Algebra.TensorProduct.basis ℝ basisC) ≠ 0
  rw [← Algebra.map_discr_eq_discr_tensorProduct_basis basisC]
  exact hdisc

end Basis

section HVector

variable [CommRing C] [IsDomain C] [Algebra ℝ C]

omit [FiniteDimensional ℝ W] [IsDomain C] in
/-- The `(1,c,1)` certificate gives every real coordinate fiber rank `c+2`. -/
theorem hVector_fiber_finrank_eq_add_two
    (𝒞 : ℕ → Submodule ℝ C) [GradedRing 𝒞]
    (g : I → C) (hg : ∀ i, g i ∈ 𝒞 1) {c : ℕ}
    (h : let f := MvPolynomial.standardGradedAevalHom 𝒞 g hg
      letI := f.toRingHom.toAlgebra
      HVectorOneCOneFreeCertificate ℝ (MvPolynomial I ℝ) C 𝒞 c)
    (y : RealProjectiveTopology.Direction W) :
    let f := MvPolynomial.standardGradedAevalHom 𝒞 g hg
    letI := f.toRingHom.toAlgebra
    Module.finrank ℝ (fiber (C := C) b y) = c + 2 := by
  let f := MvPolynomial.standardGradedAevalHom 𝒞 g hg
  let _ : Algebra (MvPolynomial I ℝ) C := f.toRingHom.toAlgebra
  simpa using fiber_finrank_eq_card b h.finBasis y

omit [FiniteDimensional ℝ W] in
/-- Nonvanishing of the certificate discriminant at a chosen representative makes the
corresponding `(1,c,1)` coordinate fiber reduced. -/
theorem hVector_fiber_isReduced
    (𝒞 : ℕ → Submodule ℝ C) [GradedRing 𝒞]
    (g : I → C) (hg : ∀ i, g i ∈ 𝒞 1) {c : ℕ}
    (h : let f := MvPolynomial.standardGradedAevalHom 𝒞 g hg
      letI := f.toRingHom.toAlgebra
      HVectorOneCOneFreeCertificate ℝ (MvPolynomial I ℝ) C 𝒞 c)
    (y : RealProjectiveTopology.Direction W)
    (hdisc : evaluationHom b y
      (AlgebraicGeometry.Proj.realHVectorDiscr 𝒞 g hg h) ≠ 0) :
    let f := MvPolynomial.standardGradedAevalHom 𝒞 g hg
    letI := f.toRingHom.toAlgebra
    IsReduced (fiber (C := C) b y) := by
  let f := MvPolynomial.standardGradedAevalHom 𝒞 g hg
  let _ : Algebra (MvPolynomial I ℝ) C := f.toRingHom.toAlgebra
  exact fiber_isReduced_of_eval_discr_ne_zero b h.finBasis y hdisc

end HVector

end RealProjectiveCoordinateFiber
