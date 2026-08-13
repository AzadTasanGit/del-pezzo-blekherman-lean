import DelPezzoBlekherman.Geometry.RealProjective.CoordinateFiber
import DelPezzoBlekherman.Fiber.RationalPointLift

noncomputable section

namespace RealProjectiveCoordinateFiber

variable {I C : Type}

/-- A rational closed point of a coordinate fiber restricts along the right tensor factor to an
actual real algebra point of the source coordinate ring. -/
noncomputable def sourceAlgHomOfRationalFiberPoint
    [CommRing C] [Algebra ℝ C] [Algebra (MvPolynomial I ℝ) C]
    [Module.Finite (MvPolynomial I ℝ) C]
    [IsScalarTower ℝ (MvPolynomial I ℝ) C]
    (x : I → ℝ) (q : RationalClosedPoint ℝ (fiberAt (C := C) x)) : C →ₐ[ℝ] ℝ := by
  let _ : Algebra (MvPolynomial I ℝ) ℝ := (evaluationHomAt x).toAlgebra
  let includeC : C →ₐ[ℝ] fiberAt (C := C) x :=
    { toRingHom := Algebra.TensorProduct.includeRight.toRingHom
      commutes' := by
        intro r
        change 1 ⊗ₜ[MvPolynomial I ℝ] (algebraMap ℝ C) r =
          r ⊗ₜ[MvPolynomial I ℝ] 1
        have hleft : (MvPolynomial.C r : MvPolynomial I ℝ) • (1 : ℝ) = r := by
          change evaluationHomAt x (MvPolynomial.C r) * 1 = r
          simp [evaluationHomAt]
        have hright : (MvPolynomial.C r : MvPolynomial I ℝ) • (1 : C) =
            (algebraMap ℝ C) r := by
          rw [Algebra.smul_def, mul_one]
          simpa using
            (IsScalarTower.algebraMap_apply ℝ (MvPolynomial I ℝ) C r).symm
        simpa only [hleft, hright] using
          (TensorProduct.smul_tmul (R := MvPolynomial I ℝ)
            (R' := MvPolynomial I ℝ) (MvPolynomial.C r) (1 : ℝ) (1 : C)).symm }
  exact (RationalClosedPoint.algHom q).comp includeC

/-- The source point obtained from a rational fiber point lies over the affine coordinates used
to form the fiber: its restriction to every polynomial parameter is exactly evaluation at `x`. -/
theorem sourceAlgHomOfRationalFiberPoint_algebraMap
    [CommRing C] [Algebra ℝ C] [Algebra (MvPolynomial I ℝ) C]
    [Module.Finite (MvPolynomial I ℝ) C]
    [IsScalarTower ℝ (MvPolynomial I ℝ) C]
    (x : I → ℝ) (q : RationalClosedPoint ℝ (fiberAt (C := C) x))
    (p : MvPolynomial I ℝ) :
    sourceAlgHomOfRationalFiberPoint x q (algebraMap (MvPolynomial I ℝ) C p) =
      evaluationHomAt x p := by
  let _ : Algebra (MvPolynomial I ℝ) ℝ := (evaluationHomAt x).toAlgebra
  change RationalClosedPoint.algHom q
      (1 ⊗ₜ[MvPolynomial I ℝ] algebraMap (MvPolynomial I ℝ) C p) =
    evaluationHomAt x p
  have hleft : p • (1 : ℝ) = evaluationHomAt x p := by
    rw [Algebra.smul_def, mul_one]
    rfl
  have hright : p • (1 : C) = algebraMap (MvPolynomial I ℝ) C p := by
    rw [Algebra.smul_def, mul_one]
  have htensor :
      (evaluationHomAt x p) ⊗ₜ[MvPolynomial I ℝ] (1 : C) =
        (1 : ℝ) ⊗ₜ[MvPolynomial I ℝ] algebraMap (MvPolynomial I ℝ) C p := by
    simpa only [hleft, hright] using
      TensorProduct.smul_tmul (R := MvPolynomial I ℝ)
        (R' := MvPolynomial I ℝ) p (1 : ℝ) (1 : C)
  rw [← htensor]
  change RationalClosedPoint.algHom q
      (algebraMap ℝ (fiberAt (C := C) x) (evaluationHomAt x p)) =
    evaluationHomAt x p
  exact (RationalClosedPoint.algHom q).commutes _

end RealProjectiveCoordinateFiber
