/-
Copyright (c) 2026 Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import DelPezzoBlekherman.Algebra.QuotientMultiplication
import Mathlib.LinearAlgebra.TensorProduct.Submodule

/-!
# Standard-graded degree-two multiplication

This file connects the abstract quotient-pairing rank theorem to canonical multiplication of a
degree-one submodule inside a commutative algebra.
-/

noncomputable section

universe u v

open scoped TensorProduct

namespace ArtinianGorensteinDegreeOneCertificate

variable {K : Type u} {A : Type v}
variable [Field K] [CommRing A] [Algebra K A]

/-- Multiplication of a subspace `U` with itself, valued in the canonical product submodule
`U * U`.  This is the degree-one-to-degree-two multiplication of a standard graded algebra
when its degree-two piece is identified with the span of degree-one products. -/
def submoduleProductMultiplication (U : Submodule K A) :
    U →ₗ[K] U →ₗ[K] (U * U) :=
  (TensorProduct.lift.equiv (.id K) U U (U * U)).symm (Submodule.mulMap' U U)

@[simp]
theorem submoduleProductMultiplication_apply (U : Submodule K A) (x y : U) :
    ((submoduleProductMultiplication U x y : U * U) : A) = (x : A) * (y : A) := by
  simp [submoduleProductMultiplication]

/-- The bilinear map obtained from canonical submodule multiplication linearizes back to
mathlib's tensor multiplication map. -/
theorem tensorProduct_lift_submoduleProductMultiplication (U : Submodule K A) :
    TensorProduct.lift (submoduleProductMultiplication U) = Submodule.mulMap' U U := by
  exact (TensorProduct.lift.equiv (.id K) U U (U * U)).apply_symm_apply
    (Submodule.mulMap' U U)

/-- Canonical degree-one multiplication in a commutative algebra is symmetric. -/
theorem submoduleProductMultiplication_symmetric (U : Submodule K A) :
    ∀ x y, submoduleProductMultiplication U x y = submoduleProductMultiplication U y x := by
  intro x y
  apply Subtype.ext
  simp only [submoduleProductMultiplication_apply]
  exact mul_comm _ _

/-- The tensor-linearized canonical product multiplication is surjective onto `U * U`. -/
theorem tensorProduct_lift_submoduleProductMultiplication_surjective (U : Submodule K A) :
    Function.Surjective (TensorProduct.lift (submoduleProductMultiplication U)) := by
  rw [tensorProduct_lift_submoduleProductMultiplication]
  exact Submodule.mulMap'_surjective U U

/-- Consequently, the PDF's symmetric-square multiplication is automatically surjective onto
the canonical degree-two product submodule of a commutative algebra. -/
theorem symmetricSquare_submoduleProductMultiplication_surjective (U : Submodule K A) :
    Function.Surjective (symmetricSquareMultiplication
      (submoduleProductMultiplication U) (submoduleProductMultiplication_symmetric U)) :=
  symmetricSquareMultiplication_surjective_of_tensorProduct_lift_surjective
    (submoduleProductMultiplication U) (submoduleProductMultiplication_symmetric U)
    (tensorProduct_lift_submoduleProductMultiplication_surjective U)

/-- Canonical multiplication transported from `U * U` to a named degree-two submodule `Q`
identified with that product submodule. -/
def submoduleMultiplicationToDegreeTwo
    (U Q : Submodule K A) (hQ : U * U = Q) : U →ₗ[K] U →ₗ[K] Q :=
  (submoduleProductMultiplication U).compr₂ (LinearEquiv.ofEq (U * U) Q hQ).toLinearMap

@[simp]
theorem submoduleMultiplicationToDegreeTwo_apply
    (U Q : Submodule K A) (hQ : U * U = Q) (x y : U) :
    ((submoduleMultiplicationToDegreeTwo U Q hQ x y : Q) : A) = (x : A) * (y : A) := by
  subst Q
  simp [submoduleMultiplicationToDegreeTwo]

/-- Transport to a named degree-two piece preserves symmetry. -/
theorem submoduleMultiplicationToDegreeTwo_symmetric
    (U Q : Submodule K A) (hQ : U * U = Q) :
    ∀ x y, submoduleMultiplicationToDegreeTwo U Q hQ x y =
      submoduleMultiplicationToDegreeTwo U Q hQ y x := by
  intro x y
  apply Subtype.ext
  simp only [submoduleMultiplicationToDegreeTwo_apply]
  exact mul_comm _ _

/-- If the named degree-two piece is the product of degree one with itself, its symmetric-square
multiplication is surjective. -/
theorem symmetricSquare_submoduleMultiplicationToDegreeTwo_surjective
    (U Q : Submodule K A) (hQ : U * U = Q) :
    Function.Surjective (symmetricSquareMultiplication
      (submoduleMultiplicationToDegreeTwo U Q hQ)
      (submoduleMultiplicationToDegreeTwo_symmetric U Q hQ)) := by
  apply (symmetricSquareMultiplication_surjective_iff_tensorProduct_lift_surjective
    (submoduleMultiplicationToDegreeTwo U Q hQ)
    (submoduleMultiplicationToDegreeTwo_symmetric U Q hQ)).2
  rw [submoduleMultiplicationToDegreeTwo, TensorProduct.lift_compr₂,
    tensorProduct_lift_submoduleProductMultiplication]
  exact (LinearEquiv.ofEq (U * U) Q hQ).surjective.comp
    (Submodule.mulMap'_surjective U U)

/-- Ring-theoretic endpoint for the rank calculation in PDF Theorem 4.3.  For the canonical
multiplication `U × U → U * U` in a commutative algebra, symmetry and degree-two generation
are discharged internally; the remaining algebraic input is exactly the perfect pairing on the
parameter quotient supplied by Proposition 2.2. -/
theorem hankelKernel_eq_parameterSpan_and_rank_of_submoduleProductMultiplication
    (U : Submodule K A)
    [Module.Finite K U]
    (ell : (U * U) →ₗ[K] K) (hell : ell ≠ 0)
    {m c : ℕ}
    (parameters : Fin (m + 1) → U)
    (hparameters : LinearIndependent K parameters)
    (hparametersKernel : ∀ i,
      parameters i ∈ LinearMap.ker ((submoduleProductMultiplication U).compr₂ ell))
    (hAG : ParameterProductPerfectPairingCertificate
      (Submodule.span K (Set.range parameters)) (submoduleProductMultiplication U)
        (submoduleProductMultiplication_symmetric U))
    (hU : Module.finrank K U = m + c + 1) :
    LinearMap.ker ((submoduleProductMultiplication U).compr₂ ell) =
        Submodule.span K (Set.range parameters) ∧
      LinearMap.BilinForm.finiteRank ((submoduleProductMultiplication U).compr₂ ell) = c :=
  hankelKernel_eq_parameterSpan_and_rank_of_parameters_mem_hankelKernel
    (submoduleProductMultiplication U) (submoduleProductMultiplication_symmetric U)
    ell hell (symmetricSquare_submoduleProductMultiplication_surjective U)
    parameters hparameters hparametersKernel hAG hU

/-- Degree-piece form of the ring-theoretic Theorem 4.3 endpoint.  A supplied identification
`U * U = Q` turns the canonical product span into the named degree-two piece, so the original
functional `ell : Q → K` is used without any abstract multiplication or generation hypothesis. -/
theorem hankelKernel_eq_parameterSpan_and_rank_of_degreeTwo_eq_product
    (U Q : Submodule K A) (hQ : U * U = Q)
    [Module.Finite K U]
    (ell : Q →ₗ[K] K) (hell : ell ≠ 0)
    {m c : ℕ}
    (parameters : Fin (m + 1) → U)
    (hparameters : LinearIndependent K parameters)
    (hparametersKernel : ∀ i,
      parameters i ∈ LinearMap.ker ((submoduleMultiplicationToDegreeTwo U Q hQ).compr₂ ell))
    (hAG : ParameterProductPerfectPairingCertificate
      (Submodule.span K (Set.range parameters))
      (submoduleMultiplicationToDegreeTwo U Q hQ)
      (submoduleMultiplicationToDegreeTwo_symmetric U Q hQ))
    (hU : Module.finrank K U = m + c + 1) :
    LinearMap.ker ((submoduleMultiplicationToDegreeTwo U Q hQ).compr₂ ell) =
        Submodule.span K (Set.range parameters) ∧
      LinearMap.BilinForm.finiteRank
        ((submoduleMultiplicationToDegreeTwo U Q hQ).compr₂ ell) = c :=
  hankelKernel_eq_parameterSpan_and_rank_of_parameters_mem_hankelKernel
    (submoduleMultiplicationToDegreeTwo U Q hQ)
    (submoduleMultiplicationToDegreeTwo_symmetric U Q hQ) ell hell
    (symmetricSquare_submoduleMultiplicationToDegreeTwo_surjective U Q hQ)
    parameters hparameters hparametersKernel hAG hU

end ArtinianGorensteinDegreeOneCertificate
