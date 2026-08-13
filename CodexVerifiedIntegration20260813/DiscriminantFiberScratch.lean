import ReducedFiberScratch
import Mathlib.RingTheory.Discriminant

noncomputable section

universe u v w

namespace Algebra

open Module

variable {R : Type u} {S : Type v} {A : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [CommRing A] [Algebra R A]

/-- The discriminant of a finite free algebra basis commutes with arbitrary base change. -/
theorem map_discr_eq_discr_tensorProduct_basis
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι R S) :
    algebraMap R A (discr R b) = discr A (TensorProduct.basis A b) := by
  let _ : Module.Free R S := Module.Free.of_basis b
  let _ : Module.Finite R S := Module.Finite.of_basis b
  rw [discr_def, discr_def, traceMatrix_of_basis, traceMatrix_of_basis]
  rw [RingHom.map_det]
  apply congrArg Matrix.det
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, traceForm_toMatrix,
    TensorProduct.basis_apply]
  rw [Algebra.trace_apply, Algebra.trace_apply]
  rw [← LinearMap.trace_baseChange (Algebra.lmul R S (b i * b j)) A]
  rw [Algebra.baseChange_lmul]
  congr 1
  simp

end Algebra

namespace Ideal

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- A fiber of a finite free algebra is reduced away from the discriminant of a basis. -/
theorem isReduced_fiber_of_discr_not_mem
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R S) (p : Ideal R) [p.IsPrime]
    (hdisc : Algebra.discr R b ∉ p) : _root_.IsReduced (p.Fiber S) := by
  apply Algebra.isReduced_of_det_traceForm_ne_zero
    (Algebra.TensorProduct.basis p.ResidueField b)
  rw [← Algebra.traceMatrix_of_basis, ← Algebra.discr_def]
  rw [← Algebra.map_discr_eq_discr_tensorProduct_basis b]
  simpa only [ne_eq, Ideal.algebraMap_residueField_eq_zero]

/-- Over a domain, a nonzero discriminant certifies that the generic fiber is reduced. -/
theorem isReduced_genericFiber_of_discr_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [IsDomain R] (b : Module.Basis ι R S)
    (hdisc : Algebra.discr R b ≠ 0) :
    _root_.IsReduced ((⊥ : Ideal R).Fiber S) := by
  apply isReduced_fiber_of_discr_not_mem b ⊥
  simpa

/-- If the generic fiber is a separable field extension, then the discriminant of every finite
basis is nonzero.  This turns generic separability into the concrete principal-open certificate
used by `isReduced_fiber_of_discr_not_mem`. -/
theorem discr_ne_zero_of_genericFiber_isSeparable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [IsDomain R] (b : Module.Basis ι R S)
    (hfield : IsField ((⊥ : Ideal R).Fiber S))
    (hsep : letI : Algebra (⊥ : Ideal R).ResidueField ((⊥ : Ideal R).Fiber S) :=
        Algebra.TensorProduct.leftAlgebra
      Algebra.IsSeparable (⊥ : Ideal R).ResidueField ((⊥ : Ideal R).Fiber S)) :
    Algebra.discr R b ≠ 0 := by
  let _ : Algebra (⊥ : Ideal R).ResidueField ((⊥ : Ideal R).Fiber S) :=
    Algebra.TensorProduct.leftAlgebra
  let _ : Field ((⊥ : Ideal R).Fiber S) := IsField.toField hfield
  let _ : Algebra.IsSeparable (⊥ : Ideal R).ResidueField ((⊥ : Ideal R).Fiber S) := hsep
  let bg := Algebra.TensorProduct.basis (⊥ : Ideal R).ResidueField b
  let _ : Module.Finite (⊥ : Ideal R).ResidueField ((⊥ : Ideal R).Fiber S) :=
    Module.Finite.of_basis bg
  intro hzero
  have hgeneric := Algebra.discr_not_zero_of_basis
    (K := (⊥ : Ideal R).ResidueField)
    (L := (⊥ : Ideal R).Fiber S)
    bg
  apply hgeneric
  rw [← Algebra.map_discr_eq_discr_tensorProduct_basis b, hzero, map_zero]

/-- A generically separable finite free domain algebra has reduced generic fiber. -/
theorem isReduced_genericFiber_of_isSeparable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [IsDomain R] (b : Module.Basis ι R S)
    (hfield : IsField ((⊥ : Ideal R).Fiber S))
    (hsep : letI : Algebra (⊥ : Ideal R).ResidueField ((⊥ : Ideal R).Fiber S) :=
        Algebra.TensorProduct.leftAlgebra
      Algebra.IsSeparable (⊥ : Ideal R).ResidueField ((⊥ : Ideal R).Fiber S)) :
    _root_.IsReduced ((⊥ : Ideal R).Fiber S) :=
  isReduced_genericFiber_of_discr_ne_zero b
    (discr_ne_zero_of_genericFiber_isSeparable b hfield hsep)

/-- In characteristic zero, the separability assumption in the preceding theorem follows from
finite dimensionality.  Thus it is enough to know that the generic fiber is a field. -/
theorem discr_ne_zero_of_genericFiber_isField_of_charZero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [IsDomain R] [CharZero R] (b : Module.Basis ι R S)
    (hfield : IsField ((⊥ : Ideal R).Fiber S)) :
    Algebra.discr R b ≠ 0 := by
  let _ : Algebra (⊥ : Ideal R).ResidueField ((⊥ : Ideal R).Fiber S) :=
    Algebra.TensorProduct.leftAlgebra
  let _ : Field ((⊥ : Ideal R).Fiber S) := IsField.toField hfield
  let bg := Algebra.TensorProduct.basis (⊥ : Ideal R).ResidueField b
  let _ : Module.Finite (⊥ : Ideal R).ResidueField ((⊥ : Ideal R).Fiber S) :=
    Module.Finite.of_basis bg
  let _ : FaithfulSMul R (⊥ : Ideal R).ResidueField :=
    (faithfulSMul_iff_algebraMap_injective R (⊥ : Ideal R).ResidueField).mpr <| by
      rw [RingHom.injective_iff_ker_eq_bot, Ideal.ker_algebraMap_residueField]
  let _ : CharZero (⊥ : Ideal R).ResidueField :=
    Algebra.charZero_of_charZero R (⊥ : Ideal R).ResidueField
  have hsep : Algebra.IsSeparable (⊥ : Ideal R).ResidueField
      ((⊥ : Ideal R).Fiber S) := inferInstance
  exact discr_ne_zero_of_genericFiber_isSeparable b hfield hsep

/-- Characteristic-zero finite free domain algebras with field generic fiber are generically
reduced. -/
theorem isReduced_genericFiber_of_isField_of_charZero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [IsDomain R] [CharZero R] (b : Module.Basis ι R S)
    (hfield : IsField ((⊥ : Ideal R).Fiber S)) :
    _root_.IsReduced ((⊥ : Ideal R).Fiber S) :=
  isReduced_genericFiber_of_discr_ne_zero b
    (discr_ne_zero_of_genericFiber_isField_of_charZero b hfield)

end Ideal

namespace IsArtinianRing

/-- A real algebra with a basis of size `c + 2` and nonzero discriminant is reduced of length
`c + 2`.  If it has at most one quadratic closed point, its closed points therefore satisfy the
fully-real/one-conjugate-pair dichotomy. -/
theorem real_fiber_count_dichotomy_of_basis_discr_ne_zero
    {A : Type u} [CommRing A] [Algebra ℝ A]
    {c : ℕ} (b : Module.Basis (Fin (c + 2)) ℝ A)
    (hdisc : Algebra.discr ℝ b ≠ 0)
    (hpairs : Nat.card (QuadraticClosedPoint ℝ A) ≤ 1) :
    (Nat.card (QuadraticClosedPoint ℝ A) = 0 ∧
        Nat.card (MaximalSpectrum A) = c + 2) ∨
      (Nat.card (QuadraticClosedPoint ℝ A) = 1 ∧
        Nat.card (MaximalSpectrum A) = c + 1) := by
  let _ : Module.Finite ℝ A := Module.Finite.of_basis b
  have hdet : ((Algebra.traceForm ℝ A).toMatrix b).det ≠ 0 := by
    rw [← Algebra.traceMatrix_of_basis, ← Algebra.discr_def]
    exact hdisc
  apply real_fiber_count_dichotomy_of_det_traceForm_ne_zero b hdet
  · simpa using Module.finrank_eq_card_basis b
  · exact hpairs

/-- Real-point version: the same hypotheses give either `c + 2` real points, or `c` real
points and one nonreal conjugate pair. -/
theorem real_fiber_rational_point_dichotomy_of_basis_discr_ne_zero
    {A : Type u} [CommRing A] [Algebra ℝ A]
    {c : ℕ} (b : Module.Basis (Fin (c + 2)) ℝ A)
    (hdisc : Algebra.discr ℝ b ≠ 0)
    (hpairs : Nat.card (QuadraticClosedPoint ℝ A) ≤ 1) :
    (Nat.card (QuadraticClosedPoint ℝ A) = 0 ∧
        Nat.card (RationalClosedPoint ℝ A) = c + 2) ∨
      (Nat.card (QuadraticClosedPoint ℝ A) = 1 ∧
        Nat.card (RationalClosedPoint ℝ A) = c) := by
  let _ : Module.Finite ℝ A := Module.Finite.of_basis b
  let _ : IsReduced A := by
    apply Algebra.isReduced_of_det_traceForm_ne_zero b
    rw [← Algebra.traceMatrix_of_basis, ← Algebra.discr_def]
    exact hdisc
  apply real_reduced_fiber_rational_point_dichotomy
  · simpa using Module.finrank_eq_card_basis b
  · exact hpairs

end IsArtinianRing
