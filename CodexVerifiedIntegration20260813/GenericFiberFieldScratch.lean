import DiscriminantFiberScratch
import Mathlib.RingTheory.Localization.BaseChange

noncomputable section

open scoped TensorProduct

universe u

namespace Ideal

/-- The generic fiber of an injective finite map of integral domains is a field.  Indeed it is
the localization of the target domain at the nonzero elements coming from the source, and it is
finite-dimensional over the source fraction field. -/
theorem isField_genericFiber_of_finite_of_isDomain
    {R S : Type u} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [Algebra R S] [FaithfulSMul R S] [Module.Finite R S] :
    IsField ((⊥ : Ideal R).Fiber S) := by
  let M : Submonoid R := nonZeroDivisors R
  let T := Localization (Algebra.algebraMapSubmonoid S M)
  have hM : Algebra.algebraMapSubmonoid S M ≤ nonZeroDivisors S := by
    rintro y ⟨x, hx, rfl⟩
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro hzero
    apply mem_nonZeroDivisors_iff_ne_zero.mp hx
    apply FaithfulSMul.algebraMap_injective R S
    simpa using hzero
  let _ : IsDomain T := IsLocalization.isDomain_of_le_nonZeroDivisors T hM
  let eR : (⊥ : Ideal R).ResidueField ≃ₐ[R] Localization M :=
    IsLocalization.algEquiv M _ _
  let e₁ : (⊥ : Ideal R).Fiber S ≃ₐ[R] (Localization M ⊗[R] S) :=
    Algebra.TensorProduct.congr eR (AlgEquiv.refl)
  let e₂ : (Localization M ⊗[R] S) ≃ₐ[R] T :=
    (Localization.tensorRightAlgEquiv M S).restrictScalars R
  let e := e₁.trans e₂
  let _ : IsDomain ((⊥ : Ideal R).Fiber S) :=
    e.toRingEquiv.isDomain_iff.mpr inferInstance
  exact IsField.of_isDomain_of_finite (⊥ : Ideal R).ResidueField
    ((⊥ : Ideal R).Fiber S)

/-- In characteristic zero, an injective finite map of integral domains therefore has nonzero
discriminant for every finite basis. -/
theorem discr_ne_zero_of_finite_of_isDomain_of_charZero
    {R S : Type u} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [CharZero R] [Algebra R S] [FaithfulSMul R S]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R S) :
    Algebra.discr R b ≠ 0 := by
  let _ : Module.Finite R S := Module.Finite.of_basis b
  exact discr_ne_zero_of_genericFiber_isField_of_charZero b
    (isField_genericFiber_of_finite_of_isDomain (R := R) (S := S))

end Ideal
