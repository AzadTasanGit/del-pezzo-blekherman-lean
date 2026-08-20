import DelPezzoBlekherman.Algebra.SoclePairing
import Mathlib.LinearAlgebra.Quotient.Bilinear
import Mathlib.LinearAlgebra.TensorProduct.Basic

noncomputable section

universe u v w

open LinearMap
open scoped TensorProduct

namespace ArtinianGorensteinDegreeOneCertificate

variable {K : Type u} {U : Type v} {Q : Type w}
variable [Field K] [AddCommGroup U] [Module K U]
variable [AddCommGroup Q] [Module K Q]

/-- Multiplication followed by the degree-two quotient map.  This is the ambient bilinear map
whose two arguments will subsequently descend modulo the parameter space. -/
def multiplicationToQuotient
    (J : Submodule K Q) (mul : U →ₗ[K] U →ₗ[K] Q) :
    U →ₗ[K] U →ₗ[K] (Q ⧸ J) :=
  mul.compr₂ J.mkQ

/-- The left kernel condition needed to descend multiplication modulo `W`.  It follows exactly
from the assertion that every product of an element of `W` with a degree-one element lies in
the degree-two relation space `J`. -/
theorem parameterSpace_le_ker_multiplicationToQuotient
    (W : Submodule K U) (J : Submodule K Q)
    (mul : U →ₗ[K] U →ₗ[K] Q)
    (hleft : ∀ w ∈ W, ∀ x, mul w x ∈ J) :
    W ≤ (multiplicationToQuotient J mul).ker := by
  intro w hw
  rw [LinearMap.mem_ker]
  ext x
  simp only [multiplicationToQuotient, LinearMap.compr₂_apply, LinearMap.zero_apply,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact hleft w hw x

/-- The corresponding right kernel condition. -/
theorem parameterSpace_le_flipKer_multiplicationToQuotient
    (W : Submodule K U) (J : Submodule K Q)
    (mul : U →ₗ[K] U →ₗ[K] Q)
    (hright : ∀ w ∈ W, ∀ x, mul x w ∈ J) :
    W ≤ (multiplicationToQuotient J mul).flip.ker := by
  intro w hw
  rw [LinearMap.mem_ker]
  ext x
  simp only [LinearMap.flip_apply, multiplicationToQuotient, LinearMap.compr₂_apply,
    LinearMap.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact hright w hw x

/-- Ambient degree-one multiplication descends canonically to both degree-one quotient
arguments once products involving the parameter space vanish in the degree-two quotient. -/
def quotientMultiplication
    (W : Submodule K U) (J : Submodule K Q)
    (mul : U →ₗ[K] U →ₗ[K] Q)
    (hleft : ∀ w ∈ W, ∀ x, mul w x ∈ J)
    (hright : ∀ w ∈ W, ∀ x, mul x w ∈ J) :
    (U ⧸ W) →ₗ[K] (U ⧸ W) →ₗ[K] (Q ⧸ J) :=
  (multiplicationToQuotient J mul).liftQ₂ W W
    (parameterSpace_le_ker_multiplicationToQuotient W J mul hleft)
    (parameterSpace_le_flipKer_multiplicationToQuotient W J mul hright)

@[simp]
theorem quotientMultiplication_mk
    (W : Submodule K U) (J : Submodule K Q)
    (mul : U →ₗ[K] U →ₗ[K] Q)
    (hleft : ∀ w ∈ W, ∀ x, mul w x ∈ J)
    (hright : ∀ w ∈ W, ∀ x, mul x w ∈ J)
    (x y : U) :
    quotientMultiplication W J mul hleft hright (W.mkQ x) (W.mkQ y) =
      J.mkQ (mul x y) := by
  rfl

/-- A functional annihilating the degree-two relation space descends canonically to the
degree-two quotient. -/
def descendedSocleFunctional
    (J : Submodule K Q) (ell : Q →ₗ[K] K) (hJ : J ≤ LinearMap.ker ell) :
    (Q ⧸ J) →ₗ[K] K :=
  J.liftQ ell hJ

@[simp]
theorem descendedSocleFunctional_mk
    (J : Submodule K Q) (ell : Q →ₗ[K] K) (hJ : J ≤ LinearMap.ker ell)
    (q : Q) :
    descendedSocleFunctional J ell hJ (J.mkQ q) = ell q := by
  rfl

/-- The descended multiplication and functional recover the original ambient Hankel values on
representatives.  This supplies, rather than assumes, the factorization used in the rank proof. -/
theorem descendedSocleFunctional_quotientMultiplication_mk
    (W : Submodule K U) (J : Submodule K Q)
    (mul : U →ₗ[K] U →ₗ[K] Q)
    (hleft : ∀ w ∈ W, ∀ x, mul w x ∈ J)
    (hright : ∀ w ∈ W, ∀ x, mul x w ∈ J)
    (ell : Q →ₗ[K] K) (hJ : J ≤ LinearMap.ker ell)
    (x y : U) :
    descendedSocleFunctional J ell hJ
        (quotientMultiplication W J mul hleft hright (W.mkQ x) (W.mkQ y)) =
      ell (mul x y) := by
  simp only [quotientMultiplication_mk, descendedSocleFunctional_mk]

/-- Symmetry of ambient multiplication passes to the quotient multiplication. -/
theorem quotientMultiplication_symmetric
    (W : Submodule K U) (J : Submodule K Q)
    (mul : U →ₗ[K] U →ₗ[K] Q)
    (hleft : ∀ w ∈ W, ∀ x, mul w x ∈ J)
    (hright : ∀ w ∈ W, ∀ x, mul x w ∈ J)
    (hsymm : ∀ x y, mul x y = mul y x) :
    ∀ x y, quotientMultiplication W J mul hleft hright x y =
      quotientMultiplication W J mul hleft hright y x := by
  intro x y
  obtain ⟨x, rfl⟩ := W.mkQ_surjective x
  obtain ⟨y, rfl⟩ := W.mkQ_surjective y
  simp only [quotientMultiplication_mk, hsymm]

/-- The swap relations used to form the second symmetric power from the tensor square.
This local construction supplies the degree-two universal property that is not currently exposed
by mathlib's `SymmetricPower` API. -/
def symmetricSquareRelations : Submodule K (TensorProduct K U U) :=
  Submodule.span K (Set.range fun xy : U × U ↦
    xy.1 ⊗ₜ[K] xy.2 - xy.2 ⊗ₜ[K] xy.1)

/-- The symmetric square of a vector space, presented as the tensor square modulo swaps. -/
abbrev SymmetricSquare (K : Type u) (U : Type v)
    [Field K] [AddCommGroup U] [Module K U] :=
  HasQuotient.Quotient (TensorProduct K U U)
    (symmetricSquareRelations (K := K) (U := U))

/-- A symmetric bilinear multiplication map kills all swap relations. -/
theorem symmetricSquareRelations_le_ker_tensorProduct_lift
    (mul : U →ₗ[K] U →ₗ[K] Q)
    (hsymm : ∀ x y, mul x y = mul y x) :
    symmetricSquareRelations ≤ LinearMap.ker (TensorProduct.lift mul) := by
  rw [symmetricSquareRelations, Submodule.span_le]
  rintro z ⟨⟨x, y⟩, rfl⟩
  change TensorProduct.lift mul (x ⊗ₜ[K] y - y ⊗ₜ[K] x) = 0
  simp only [map_sub, TensorProduct.lift.tmul, sub_eq_zero]
  exact hsymm x y

/-- The multiplication map `Sym²(U) → Q` induced by a symmetric bilinear multiplication.
This is the abstract linear map used in the PDF's standard-graded degree-two argument. -/
def symmetricSquareMultiplication
    (mul : U →ₗ[K] U →ₗ[K] Q)
    (hsymm : ∀ x y, mul x y = mul y x) :
    SymmetricSquare K U →ₗ[K] Q :=
  (symmetricSquareRelations (K := K) (U := U)).liftQ (TensorProduct.lift mul)
    (symmetricSquareRelations_le_ker_tensorProduct_lift mul hsymm)

@[simp]
theorem symmetricSquareMultiplication_mk
    (mul : U →ₗ[K] U →ₗ[K] Q)
    (hsymm : ∀ x y, mul x y = mul y x) (t : TensorProduct K U U) :
    symmetricSquareMultiplication mul hsymm
        ((symmetricSquareRelations (K := K) (U := U)).mkQ t) = TensorProduct.lift mul t := by
  rfl

@[simp]
theorem symmetricSquareMultiplication_mk_tmul
    (mul : U →ₗ[K] U →ₗ[K] Q)
    (hsymm : ∀ x y, mul x y = mul y x) (x y : U) :
    symmetricSquareMultiplication mul hsymm
        ((symmetricSquareRelations (K := K) (U := U)).mkQ (x ⊗ₜ[K] y)) = mul x y := by
  rfl

/-- Surjectivity of the paper's symmetric-square multiplication map implies that products span
the ambient degree-two space, expressed through the tensor-product lift. -/
theorem tensorProduct_lift_surjective_of_symmetricSquareMultiplication_surjective
    (mul : U →ₗ[K] U →ₗ[K] Q)
    (hsymm : ∀ x y, mul x y = mul y x)
    (hmul : Function.Surjective (symmetricSquareMultiplication mul hsymm)) :
    Function.Surjective (TensorProduct.lift mul) := by
  intro q
  obtain ⟨z, hz⟩ := hmul q
  obtain ⟨t, rfl⟩ :=
    (symmetricSquareRelations (K := K) (U := U)).mkQ_surjective z
  exact ⟨t, hz⟩

/-- Conversely, tensor-product generation makes the descended symmetric-square multiplication
surjective. -/
theorem symmetricSquareMultiplication_surjective_of_tensorProduct_lift_surjective
    (mul : U →ₗ[K] U →ₗ[K] Q)
    (hsymm : ∀ x y, mul x y = mul y x)
    (hmul : Function.Surjective (TensorProduct.lift mul)) :
    Function.Surjective (symmetricSquareMultiplication mul hsymm) := by
  intro q
  obtain ⟨t, ht⟩ := hmul q
  exact ⟨(symmetricSquareRelations (K := K) (U := U)).mkQ t, ht⟩

/-- For symmetric multiplication, generation through the PDF's `Sym²(U)` map is equivalent to
generation through the tensor-linearized multiplication map. -/
theorem symmetricSquareMultiplication_surjective_iff_tensorProduct_lift_surjective
    (mul : U →ₗ[K] U →ₗ[K] Q)
    (hsymm : ∀ x y, mul x y = mul y x) :
    Function.Surjective (symmetricSquareMultiplication mul hsymm) ↔
      Function.Surjective (TensorProduct.lift mul) :=
  ⟨tensorProduct_lift_surjective_of_symmetricSquareMultiplication_surjective mul hsymm,
    symmetricSquareMultiplication_surjective_of_tensorProduct_lift_surjective mul hsymm⟩

/-- If degree two is spanned by products of degree-one elements, then a nonzero degree-two
functional gives a nonzero Hankel form.  Surjectivity of `TensorProduct.lift mul` is the precise
linear statement that the products span. -/
theorem hankelForm_ne_zero_of_tensorProduct_lift_surjective
    (mul : U →ₗ[K] U →ₗ[K] Q)
    (ell : Q →ₗ[K] K) (hell : ell ≠ 0)
    (hmul : Function.Surjective (TensorProduct.lift mul)) :
    mul.compr₂ ell ≠ 0 := by
  intro hzero
  apply hell
  apply (LinearMap.cancel_right hmul).mp
  rw [← TensorProduct.lift_compr₂]
  simp only [LinearMap.zero_comp]
  rw [hzero]
  apply TensorProduct.ext'
  intro x y
  rfl

/-- PDF-facing form of degree-two generation: a nonzero functional on a space generated by the
image of `Sym²(U)` induces a nonzero Hankel form. -/
theorem hankelForm_ne_zero_of_symmetricSquareMultiplication_surjective
    (mul : U →ₗ[K] U →ₗ[K] Q)
    (hsymm : ∀ x y, mul x y = mul y x)
    (ell : Q →ₗ[K] K) (hell : ell ≠ 0)
    (hmul : Function.Surjective (symmetricSquareMultiplication mul hsymm)) :
    mul.compr₂ ell ≠ 0 :=
  hankelForm_ne_zero_of_tensorProduct_lift_surjective mul ell hell
    (tensorProduct_lift_surjective_of_symmetricSquareMultiplication_surjective mul hsymm hmul)

/-- The degree-two part of the ideal generated by the parameter space: the span of all products
`w * x` with `w ∈ W` and `x` in the ambient degree-one space. -/
def parameterProductSubmodule
    (W : Submodule K U) (mul : U →ₗ[K] U →ₗ[K] Q) : Submodule K Q :=
  Submodule.span K (Set.range fun wx : W × U ↦ mul wx.1 wx.2)

/-- Every product involving a parameter-space element belongs to the canonical degree-two
product submodule. -/
theorem mul_mem_parameterProductSubmodule
    (W : Submodule K U) (mul : U →ₗ[K] U →ₗ[K] Q)
    (w : U) (hw : w ∈ W) (x : U) :
    mul w x ∈ parameterProductSubmodule W mul := by
  apply Submodule.subset_span
  exact ⟨(⟨w, hw⟩, x), rfl⟩

/-- If `W` lies in the radical of the Hankel form associated to `ell`, then `ell` annihilates
the entire degree-two product submodule generated by `W`. -/
theorem parameterProductSubmodule_le_ker_functional
    (W : Submodule K U) (mul : U →ₗ[K] U →ₗ[K] Q) (ell : Q →ₗ[K] K)
    (hW : W ≤ LinearMap.ker (mul.compr₂ ell)) :
    parameterProductSubmodule W mul ≤ LinearMap.ker ell := by
  rw [parameterProductSubmodule, Submodule.span_le]
  rintro q ⟨⟨⟨w, hw⟩, x⟩, rfl⟩
  change mul w x ∈ LinearMap.ker ell
  rw [LinearMap.mem_ker]
  have hwker := hW hw
  rw [LinearMap.mem_ker] at hwker
  simpa only [LinearMap.compr₂_apply, LinearMap.zero_apply] using
    LinearMap.congr_fun hwker x

/-- The canonical multiplication on the quotient by a parameter space, with degree-two target
the quotient by the span of products involving that parameter space. -/
def parameterProductQuotientMultiplication
    (W : Submodule K U) (mul : U →ₗ[K] U →ₗ[K] Q)
    (hsymm : ∀ x y, mul x y = mul y x) :
    (U ⧸ W) →ₗ[K] (U ⧸ W) →ₗ[K] (Q ⧸ parameterProductSubmodule W mul) :=
  quotientMultiplication W (parameterProductSubmodule W mul) mul
    (mul_mem_parameterProductSubmodule W mul)
    (fun w hw y ↦ hsymm y w ▸ mul_mem_parameterProductSubmodule W mul w hw y)

@[simp]
theorem parameterProductQuotientMultiplication_mk
    (W : Submodule K U) (mul : U →ₗ[K] U →ₗ[K] Q)
    (hsymm : ∀ x y, mul x y = mul y x) (x y : U) :
    parameterProductQuotientMultiplication W mul hsymm (W.mkQ x) (W.mkQ y) =
      (parameterProductSubmodule W mul).mkQ (mul x y) := by
  rfl

/-- The canonical quotient multiplication remains symmetric. -/
theorem parameterProductQuotientMultiplication_symmetric
    (W : Submodule K U) (mul : U →ₗ[K] U →ₗ[K] Q)
    (hsymm : ∀ x y, mul x y = mul y x) :
    ∀ x y, parameterProductQuotientMultiplication W mul hsymm x y =
      parameterProductQuotientMultiplication W mul hsymm y x :=
  quotientMultiplication_symmetric W (parameterProductSubmodule W mul) mul
    (mul_mem_parameterProductSubmodule W mul)
    (fun w hw y ↦ hsymm y w ▸ mul_mem_parameterProductSubmodule W mul w hw y) hsymm

/-- The exact Artinian Gorenstein information about the canonical quotient used by Theorem 4.3:
its degree-two piece is one-dimensional, and no nonzero degree-one class annihilates all
degree-one classes.  This is a proof-only interface for the conclusion of PDF Proposition 2.2;
it does not assert that the upstream Cohen--Macaulay/Gorenstein derivation has been formalized. -/
structure ParameterProductGorensteinCertificate
    (W : Submodule K U) (mul : U →ₗ[K] U →ₗ[K] Q)
    (hsymm : ∀ x y, mul x y = mul y x) : Prop where
  socleFinrankOne : Module.finrank K (Q ⧸ parameterProductSubmodule W mul) = 1
  socleAnnihilator : ∀ x,
    (∀ y, parameterProductQuotientMultiplication W mul hsymm x y = 0) → x = 0

/-- The intrinsic perfect-pairing form of the Artinian Gorenstein quotient data appearing in the
PDF.  The multiplication takes values directly in the one-dimensional degree-two socle, without
choosing a coordinate on that socle. -/
structure ParameterProductPerfectPairingCertificate
    (W : Submodule K U) (mul : U →ₗ[K] U →ₗ[K] Q)
    (hsymm : ∀ x y, mul x y = mul y x) : Prop where
  socleFinrankOne : Module.finrank K (Q ⧸ parameterProductSubmodule W mul) = 1
  perfect : (parameterProductQuotientMultiplication W mul hsymm).Nondegenerate

/-- The Gorenstein annihilator formulation already implies the intrinsic perfect-pairing
formulation: symmetry turns the supplied left nondegeneracy into right nondegeneracy. -/
theorem ParameterProductGorensteinCertificate.toPerfectPairingCertificate
    {W : Submodule K U} {mul : U →ₗ[K] U →ₗ[K] Q}
    {hsymm : ∀ x y, mul x y = mul y x}
    (h : ParameterProductGorensteinCertificate W mul hsymm) :
    ParameterProductPerfectPairingCertificate W mul hsymm where
  socleFinrankOne := h.socleFinrankOne
  perfect := by
    constructor
    · exact h.socleAnnihilator
    · intro y hy
      apply h.socleAnnihilator y
      intro x
      rw [parameterProductQuotientMultiplication_symmetric W mul hsymm]
      exact hy x

/-- Choosing the canonical coordinate on the one-dimensional socle turns the intrinsic
socle-valued perfect pairing into a nondegenerate scalar pairing. -/
theorem ParameterProductPerfectPairingCertificate.scalarPairing_nondegenerate
    {W : Submodule K U} {mul : U →ₗ[K] U →ₗ[K] Q}
    {hsymm : ∀ x y, mul x y = mul y x}
    (h : ParameterProductPerfectPairingCertificate W mul hsymm) :
    ((parameterProductQuotientMultiplication W mul hsymm).compr₂
      (socleEquivOfFinrankEqOne h.socleFinrankOne).toLinearMap).Nondegenerate := by
  constructor
  · intro x hx
    apply h.perfect.1 x
    intro y
    apply (socleEquivOfFinrankEqOne h.socleFinrankOne).injective
    exact (hx y).trans (map_zero _).symm
  · intro y hy
    apply h.perfect.2 y
    intro x
    apply (socleEquivOfFinrankEqOne h.socleFinrankOne).injective
    exact (hy x).trans (map_zero _).symm

/-- A perfect scalar Gorenstein pairing has zero degree-one annihilator, so it supplies the
annihilator-form certificate consumed by the ambient rank theorem. -/
theorem ParameterProductPerfectPairingCertificate.toGorensteinCertificate
    {W : Submodule K U} {mul : U →ₗ[K] U →ₗ[K] Q}
    {hsymm : ∀ x y, mul x y = mul y x}
    (h : ParameterProductPerfectPairingCertificate W mul hsymm) :
    ParameterProductGorensteinCertificate W mul hsymm where
  socleFinrankOne := h.socleFinrankOne
  socleAnnihilator := h.perfect.1

variable [Module.Finite K U]

/-- Ambient-data form of the Artinian Gorenstein step in PDF Theorem 4.3.  Here `W` is the
parameter space in degree one, `J` is the degree-two part of its generated ideal, `mul` is
ambient multiplication, and `ell` is the original degree-two functional.  The hypotheses that
`W * U ⊆ J` and `ell(J) = 0` construct both quotient multiplication and the induced socle
functional internally.  The theorem then identifies the actual ambient Hankel kernel with `W`
and obtains the paper's dimension and rank equalities. -/
theorem hankelKernel_eq_parameterSpace_and_finrank_and_rank_of_ambientMultiplication
    (W : Submodule K U) (J : Submodule K Q)
    (mul : U →ₗ[K] U →ₗ[K] Q)
    (hprod : ∀ w ∈ W, ∀ x, mul w x ∈ J)
    (hsymm : ∀ x y, mul x y = mul y x)
    (ell : Q →ₗ[K] K) (hJ : J ≤ LinearMap.ker ell)
    (hS : Module.finrank K (Q ⧸ J) = 1)
    (hann : ∀ x,
      (∀ y, quotientMultiplication W J mul hprod
        (fun w hw y ↦ hsymm y w ▸ hprod w hw y) x y = 0) → x = 0)
    (hB : mul.compr₂ ell ≠ 0)
    {m c : ℕ}
    (hU : Module.finrank K U = m + c + 1)
    (hQ : Module.finrank K (U ⧸ W) = c) :
    LinearMap.ker (mul.compr₂ ell) = W ∧
      Module.finrank K (LinearMap.ker (mul.compr₂ ell)) = m + 1 ∧
        LinearMap.BilinForm.finiteRank (mul.compr₂ ell) = c := by
  let hright : ∀ w ∈ W, ∀ x, mul x w ∈ J :=
    fun w hw x ↦ hsymm x w ▸ hprod w hw x
  exact hankelKernel_eq_parameterSpace_and_finrank_and_rank_of_factorization
    W (quotientMultiplication W J mul hprod hright)
      (quotientMultiplication_symmetric W J mul hprod hright hsymm)
    hS hann (descendedSocleFunctional J ell hJ) (mul.compr₂ ell)
      (fun x y ↦ (descendedSocleFunctional_quotientMultiplication_mk
        W J mul hprod hright ell hJ x y).symm)
    hB hU hQ

/-- Paper-facing strengthening of
`hankelKernel_eq_parameterSpace_and_finrank_and_rank_of_ambientMultiplication`: nonzeroness is
assumed only for the original degree-two functional.  Generation of degree two by products
proves internally that its associated ambient Hankel form is nonzero. -/
theorem hankelKernel_eq_parameterSpace_and_finrank_and_rank_of_degreeTwoGenerated
    (W : Submodule K U) (J : Submodule K Q)
    (mul : U →ₗ[K] U →ₗ[K] Q)
    (hprod : ∀ w ∈ W, ∀ x, mul w x ∈ J)
    (hsymm : ∀ x y, mul x y = mul y x)
    (ell : Q →ₗ[K] K) (hell : ell ≠ 0)
    (hmul : Function.Surjective (symmetricSquareMultiplication mul hsymm))
    (hJ : J ≤ LinearMap.ker ell)
    (hS : Module.finrank K (Q ⧸ J) = 1)
    (hann : ∀ x,
      (∀ y, quotientMultiplication W J mul hprod
        (fun w hw y ↦ hsymm y w ▸ hprod w hw y) x y = 0) → x = 0)
    {m c : ℕ}
    (hU : Module.finrank K U = m + c + 1)
    (hQ : Module.finrank K (U ⧸ W) = c) :
    LinearMap.ker (mul.compr₂ ell) = W ∧
      Module.finrank K (LinearMap.ker (mul.compr₂ ell)) = m + 1 ∧
        LinearMap.BilinForm.finiteRank (mul.compr₂ ell) = c :=
  hankelKernel_eq_parameterSpace_and_finrank_and_rank_of_ambientMultiplication
    W J mul hprod hsymm ell hJ hS hann
      (hankelForm_ne_zero_of_symmetricSquareMultiplication_surjective
        mul hsymm ell hell hmul)
    hU hQ

/-- Canonical-ideal version of the Artinian Gorenstein step in PDF Theorem 4.3.  The degree-two
relation space is no longer supplied: it is constructed as the span of `W * U`.  Containment of
`W` in the ambient Hankel radical proves that the original functional descends to this quotient.
The remaining quotient hypotheses are precisely the one-dimensional socle, its annihilator
property, and the Hilbert dimensions used in the paper. -/
theorem hankelKernel_eq_parameterSpace_and_finrank_and_rank_of_parameterProductSubmodule
    (W : Submodule K U)
    (mul : U →ₗ[K] U →ₗ[K] Q)
    (hsymm : ∀ x y, mul x y = mul y x)
    (ell : Q →ₗ[K] K) (hell : ell ≠ 0)
    (hmul : Function.Surjective (symmetricSquareMultiplication mul hsymm))
    (hW : W ≤ LinearMap.ker (mul.compr₂ ell))
    (hS : Module.finrank K (Q ⧸ parameterProductSubmodule W mul) = 1)
    (hann : ∀ x,
      (∀ y, quotientMultiplication W (parameterProductSubmodule W mul) mul
        (mul_mem_parameterProductSubmodule W mul)
        (fun w hw y ↦ hsymm y w ▸ mul_mem_parameterProductSubmodule W mul w hw y) x y = 0) →
      x = 0)
    {m c : ℕ}
    (hU : Module.finrank K U = m + c + 1)
    (hQ : Module.finrank K (U ⧸ W) = c) :
    LinearMap.ker (mul.compr₂ ell) = W ∧
      Module.finrank K (LinearMap.ker (mul.compr₂ ell)) = m + 1 ∧
        LinearMap.BilinForm.finiteRank (mul.compr₂ ell) = c :=
  hankelKernel_eq_parameterSpace_and_finrank_and_rank_of_degreeTwoGenerated
    W (parameterProductSubmodule W mul) mul
    (mul_mem_parameterProductSubmodule W mul) hsymm ell hell hmul
    (parameterProductSubmodule_le_ker_functional W mul ell hW) hS hann hU hQ

/-- Parameter-sequence form of the canonical-ideal rank theorem.  The chosen parameter space
has the known dimension `m+1`; its quotient dimension `c` is derived internally from
`dim R₁ = m+c+1`, as in the proof of PDF Theorem 4.3. -/
theorem hankelKernel_eq_parameterSpace_and_rank_of_parameterFinrank
    (W : Submodule K U)
    (mul : U →ₗ[K] U →ₗ[K] Q)
    (hsymm : ∀ x y, mul x y = mul y x)
    (ell : Q →ₗ[K] K) (hell : ell ≠ 0)
    (hmul : Function.Surjective (symmetricSquareMultiplication mul hsymm))
    (hWker : W ≤ LinearMap.ker (mul.compr₂ ell))
    (hS : Module.finrank K (Q ⧸ parameterProductSubmodule W mul) = 1)
    (hann : ∀ x,
      (∀ y, quotientMultiplication W (parameterProductSubmodule W mul) mul
        (mul_mem_parameterProductSubmodule W mul)
        (fun w hw y ↦ hsymm y w ▸ mul_mem_parameterProductSubmodule W mul w hw y) x y = 0) →
      x = 0)
    {m c : ℕ}
    (hU : Module.finrank K U = m + c + 1)
    (hWfinrank : Module.finrank K W = m + 1) :
    LinearMap.ker (mul.compr₂ ell) = W ∧
      LinearMap.BilinForm.finiteRank (mul.compr₂ ell) = c := by
  have hQ : Module.finrank K (U ⧸ W) = c :=
    finrank_quotient_eq_of_parameterSpace_finrank W hU hWfinrank
  have hresult :=
    hankelKernel_eq_parameterSpace_and_finrank_and_rank_of_parameterProductSubmodule
      W mul hsymm ell hell hmul hWker hS hann hU hQ
  exact ⟨hresult.1, hresult.2.2⟩

/-- Certificate form of the parameter-sequence rank theorem.  It combines the canonical
quotient construction with precisely the two Artinian Gorenstein consequences consumed by the
proof, while deriving the degree-one quotient dimension from the parameter-space dimension. -/
theorem hankelKernel_eq_parameterSpace_and_rank_of_gorensteinCertificate
    (W : Submodule K U)
    (mul : U →ₗ[K] U →ₗ[K] Q)
    (hsymm : ∀ x y, mul x y = mul y x)
    (ell : Q →ₗ[K] K) (hell : ell ≠ 0)
    (hmul : Function.Surjective (symmetricSquareMultiplication mul hsymm))
    (hWker : W ≤ LinearMap.ker (mul.compr₂ ell))
    (hAG : ParameterProductGorensteinCertificate W mul hsymm)
    {m c : ℕ}
    (hU : Module.finrank K U = m + c + 1)
    (hWfinrank : Module.finrank K W = m + 1) :
    LinearMap.ker (mul.compr₂ ell) = W ∧
      LinearMap.BilinForm.finiteRank (mul.compr₂ ell) = c :=
  hankelKernel_eq_parameterSpace_and_rank_of_parameterFinrank
    W mul hsymm ell hell hmul hWker hAG.socleFinrankOne hAG.socleAnnihilator hU hWfinrank

/-- Perfect-pairing endpoint for PDF Theorem 4.3.  Once the chosen parameter quotient has the
one-dimensional perfect Gorenstein multiplication pairing asserted by Proposition 2.2, all
remaining quotient annihilator reasoning and the ambient Hankel kernel/rank calculation are
performed internally. -/
theorem hankelKernel_eq_parameterSpace_and_rank_of_perfectPairingCertificate
    (W : Submodule K U)
    (mul : U →ₗ[K] U →ₗ[K] Q)
    (hsymm : ∀ x y, mul x y = mul y x)
    (ell : Q →ₗ[K] K) (hell : ell ≠ 0)
    (hmul : Function.Surjective (symmetricSquareMultiplication mul hsymm))
    (hWker : W ≤ LinearMap.ker (mul.compr₂ ell))
    (hAG : ParameterProductPerfectPairingCertificate W mul hsymm)
    {m c : ℕ}
    (hU : Module.finrank K U = m + c + 1)
    (hWfinrank : Module.finrank K W = m + 1) :
    LinearMap.ker (mul.compr₂ ell) = W ∧
      LinearMap.BilinForm.finiteRank (mul.compr₂ ell) = c :=
  hankelKernel_eq_parameterSpace_and_rank_of_gorensteinCertificate
    W mul hsymm ell hell hmul hWker hAG.toGorensteinCertificate hU hWfinrank

/-- Parameter-sequence endpoint matching the construction in PDF Theorem 4.3.  The parameter
space is exhibited as the span of an explicitly linearly independent `(m+1)`-tuple, so its
dimension is derived rather than assumed. -/
theorem hankelKernel_eq_parameterSpace_and_rank_of_linearIndependentParameters
    (W : Submodule K U)
    (mul : U →ₗ[K] U →ₗ[K] Q)
    (hsymm : ∀ x y, mul x y = mul y x)
    (ell : Q →ₗ[K] K) (hell : ell ≠ 0)
    (hmul : Function.Surjective (symmetricSquareMultiplication mul hsymm))
    (hWker : W ≤ LinearMap.ker (mul.compr₂ ell))
    (hAG : ParameterProductPerfectPairingCertificate W mul hsymm)
    {m c : ℕ}
    (parameters : Fin (m + 1) → U)
    (hparameters : LinearIndependent K parameters)
    (hW : W = Submodule.span K (Set.range parameters))
    (hU : Module.finrank K U = m + c + 1) :
    LinearMap.ker (mul.compr₂ ell) = W ∧
      LinearMap.BilinForm.finiteRank (mul.compr₂ ell) = c := by
  apply hankelKernel_eq_parameterSpace_and_rank_of_perfectPairingCertificate
    W mul hsymm ell hell hmul hWker hAG hU
  rw [hW, finrank_span_eq_card hparameters]
  simp

/-- Fully pointwise parameter-sequence endpoint in the zero-annihilator Gorenstein formulation.
Each chosen parameter is assumed to lie in the ambient Hankel kernel, exactly as in the paper;
Lean proves span containment and derives its dimension from linear independence. -/
theorem hankelKernel_eq_parameterSpan_and_rank_of_gorensteinCertificate
    (mul : U →ₗ[K] U →ₗ[K] Q)
    (hsymm : ∀ x y, mul x y = mul y x)
    (ell : Q →ₗ[K] K) (hell : ell ≠ 0)
    (hmul : Function.Surjective (symmetricSquareMultiplication mul hsymm))
    {m c : ℕ}
    (parameters : Fin (m + 1) → U)
    (hparameters : LinearIndependent K parameters)
    (hparametersKernel : ∀ i, parameters i ∈ LinearMap.ker (mul.compr₂ ell))
    (hAG : ParameterProductGorensteinCertificate
      (Submodule.span K (Set.range parameters)) mul hsymm)
    (hU : Module.finrank K U = m + c + 1) :
    LinearMap.ker (mul.compr₂ ell) = Submodule.span K (Set.range parameters) ∧
      LinearMap.BilinForm.finiteRank (mul.compr₂ ell) = c := by
  apply hankelKernel_eq_parameterSpace_and_rank_of_gorensteinCertificate
    (Submodule.span K (Set.range parameters)) mul hsymm ell hell hmul
      (Submodule.span_le.mpr (Set.range_subset_iff.mpr hparametersKernel)) hAG hU
  rw [finrank_span_eq_card hparameters]
  simp

/-- Fully pointwise parameter-sequence endpoint for PDF Theorem 4.3 in intrinsic perfect-pairing
form.  The perfect certificate is converted to the equivalent zero-annihilator formulation. -/
theorem hankelKernel_eq_parameterSpan_and_rank_of_parameters_mem_hankelKernel
    (mul : U →ₗ[K] U →ₗ[K] Q)
    (hsymm : ∀ x y, mul x y = mul y x)
    (ell : Q →ₗ[K] K) (hell : ell ≠ 0)
    (hmul : Function.Surjective (symmetricSquareMultiplication mul hsymm))
    {m c : ℕ}
    (parameters : Fin (m + 1) → U)
    (hparameters : LinearIndependent K parameters)
    (hparametersKernel : ∀ i, parameters i ∈ LinearMap.ker (mul.compr₂ ell))
    (hAG : ParameterProductPerfectPairingCertificate
      (Submodule.span K (Set.range parameters)) mul hsymm)
    (hU : Module.finrank K U = m + c + 1) :
    LinearMap.ker (mul.compr₂ ell) = Submodule.span K (Set.range parameters) ∧
      LinearMap.BilinForm.finiteRank (mul.compr₂ ell) = c :=
  hankelKernel_eq_parameterSpan_and_rank_of_gorensteinCertificate
    mul hsymm ell hell hmul parameters hparameters hparametersKernel
      hAG.toGorensteinCertificate hU

end ArtinianGorensteinDegreeOneCertificate
