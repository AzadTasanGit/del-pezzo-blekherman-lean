import DelPezzoBlekherman.Algebra.SoclePairing
import Mathlib.LinearAlgebra.Quotient.Bilinear
import Mathlib.LinearAlgebra.TensorProduct.Basic

noncomputable section

universe u v w

open LinearMap

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
    (hmul : Function.Surjective (TensorProduct.lift mul))
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
      (hankelForm_ne_zero_of_tensorProduct_lift_surjective mul ell hell hmul)
    hU hQ

end ArtinianGorensteinDegreeOneCertificate
