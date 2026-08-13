import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.LinearAlgebra.QuadraticForm.Real
import Mathlib.LinearAlgebra.Dual.Lemmas

noncomputable section

universe u

namespace QuadraticForm

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- Restricting a real quadratic form to a subspace cannot increase its negative index. -/
theorem sigNeg_restrict_le (Q : QuadraticForm ℝ V) (W : Submodule ℝ V) :
    sigNeg (Q.restrict W) ≤ sigNeg Q := by
  obtain ⟨N, hNdim, hNneg⟩ := exists_finrank_eq_sigNeg_and_negDef (Q.restrict W)
  let N' : Submodule ℝ V := N.map W.subtype
  have hmap : Function.Injective (W.subtype.domRestrict N) := by
    exact W.injective_subtype.comp Subtype.val_injective
  have hdim : Module.finrank ℝ N' = Module.finrank ℝ N := by
    have he := (LinearEquiv.finrank_eq
      (LinearEquiv.ofInjective (W.subtype.domRestrict N) hmap)).symm
    rw [LinearMap.range_domRestrict] at he
    exact he
  have hneg : ((-Q).restrict N').PosDef := by
    rintro ⟨x, ⟨y, hyN, rfl⟩⟩ hx
    have hy : (⟨y, hyN⟩ : N) ≠ 0 := by
      intro heq
      apply hx
      ext
      exact congrArg (fun z : N ↦ (z : V)) heq
    simpa [QuadraticMap.restrict_apply] using hNneg ⟨y, hyN⟩ hy
  rw [← hNdim, ← hdim]
  exact le_sigNeg_of_negDef Q hneg

/-- Hyperplane inertia bound (the paper's Lemma 6.1 in signature language): if a real quadratic
form is nonnegative on a codimension-one subspace, then it has at most one negative direction. -/
theorem sigNeg_le_one_of_nonneg_hyperplane
    (Q : QuadraticForm ℝ V) (W : Submodule ℝ V)
    (hcodim : Module.finrank ℝ V = Module.finrank ℝ W + 1)
    (hnonneg : ∀ x ∈ W, 0 ≤ Q x) :
    sigNeg Q ≤ 1 := by
  have hbound := sigPos_add_finrank_le_of_nonpos (Q := -Q) (V := W) (by
    intro x hx
    simpa using neg_nonpos.mpr (hnonneg x hx))
  rw [sigPos_neg] at hbound
  omega

/-- Kernel formulation of the hyperplane inertia bound: the kernel of any nonzero functional is
codimension one automatically. -/
theorem sigNeg_le_one_of_nonneg_ker
    (Q : QuadraticForm ℝ V) (f : Module.Dual ℝ V) (hf : f ≠ 0)
    (hnonneg : ∀ x, f x = 0 → 0 ≤ Q x) :
    sigNeg Q ≤ 1 := by
  apply sigNeg_le_one_of_nonneg_hyperplane Q (LinearMap.ker f)
  · exact (Module.Dual.finrank_ker_add_one_of_ne_zero hf).symm
  · intro x hx
    exact hnonneg x (LinearMap.mem_ker.mp hx)

/-- A family of nonreal conjugate pairs contributes at least one independent negative direction
per pair.  This certificate records exactly the negative-definite subspace constructed from those
directions in the paper's real-fiber argument. -/
structure NonrealPairNegativeDirections (Q : QuadraticForm ℝ V) (P : Type*) where
  space : Submodule ℝ V
  finrank_eq_card : Module.finrank ℝ space = Nat.card P
  negDef : ((-Q).restrict space).PosDef

namespace NonrealPairNegativeDirections

variable {Q : QuadraticForm ℝ V} {P : Type*}

/-- The number of conjugate pairs is bounded by the negative index. -/
theorem card_le_sigNeg (h : NonrealPairNegativeDirections Q P) :
    Nat.card P ≤ sigNeg Q := by
  rw [← h.finrank_eq_card]
  exact le_sigNeg_of_negDef Q h.negDef

/-- In particular, a Lorentzian form (negative index at most one) permits at most one nonreal
conjugate pair. -/
theorem card_le_one (h : NonrealPairNegativeDirections Q P) (hQ : sigNeg Q ≤ 1) :
    Nat.card P ≤ 1 :=
  (h.card_le_sigNeg).trans hQ

/-- The same conclusion holds when the relevant form is a restriction of an ambient index-one
form. -/
theorem card_le_one_of_restrict {W : Submodule ℝ V}
    {P : Type*}
    (h : NonrealPairNegativeDirections (Q.restrict W) P)
    (hQ : sigNeg Q ≤ 1) : Nat.card P ≤ 1 :=
  h.card_le_one ((sigNeg_restrict_le Q W).trans hQ)

/-- Combining the hyperplane inertia bound with the pair-direction construction gives the
at-most-one-pair conclusion without a separate signature hypothesis. -/
theorem card_le_one_of_nonneg_hyperplane
    {P : Type*} (h : NonrealPairNegativeDirections Q P)
    (W : Submodule ℝ V)
    (hcodim : Module.finrank ℝ V = Module.finrank ℝ W + 1)
    (hnonneg : ∀ x ∈ W, 0 ≤ Q x) : Nat.card P ≤ 1 :=
  h.card_le_one (sigNeg_le_one_of_nonneg_hyperplane Q W hcodim hnonneg)

/-- Functional-kernel version, closest to the evaluation-relation hyperplane in the fiber
classification. -/
theorem card_le_one_of_nonneg_ker
    {P : Type*} (h : NonrealPairNegativeDirections Q P)
    (f : Module.Dual ℝ V) (hf : f ≠ 0)
    (hnonneg : ∀ x, f x = 0 → 0 ≤ Q x) : Nat.card P ≤ 1 :=
  h.card_le_one (sigNeg_le_one_of_nonneg_ker Q f hf hnonneg)

end NonrealPairNegativeDirections

end QuadraticForm
