import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Real.Basic

noncomputable section

universe u v w

open scoped BigOperators
open Finset

namespace SOSKernelLength

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [Module.Finite ℝ V]

/-- If a positive-semidefinite bilinear form annihilates a sum of diagonal values, every summand
lies in its radical.  This is the Gram-kernel step in the boundary SOS argument. -/
theorem each_mem_ker_of_sum_apply_self_eq_zero
    (B : LinearMap.BilinForm ℝ V) (hB : B.IsPosSemidef)
    {ι : Type v} [Fintype ι] (f : ι → V)
    (hsum : ∑ i, B (f i) (f i) = 0) :
    ∀ i, f i ∈ LinearMap.ker B := by
  intro i
  apply (B.apply_apply_same_eq_zero_iff hB.isNonneg.nonneg hB.isSymm).mp
  exact (Finset.sum_eq_zero_iff_of_nonneg
    (fun j hj ↦ hB.isNonneg.nonneg (f j))).mp hsum i (Finset.mem_univ i)

theorem span_range_le_ker_of_sum_apply_self_eq_zero
    (B : LinearMap.BilinForm ℝ V) (hB : B.IsPosSemidef)
    {ι : Type v} [Fintype ι] (f : ι → V)
    (hsum : ∑ i, B (f i) (f i) = 0) :
    Submodule.span ℝ (Set.range f) ≤ LinearMap.ker B := by
  apply Submodule.span_le.mpr
  rintro x ⟨i, rfl⟩
  exact each_mem_ker_of_sum_apply_self_eq_zero B hB f hsum i

/-- If the geometry forces the summands of a boundary SOS representation to span the whole
Hankel radical, the number of summands is at least the radical dimension. -/
theorem finrank_ker_le_card
    (B : LinearMap.BilinForm ℝ V) (hB : B.IsPosSemidef)
    {ι : Type v} [Fintype ι] (f : ι → V)
    (hsum : ∑ i, B (f i) (f i) = 0)
    (hspans : LinearMap.ker B ≤ Submodule.span ℝ (Set.range f)) :
    Module.finrank ℝ (LinearMap.ker B) ≤ Fintype.card ι := by
  have hle := span_range_le_ker_of_sum_apply_self_eq_zero B hB f hsum
  have heq : Submodule.span ℝ (Set.range f) = LinearMap.ker B := le_antisymm hle hspans
  rw [← heq]
  exact finrank_range_le_card f

theorem card_ge_add_one_of_finrank_ker_eq
    (B : LinearMap.BilinForm ℝ V) (hB : B.IsPosSemidef)
    {ι : Type v} [Fintype ι] (f : ι → V)
    (hsum : ∑ i, B (f i) (f i) = 0)
    (hspans : LinearMap.ker B ≤ Submodule.span ℝ (Set.range f))
    {m : ℕ} (hker : Module.finrank ℝ (LinearMap.ker B) = m + 1) :
    m + 1 ≤ Fintype.card ι := by
  rw [← hker]
  exact finrank_ker_le_card B hB f hsum hspans

section Basepoints

variable {X : Type*}

/-- Abstract projective base-locus lemma used by the SOS-length argument.  If every proper
subspace of `W` has a common zero, then any family in `W` with no common zero spans `W`. -/
theorem span_eq_of_no_common_zero
    (eval : X → Module.Dual ℝ V) (W : Submodule ℝ V)
    {ι : Type v} [Fintype ι] (f : ι → V)
    (hfW : ∀ i, f i ∈ W)
    (hproper : ∀ U : Submodule ℝ V, U < W →
      ∃ x : X, ∀ g ∈ U, eval x g = 0)
    (hnoCommonZero : ∀ x : X, ∃ i, eval x (f i) ≠ 0) :
    Submodule.span ℝ (Set.range f) = W := by
  have hle : Submodule.span ℝ (Set.range f) ≤ W := by
    apply Submodule.span_le.mpr
    rintro g ⟨i, rfl⟩
    exact hfW i
  apply le_antisymm hle
  by_contra hnot
  have hne : Submodule.span ℝ (Set.range f) ≠ W := by
    intro heq
    apply hnot
    rw [heq]
  have hlt : Submodule.span ℝ (Set.range f) < W := lt_of_le_of_ne hle hne
  obtain ⟨x, hx⟩ := hproper (Submodule.span ℝ (Set.range f)) hlt
  obtain ⟨i, hi⟩ := hnoCommonZero x
  exact hi (hx (f i) (Submodule.subset_span ⟨i, rfl⟩))

/-- With the Hankel radical as `W`, the abstract base-locus statement supplies precisely the
spanning hypothesis needed for the length lower bound. -/
theorem ker_le_span_of_no_common_zero
    (B : LinearMap.BilinForm ℝ V)
    (eval : X → Module.Dual ℝ V)
    {ι : Type v} [Fintype ι] (f : ι → V)
    (hfker : ∀ i, f i ∈ LinearMap.ker B)
    (hproper : ∀ U : Submodule ℝ V, U < LinearMap.ker B →
      ∃ x : X, ∀ g ∈ U, eval x g = 0)
    (hnoCommonZero : ∀ x : X, ∃ i, eval x (f i) ≠ 0) :
    LinearMap.ker B ≤ Submodule.span ℝ (Set.range f) := by
  rw [span_eq_of_no_common_zero eval (LinearMap.ker B) f hfker hproper hnoCommonZero]

end Basepoints

section Hankel

variable {Q : Type w} [AddCommGroup Q] [Module ℝ Q]

/-- Strict positivity of a sum of squares implies that its summands have no common evaluation
zero. -/
theorem no_common_zero_of_strictlyPositive_sos
    {X : Type*} (evalV : X → Module.Dual ℝ V) (evalQ : X → Q →ₗ[ℝ] ℝ)
    (mul : V → V → Q)
    (hevalMul : ∀ x f, evalQ x (mul f f) = (evalV x f) ^ 2)
    (p : Q) (hpositive : ∀ x, 0 < evalQ x p)
    {ι : Type v} [Fintype ι] (f : ι → V)
    (hrep : p = ∑ i, mul (f i) (f i)) :
    ∀ x, ∃ i, evalV x (f i) ≠ 0 := by
  intro x
  by_contra h
  have hall : ∀ i, evalV x (f i) = 0 := by
    intro i
    exact not_ne_iff.mp (not_exists.mp h i)
  have hp := hpositive x
  rw [hrep, map_sum] at hp
  simp_rw [hevalMul, hall] at hp
  simpa using hp

/-- Compatibility wrapper converting annihilation of a sum of squares by a supporting
functional into annihilation by its Hankel bilinear form. -/
theorem hankel_sum_eq_zero
    (mul : V → V → Q) (ell : Q →ₗ[ℝ] ℝ)
    (B : LinearMap.BilinForm ℝ V)
    (hB : ∀ x y, B x y = ell (mul x y))
    {ι : Type v} [Fintype ι] (f : ι → V)
    (hsupport : ell (∑ i, mul (f i) (f i)) = 0) :
    ∑ i, B (f i) (f i) = 0 := by
  rw [map_sum] at hsupport
  simpa only [hB] using hsupport

/-- Combined boundary-SOS length theorem in Hankel language.  Its sole remaining geometric input
is `hspans`: strict positivity/basepoint-freeness forces the summands to span the radical. -/
theorem boundary_sos_length_ge_add_one
    (mul : V → V → Q) (ell : Q →ₗ[ℝ] ℝ)
    (B : LinearMap.BilinForm ℝ V) (hPSD : B.IsPosSemidef)
    (hB : ∀ x y, B x y = ell (mul x y))
    {ι : Type v} [Fintype ι] (f : ι → V)
    (hsupport : ell (∑ i, mul (f i) (f i)) = 0)
    (hspans : LinearMap.ker B ≤ Submodule.span ℝ (Set.range f))
    {m : ℕ} (hker : Module.finrank ℝ (LinearMap.ker B) = m + 1) :
    m + 1 ≤ Fintype.card ι :=
  card_ge_add_one_of_finrank_ker_eq B hPSD f
    (hankel_sum_eq_zero mul ell B hB f hsupport) hspans hker

/-- Boundary SOS length with the spanning condition discharged by the exact projective
base-locus property and strict-positivity/no-common-zero input. -/
theorem boundary_sos_length_ge_add_one_of_basepoints
    {X : Type*} (eval : X → Module.Dual ℝ V)
    (mul : V → V → Q) (ell : Q →ₗ[ℝ] ℝ)
    (B : LinearMap.BilinForm ℝ V) (hPSD : B.IsPosSemidef)
    (hB : ∀ x y, B x y = ell (mul x y))
    {ι : Type v} [Fintype ι] (f : ι → V)
    (hsupport : ell (∑ i, mul (f i) (f i)) = 0)
    (hproper : ∀ U : Submodule ℝ V, U < LinearMap.ker B →
      ∃ x : X, ∀ g ∈ U, eval x g = 0)
    (hnoCommonZero : ∀ x : X, ∃ i, eval x (f i) ≠ 0)
    {m : ℕ} (hker : Module.finrank ℝ (LinearMap.ker B) = m + 1) :
    m + 1 ≤ Fintype.card ι := by
  have hsum := hankel_sum_eq_zero mul ell B hB f hsupport
  have hfker := each_mem_ker_of_sum_apply_self_eq_zero B hPSD f hsum
  exact card_ge_add_one_of_finrank_ker_eq B hPSD f hsum
    (ker_le_span_of_no_common_zero B eval f hfker hproper hnoCommonZero) hker

/-- Exact minimality when an `m+1`-square representation is supplied.  Strict positivity derives
the no-common-zero condition for every competing representation, so the preceding lower bound
shows that none can use fewer squares. -/
theorem supplied_add_one_representation_is_minimal
    {X : Type*} (evalV : X → Module.Dual ℝ V) (evalQ : X → Q →ₗ[ℝ] ℝ)
    (mul : V → V → Q)
    (hevalMul : ∀ x f, evalQ x (mul f f) = (evalV x f) ^ 2)
    (ell : Q →ₗ[ℝ] ℝ) (B : LinearMap.BilinForm ℝ V)
    (hPSD : B.IsPosSemidef) (hB : ∀ x y, B x y = ell (mul x y))
    (p : Q) (hpositive : ∀ x, 0 < evalQ x p) (hsupport : ell p = 0)
    (hproper : ∀ U : Submodule ℝ V, U < LinearMap.ker B →
      ∃ x : X, ∀ g ∈ U, evalV x g = 0)
    {m : ℕ} (hker : Module.finrank ℝ (LinearMap.ker B) = m + 1)
    (f₀ : Fin (m + 1) → V) (hrep₀ : p = ∑ i, mul (f₀ i) (f₀ i)) :
    (p = ∑ i, mul (f₀ i) (f₀ i)) ∧
      ∀ {ι : Type v} [Fintype ι] (f : ι → V),
        p = ∑ i, mul (f i) (f i) → m + 1 ≤ Fintype.card ι := by
  refine ⟨hrep₀, ?_⟩
  intro ι inst f hrep
  have hsupport' : ell (∑ i, mul (f i) (f i)) = 0 := by
    rw [← hrep]
    exact hsupport
  exact boundary_sos_length_ge_add_one_of_basepoints evalV mul ell B hPSD hB f hsupport'
    hproper (no_common_zero_of_strictlyPositive_sos evalV evalQ mul hevalMul p
      hpositive f hrep) hker

end Hankel

end SOSKernelLength
