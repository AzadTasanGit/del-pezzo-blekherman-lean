/-
Copyright (c) 2026 Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import DelPezzoBlekherman.LinearAlgebra.HyperplaneInertia
import DelPezzoBlekherman.LinearAlgebra.HyperplaneRadical

/-!
# Real diagonal evaluation forms

This file formalizes the normalization-independent reciprocal vector calculation at
the heart of Lemma 7.1 and Theorem 7.2. The remaining positivity/sign classification
will build on these exact radical computations.
-/

open Finset
open LinearMap (BilinForm)

namespace DelPezzoBlekherman

/-- The diagonal bilinear form with weights `μ`. -/
noncomputable def diagonalBilin {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → ℝ) : BilinForm ℝ (ι → ℝ) :=
  Matrix.toBilin' (Matrix.diagonal μ)

theorem diagonalBilin_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ x y : ι → ℝ) :
    diagonalBilin μ x y = ∑ i, μ i * x i * y i := by
  simp only [diagonalBilin, Matrix.toBilin'_apply, Matrix.diagonal_apply, mul_ite,
    mul_zero, ite_mul, zero_mul, sum_ite_eq, mem_univ, ↓reduceIte]
  congr 1
  funext i
  ring

theorem diagonalBilin_isSymm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → ℝ) : (diagonalBilin μ).IsSymm := by
  rw [LinearMap.BilinForm.isSymm_def]
  intro x y
  simp only [diagonalBilin_apply]
  congr 1
  funext i
  ring

theorem diagonalBilin_nondegenerate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → ℝ) (hμ : ∀ i, μ i ≠ 0) :
    (diagonalBilin μ).Nondegenerate := by
  apply LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr
  rw [Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ ↦ hμ i)

/-- The functional cutting out the degree-one evaluation hyperplane. -/
noncomputable def relationFunctional {ι : Type*} [Fintype ι]
    (u : ι → ℝ) : (ι → ℝ) →ₗ[ℝ] ℝ :=
  (dotProductBilin ℝ ℝ) u

@[simp] theorem relationFunctional_apply {ι : Type*} [Fintype ι]
    (u x : ι → ℝ) :
    relationFunctional u x = ∑ i, u i * x i := by
  rfl

/-- The reciprocal vector `(uᵢ / μᵢ)ᵢ`. -/
noncomputable def reciprocalVector {ι : Type*} (u μ : ι → ℝ) : ι → ℝ :=
  fun i ↦ u i / μ i

/-- The reciprocal coefficient sum `Σ uᵢ² / μᵢ`. -/
noncomputable def reciprocalSum {ι : Type*} [Fintype ι] (u μ : ι → ℝ) : ℝ :=
  ∑ i, u i ^ 2 / μ i

/-- The diagonal form identifies the reciprocal vector with the relation functional. -/
theorem diagonalBilin_reciprocalVector
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u μ x : ι → ℝ) (hμ : ∀ i, μ i ≠ 0) :
    diagonalBilin μ x (reciprocalVector u μ) = relationFunctional u x := by
  simp only [diagonalBilin_apply, reciprocalVector, relationFunctional_apply]
  apply Finset.sum_congr rfl
  intro i _
  field_simp [hμ i]

/-- Evaluating the relation functional on the reciprocal vector is exactly the
reciprocal sum appearing in equation (2) of the paper. -/
theorem relationFunctional_reciprocalVector
    {ι : Type*} [Fintype ι]
    (u μ : ι → ℝ) :
    relationFunctional u (reciprocalVector u μ) = reciprocalSum u μ := by
  simp only [relationFunctional_apply, reciprocalVector, reciprocalSum]
  congr 1
  funext i
  ring

theorem reciprocalVector_ne_zero
    {ι : Type*} [Nonempty ι]
    (u μ : ι → ℝ) (hu : ∀ i, u i ≠ 0) (hμ : ∀ i, μ i ≠ 0) :
    reciprocalVector u μ ≠ 0 := by
  intro h
  let i : ι := Classical.choice ‹Nonempty ι›
  have hi := congr_fun h i
  simp [reciprocalVector, hu i, hμ i] at hi

theorem relationFunctional_ne_zero
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (u : ι → ℝ) (hu : ∀ i, u i ≠ 0) :
    relationFunctional u ≠ 0 := by
  classical
  intro h
  let i : ι := Classical.choice ‹Nonempty ι›
  have hi := LinearMap.congr_fun h (Pi.single i 1)
  simp [relationFunctional_apply, Pi.single_apply, hu i] at hi

/-- Nonzero relation coefficients make their kernel a genuine hyperplane. -/
theorem relationHyperplane_codim_one
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (u : ι → ℝ) (hu : ∀ i, u i ≠ 0) :
    Module.finrank ℝ (LinearMap.ker (relationFunctional u)) + 1 =
      Module.finrank ℝ (ι → ℝ) := by
  classical
  have hs : Function.Surjective (relationFunctional u) := by
    intro z
    let i : ι := Classical.choice ‹Nonempty ι›
    refine ⟨Pi.single i (z / u i), ?_⟩
    simp only [relationFunctional_apply, Pi.single_apply, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    field_simp [hu i]
  have hrange : LinearMap.range (relationFunctional u) = ⊤ :=
    LinearMap.range_eq_top.mpr hs
  have h := (relationFunctional u).finrank_range_add_finrank_ker
  rw [hrange, finrank_top, Module.finrank_self] at h
  omega

/-- If the reciprocal identity holds, the restriction of the diagonal evaluation
form to the degree-one evaluation hyperplane has radical exactly the reciprocal line.
This is the radical assertion in the converse and forward directions of Lemma 7.1. -/
theorem diagonal_hyperplane_radical
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (u μ : ι → ℝ) (hu : ∀ i, u i ≠ 0) (hμ : ∀ i, μ i ≠ 0)
    (hrec : reciprocalSum u μ = 0) :
    (LinearMap.ker ((diagonalBilin μ).restrict
      (LinearMap.ker (relationFunctional u)))).map
        (LinearMap.ker (relationFunctional u)).subtype =
      ℝ ∙ reciprocalVector u μ := by
  apply hyperplane_restriction_radical_span
    (diagonalBilin μ) (diagonalBilin_isSymm μ) (diagonalBilin_nondegenerate μ hμ)
    (relationFunctional u) (reciprocalVector u μ)
    (relationHyperplane_codim_one u hu)
    (reciprocalVector_ne_zero u μ hu hμ)
    (fun x ↦ diagonalBilin_reciprocalVector u μ x hμ)
  rw [relationFunctional_reciprocalVector]
  exact hrec

/-- Positive semidefiniteness on the relation hyperplane allows at most one negative
diagonal coefficient. This is Lemma 6.1 applied to the weighted sum of squares and is
the inertia half of Lemma 7.1. -/
theorem diagonal_at_most_one_negative
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (u μ : ι → ℝ) (hu : ∀ i, u i ≠ 0)
    (hpsd : ((diagonalBilin μ).restrict
      (LinearMap.ker (relationFunctional u))).IsPosSemidef) :
    {i | μ i < 0}.ncard ≤ 1 := by
  have hQ := hyperplane_inertia_bound
    (QuadraticMap.weightedSumSquares ℝ μ)
    (LinearMap.ker (relationFunctional u))
    (relationHyperplane_codim_one u hu) (by
      intro x hx
      have h := hpsd.isNonneg.nonneg ⟨x, hx⟩
      change 0 ≤ diagonalBilin μ x x at h
      rw [diagonalBilin_apply] at h
      simpa [QuadraticMap.weightedSumSquares_apply, smul_eq_mul, pow_two,
        mul_assoc] using h)
  rwa [QuadraticForm.sigNeg_weightedSumSquares] at hQ

/-- With nonzero coefficients, the reciprocal identity cannot hold if every weight
is positive; hence at least one weight is negative. -/
theorem exists_negative_of_reciprocal_zero
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (u μ : ι → ℝ) (hu : ∀ i, u i ≠ 0) (hμ : ∀ i, μ i ≠ 0)
    (hrec : reciprocalSum u μ = 0) :
    ∃ i, μ i < 0 := by
  by_contra hn
  push Not at hn
  have hpos : ∀ i, 0 < μ i := by
    intro i
    exact lt_of_le_of_ne (hn i) (Ne.symm (hμ i))
  have hsumpos : 0 < reciprocalSum u μ := by
    rw [reciprocalSum]
    apply Finset.sum_pos
    · intro i _
      exact div_pos (sq_pos_of_ne_zero (hu i)) (hpos i)
    · exact Finset.univ_nonempty
  linarith

/-- Forward sign classification from Lemma 7.1: under PSD restriction, nonzero
coefficients, and the reciprocal identity, exactly one diagonal weight is negative. -/
theorem diagonal_exactly_one_negative
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (u μ : ι → ℝ) (hu : ∀ i, u i ≠ 0) (hμ : ∀ i, μ i ≠ 0)
    (hpsd : ((diagonalBilin μ).restrict
      (LinearMap.ker (relationFunctional u))).IsPosSemidef)
    (hrec : reciprocalSum u μ = 0) :
    {i | μ i < 0}.ncard = 1 := by
  have hle := diagonal_at_most_one_negative u μ hu hpsd
  obtain ⟨i, hi⟩ := exists_negative_of_reciprocal_zero u μ hu hμ hrec
  have hpos : 0 < {i | μ i < 0}.ncard :=
    (Set.ncard_pos (s := {i | μ i < 0})).mpr ⟨i, hi⟩
  omega

/-- Weighted Cauchy--Schwarz converse in Lemma 7.1. If `j` is the unique negative
coefficient and the reciprocal identity holds, the diagonal form is nonnegative on
the relation hyperplane. -/
theorem diagonal_nonneg_on_hyperplane_of_distinguished_negative
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u μ : ι → ℝ) (j : ι)
    (hu : ∀ i, u i ≠ 0) (hμ : ∀ i, μ i ≠ 0)
    (hneg : μ j < 0) (hpos : ∀ i, i ≠ j → 0 < μ i)
    (hrec : reciprocalSum u μ = 0)
    (x : ι → ℝ) (hx : x ∈ LinearMap.ker (relationFunctional u)) :
    0 ≤ diagonalBilin μ x x := by
  let s : Finset ι := Finset.univ.erase j
  let S : ℝ := ∑ i ∈ s, u i ^ 2 / μ i
  have hsplitRec : S + u j ^ 2 / μ j = 0 := by
    have h := hrec
    rw [reciprocalSum] at h
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)] at h
    exact h
  have hS : 0 < S := by
    have hjterm : u j ^ 2 / μ j < 0 :=
      div_neg_of_pos_of_neg (sq_pos_of_ne_zero (hu j)) hneg
    linarith
  have hsplitRel : (∑ i ∈ s, u i * x i) + u j * x j = 0 := by
    have h0 := LinearMap.mem_ker.mp hx
    simp only [relationFunctional_apply] at h0
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)] at h0
    exact h0
  have hg : ∀ i ∈ s, 0 < u i ^ 2 / μ i := by
    intro i hi
    apply div_pos (sq_pos_of_ne_zero (hu i))
    apply hpos i
    exact (Finset.mem_erase.mp hi).1
  have hcs := Finset.sq_sum_div_le_sum_sq_div s (fun i ↦ u i * x i) hg
  have hrhs : (∑ i ∈ s, (u i * x i) ^ 2 / (u i ^ 2 / μ i)) =
      ∑ i ∈ s, μ i * x i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    field_simp [hu i, hμ i]
  rw [hrhs] at hcs
  change (∑ i ∈ s, u i * x i) ^ 2 / S ≤ ∑ i ∈ s, μ i * x i ^ 2 at hcs
  have hleft : (∑ i ∈ s, u i * x i) ^ 2 / S = -(μ j * x j ^ 2) := by
    have hj : u j ^ 2 / μ j = -S := by linarith
    have hrel : (∑ i ∈ s, u i * x i) = -(u j * x j) := by linarith
    rw [hrel]
    have hS0 : S ≠ 0 := ne_of_gt hS
    have hmj0 := hμ j
    field_simp [hmj0] at hj
    field_simp [hS0]
    ring_nf at hj ⊢
    nlinarith
  rw [hleft] at hcs
  rw [diagonalBilin_apply]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
  ring_nf at hcs ⊢
  linarith

/-- Bundled PSD version of the preceding weighted Cauchy--Schwarz theorem. -/
theorem diagonal_psd_on_hyperplane_of_distinguished_negative
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u μ : ι → ℝ) (j : ι)
    (hu : ∀ i, u i ≠ 0) (hμ : ∀ i, μ i ≠ 0)
    (hneg : μ j < 0) (hpos : ∀ i, i ≠ j → 0 < μ i)
    (hrec : reciprocalSum u μ = 0) :
    ((diagonalBilin μ).restrict
      (LinearMap.ker (relationFunctional u))).IsPosSemidef := by
  refine ⟨(diagonalBilin_isSymm μ).restrict _, ?_⟩
  constructor
  intro x
  exact diagonal_nonneg_on_hyperplane_of_distinguished_negative
    u μ j hu hμ hneg hpos hrec x x.property

/-- If the mapped restricted radical is the reciprocal line, then the reciprocal
identity is necessary. -/
theorem reciprocal_zero_of_radical_eq_span
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (u μ : ι → ℝ)
    (hrad : (LinearMap.ker ((diagonalBilin μ).restrict
      (LinearMap.ker (relationFunctional u)))).map
        (LinearMap.ker (relationFunctional u)).subtype =
      ℝ ∙ reciprocalVector u μ) :
    reciprocalSum u μ = 0 := by
  have hrho : reciprocalVector u μ ∈ ℝ ∙ reciprocalVector u μ :=
    Submodule.mem_span_singleton_self _
  rw [← hrad] at hrho
  rcases hrho with ⟨y, _, hval⟩
  have hmem : reciprocalVector u μ ∈ LinearMap.ker (relationFunctional u) := by
    rw [← hval]
    exact y.property
  have hz := LinearMap.mem_ker.mp hmem
  rw [relationFunctional_reciprocalVector] at hz
  exact hz

/-- Kernel-face form of Lemma 7.1. For nonzero relation and diagonal coefficients,
PSD restriction with radical equal to the reciprocal line is equivalent to the
existence of exactly one negative coefficient and the reciprocal identity.

The right side names the negative index `j`, which is equivalent to the paper's
phrase "exactly one `μᵢ` is negative". -/
theorem diagonal_kernel_face_classification
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (u μ : ι → ℝ) (hu : ∀ i, u i ≠ 0) (hμ : ∀ i, μ i ≠ 0) :
    (((diagonalBilin μ).restrict
        (LinearMap.ker (relationFunctional u))).IsPosSemidef ∧
      (LinearMap.ker ((diagonalBilin μ).restrict
        (LinearMap.ker (relationFunctional u)))).map
          (LinearMap.ker (relationFunctional u)).subtype =
        ℝ ∙ reciprocalVector u μ) ↔
      ∃ j, μ j < 0 ∧ (∀ i, i ≠ j → 0 < μ i) ∧ reciprocalSum u μ = 0 := by
  constructor
  · rintro ⟨hpsd, hrad⟩
    have hrec := reciprocal_zero_of_radical_eq_span u μ hrad
    have hone := diagonal_exactly_one_negative u μ hu hμ hpsd hrec
    obtain ⟨j, hjset⟩ := Set.ncard_eq_one.mp hone
    refine ⟨j, ?_, ?_, hrec⟩
    · have : j ∈ ({i | μ i < 0} : Set ι) := by rw [hjset]; simp
      exact this
    · intro i hij
      have hnonneg : 0 ≤ μ i := by
        by_contra hn
        have hilt : μ i < 0 := lt_of_not_ge hn
        have himem : i ∈ ({k | μ k < 0} : Set ι) := hilt
        rw [hjset] at himem
        exact hij (Set.mem_singleton_iff.mp himem)
      exact lt_of_le_of_ne hnonneg (Ne.symm (hμ i))
  · rintro ⟨j, hneg, hpos, hrec⟩
    exact ⟨diagonal_psd_on_hyperplane_of_distinguished_negative
      u μ j hu hμ hneg hpos hrec,
      diagonal_hyperplane_radical u μ hu hμ hrec⟩

end DelPezzoBlekherman
