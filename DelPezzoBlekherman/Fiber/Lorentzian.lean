/-
Copyright (c) 2026 Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import DelPezzoBlekherman.Fiber.RealDiagonal

/-!
# Lorentzian evaluation forms

This file proves the real/complex hyperplane calculation used in Lemma 7.3.  It
combines a positive real diagonal block with the real bilinear form
`2 * re (b * w * z)` on one complex coordinate.  The kernel-face condition is
shown to be equivalent to the reciprocal scalar identity from the paper.
-/

open LinearMap (BilinForm)

namespace DelPezzoBlekherman

/-- The real bilinear form whose quadratic form is `2 * re (b * w²)`. -/
noncomputable def complexSquareBilin (b : ℂ) : BilinForm ℝ ℂ :=
  LinearMap.mk₂ ℝ (fun w z : ℂ ↦ 2 * (b * w * z).re)
    (by intro w₁ w₂ z; simp [add_mul, mul_add])
    (by intro c w z; simp [mul_assoc]; ring)
    (by intro w z₁ z₂; simp [add_mul, mul_add])
    (by intro c w z; simp [mul_assoc]; ring)

@[simp] theorem complexSquareBilin_apply (b w z : ℂ) :
    complexSquareBilin b w z = 2 * (b * w * z).re := rfl

theorem complexSquareBilin_isSymm (b : ℂ) : (complexSquareBilin b).IsSymm := by
  rw [LinearMap.BilinForm.isSymm_def]
  intro w z
  simp only [complexSquareBilin_apply]
  congr 2
  ring

theorem complexSquareBilin_nondegenerate (b : ℂ) (hb : b ≠ 0) :
    (complexSquareBilin b).Nondegenerate := by
  have hleft : (complexSquareBilin b).SeparatingLeft := by
    intro w hw
    by_contra hw0
    have hbw : b * w ≠ 0 := mul_ne_zero hb hw0
    have hz := hw ((b * w)⁻¹)
    simp only [complexSquareBilin_apply] at hz
    rw [mul_inv_cancel₀ hbw] at hz
    norm_num at hz
  refine ⟨hleft, ?_⟩
  intro z hz
  apply hleft z
  intro w
  rw [(complexSquareBilin_isSymm b).eq]
  exact hz w

theorem complexSquareBilin_mul_I_self (b w : ℂ) :
    complexSquareBilin b (Complex.I * w) (Complex.I * w) =
      -complexSquareBilin b w w := by
  simp only [complexSquareBilin_apply, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im]
  ring

/-- Every nonzero complex square block contains a negative direction. -/
theorem complexSquareBilin_exists_negative (b : ℂ) (hb : b ≠ 0) :
    ∃ w : ℂ, complexSquareBilin b w w < 0 := by
  by_contra hn
  push Not at hn
  have hall : ∀ w : ℂ, complexSquareBilin b w w = 0 := by
    intro w
    have hw := hn w
    have hiw := hn (Complex.I * w)
    rw [complexSquareBilin_mul_I_self] at hiw
    linarith
  have hcross : complexSquareBilin b 1 b⁻¹ = 0 := by
    have hadd := hall (1 + b⁻¹)
    have h1 := hall 1
    have hinv := hall b⁻¹
    have hadd' : complexSquareBilin b 1 1 + complexSquareBilin b b⁻¹ 1 +
        (complexSquareBilin b 1 b⁻¹ + complexSquareBilin b b⁻¹ b⁻¹) = 0 := by
      simpa only [map_add, LinearMap.add_apply] using hadd
    have hsymcross : complexSquareBilin b b⁻¹ 1 = complexSquareBilin b 1 b⁻¹ :=
      (complexSquareBilin_isSymm b).eq _ _
    linarith
  rw [complexSquareBilin_apply] at hcross
  field_simp [hb] at hcross
  norm_num at hcross

/-- The orthogonal sum of a real diagonal form and one complex square block. -/
noncomputable def lorentzBilin {iota : Type*} [Fintype iota] [DecidableEq iota]
    (a : iota → ℝ) (b : ℂ) : BilinForm ℝ ((iota → ℝ) × ℂ) :=
  LinearMap.mk₂ ℝ
    (fun X Y ↦ diagonalBilin a X.1 Y.1 + complexSquareBilin b X.2 Y.2)
    (by intro X Y Z; simp; ring)
    (by intro c X Y; simp; ring)
    (by intro X Y Z; simp; ring)
    (by intro c X Y; simp; ring)

@[simp] theorem lorentzBilin_apply {iota : Type*} [Fintype iota] [DecidableEq iota]
    (a : iota → ℝ) (b : ℂ) (X Y : (iota → ℝ) × ℂ) :
    lorentzBilin a b X Y =
      diagonalBilin a X.1 Y.1 + complexSquareBilin b X.2 Y.2 := rfl

theorem lorentzBilin_isSymm {iota : Type*} [Fintype iota] [DecidableEq iota]
    (a : iota → ℝ) (b : ℂ) : (lorentzBilin a b).IsSymm := by
  rw [LinearMap.BilinForm.isSymm_def]
  intro X Y
  simp only [lorentzBilin_apply]
  rw [(diagonalBilin_isSymm a).eq, (complexSquareBilin_isSymm b).eq]

theorem lorentzBilin_nondegenerate {iota : Type*} [Fintype iota] [DecidableEq iota]
    (a : iota → ℝ) (b : ℂ) (ha : ∀ i, a i ≠ 0) (hb : b ≠ 0) :
    (lorentzBilin a b).Nondegenerate := by
  have hdiag := diagonalBilin_nondegenerate a ha
  have hcomplex := complexSquareBilin_nondegenerate b hb
  have hleft : (lorentzBilin a b).SeparatingLeft := by
    intro X hX
    have hx : X.1 = 0 := by
      apply hdiag.1 X.1
      intro y
      have h := hX (y, 0)
      simpa using h
    have hz : X.2 = 0 := by
      apply hcomplex.1 X.2
      intro z
      have h := hX (0, z)
      simpa using h
    exact Prod.ext hx hz
  refine ⟨hleft, ?_⟩
  intro Y hY
  apply hleft Y
  intro X
  rw [(lorentzBilin_isSymm a b).eq]
  exact hY X

noncomputable def complexRelationFunctional (v : ℂ) : ℂ →ₗ[ℝ] ℝ where
  toFun w := 2 * (v * w).re
  map_add' w z := by simp [mul_add]
  map_smul' c w := by simp; ring

@[simp] theorem complexRelationFunctional_apply (v w : ℂ) :
    complexRelationFunctional v w = 2 * (v * w).re := rfl

/-- The real relation functional on the mixed real/complex evaluation space. -/
noncomputable def lorentzRelation {iota : Type*} [Fintype iota]
    (u : iota → ℝ) (v : ℂ) : ((iota → ℝ) × ℂ) →ₗ[ℝ] ℝ where
  toFun X := relationFunctional u X.1 + complexRelationFunctional v X.2
  map_add' X Y := by
    change relationFunctional u (X.1 + Y.1) +
        complexRelationFunctional v (X.2 + Y.2) = _
    rw [map_add, map_add]
    ring
  map_smul' c X := by simp; ring

@[simp] theorem lorentzRelation_apply {iota : Type*} [Fintype iota]
    (u : iota → ℝ) (v : ℂ) (X : (iota → ℝ) × ℂ) :
    lorentzRelation u v X = relationFunctional u X.1 + 2 * (v * X.2).re := rfl

/-- The vector representing the relation functional under `lorentzBilin`. -/
noncomputable def lorentzReciprocal {iota : Type*}
    (u a : iota → ℝ) (v b : ℂ) : (iota → ℝ) × ℂ :=
  (reciprocalVector u a, v / b)

/-- The reciprocal scalar appearing in Lemma 7.3. -/
noncomputable def lorentzReciprocalSum {iota : Type*} [Fintype iota]
    (u a : iota → ℝ) (v b : ℂ) : ℝ :=
  reciprocalSum u a + 2 * (v ^ 2 / b).re

theorem lorentzBilin_reciprocal {iota : Type*} [Fintype iota] [DecidableEq iota]
    (u a : iota → ℝ) (v b : ℂ) (X : (iota → ℝ) × ℂ)
    (ha : ∀ i, a i ≠ 0) (hb : b ≠ 0) :
    lorentzBilin a b X (lorentzReciprocal u a v b) = lorentzRelation u v X := by
  simp only [lorentzBilin_apply, lorentzReciprocal, lorentzRelation_apply]
  rw [diagonalBilin_reciprocalVector u a X.1 ha]
  congr 1
  rw [complexSquareBilin_apply]
  congr 2
  field_simp [hb]

theorem lorentzRelation_reciprocal {iota : Type*} [Fintype iota]
    (u a : iota → ℝ) (v b : ℂ) :
    lorentzRelation u v (lorentzReciprocal u a v b) =
      lorentzReciprocalSum u a v b := by
  simp only [lorentzRelation_apply, lorentzReciprocal,
    relationFunctional_reciprocalVector, lorentzReciprocalSum]
  congr 1
  congr 2
  ring

theorem lorentzRelation_surjective {iota : Type*} [Fintype iota] [Nonempty iota]
    (u : iota → ℝ) (v : ℂ) (hu : ∀ i, u i ≠ 0) :
    Function.Surjective (lorentzRelation u v) := by
  classical
  intro z
  let i : iota := Classical.choice ‹Nonempty iota›
  refine ⟨(Pi.single i (z / u i), 0), ?_⟩
  simp only [lorentzRelation_apply, relationFunctional_apply, Pi.single_apply,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  field_simp [hu i]
  norm_num

theorem lorentzRelationHyperplane_codim_one
    {iota : Type*} [Fintype iota] [Nonempty iota]
    (u : iota → ℝ) (v : ℂ) (hu : ∀ i, u i ≠ 0) :
    Module.finrank ℝ (LinearMap.ker (lorentzRelation u v)) + 1 =
      Module.finrank ℝ ((iota → ℝ) × ℂ) := by
  have hrange : LinearMap.range (lorentzRelation u v) = ⊤ :=
    LinearMap.range_eq_top.mpr (lorentzRelation_surjective u v hu)
  have h := (lorentzRelation u v).finrank_range_add_finrank_ker
  rw [hrange, finrank_top, Module.finrank_self] at h
  omega

theorem lorentzReciprocal_ne_zero
    {iota : Type*} [Nonempty iota]
    (u a : iota → ℝ) (v b : ℂ) (hu : ∀ i, u i ≠ 0) (ha : ∀ i, a i ≠ 0) :
    lorentzReciprocal u a v b ≠ 0 := by
  intro h
  have hfirst : reciprocalVector u a = 0 := congrArg Prod.fst h
  exact reciprocalVector_ne_zero u a hu ha hfirst

theorem lorentz_hyperplane_radical
    {iota : Type*} [Fintype iota] [Nonempty iota] [DecidableEq iota]
    (u a : iota → ℝ) (v b : ℂ)
    (hu : ∀ i, u i ≠ 0) (ha : ∀ i, a i ≠ 0) (hb : b ≠ 0)
    (hrec : lorentzReciprocalSum u a v b = 0) :
    (LinearMap.ker ((lorentzBilin a b).restrict
      (LinearMap.ker (lorentzRelation u v)))).map
        (LinearMap.ker (lorentzRelation u v)).subtype =
      ℝ ∙ lorentzReciprocal u a v b := by
  apply hyperplane_restriction_radical_span
    (lorentzBilin a b) (lorentzBilin_isSymm a b)
    (lorentzBilin_nondegenerate a b ha hb)
    (lorentzRelation u v) (lorentzReciprocal u a v b)
    (lorentzRelationHyperplane_codim_one u v hu)
    (lorentzReciprocal_ne_zero u a v b hu ha)
    (fun X ↦ lorentzBilin_reciprocal u a v b X ha hb)
  rw [lorentzRelation_reciprocal]
  exact hrec

/-- The normalized two-real-dimensional inequality behind the Lorentzian case. -/
theorem normalized_complex_null_inequality
    (S : ℝ) (t z : ℂ) (hS : 0 < S) (hrel : S + 2 * t.re = 0) :
    0 ≤ (2 * (t * z).re) ^ 2 / S + 2 * (t * z ^ 2).re := by
  have ht : t.re < 0 := by linarith
  have hSeq : S = -2 * t.re := by linarith
  simp only [pow_two, Complex.mul_re, Complex.mul_im] at ⊢
  rw [hSeq]
  field_simp [ne_of_lt ht]
  ring_nf
  have hinv : t.re⁻¹ < 0 := inv_lt_zero.mpr ht
  nlinarith [mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg (add_nonneg (sq_nonneg t.re) (sq_nonneg t.im)) (sq_nonneg z.im))
    (le_of_lt hinv)]

theorem complex_null_inequality
    (S : ℝ) (v b w : ℂ) (hS : 0 < S) (hb : b ≠ 0)
    (hrel : S + 2 * (v ^ 2 / b).re = 0) :
    0 ≤ (2 * (v * w).re) ^ 2 / S + 2 * (b * w ^ 2).re := by
  have hv : v ≠ 0 := by
    intro hv
    subst v
    norm_num at hrel
    linarith
  let t : ℂ := v ^ 2 / b
  let z : ℂ := b * w / v
  have htz : t * z = v * w := by
    dsimp [t, z]
    field_simp [hb, hv]
  have htz2 : t * z ^ 2 = b * w ^ 2 := by
    dsimp [t, z]
    field_simp [hb, hv]
  have h := normalized_complex_null_inequality S t z hS hrel
  rwa [htz, htz2] at h

/-- Weighted Cauchy--Schwarz together with the complex null inequality proves
nonnegativity on the relation hyperplane. -/
theorem lorentz_nonneg_on_hyperplane
    {iota : Type*} [Fintype iota] [Nonempty iota] [DecidableEq iota]
    (u a : iota → ℝ) (v b : ℂ)
    (hu : ∀ i, u i ≠ 0) (ha : ∀ i, 0 < a i) (hb : b ≠ 0)
    (hrec : lorentzReciprocalSum u a v b = 0)
    (X : (iota → ℝ) × ℂ) (hX : X ∈ LinearMap.ker (lorentzRelation u v)) :
    0 ≤ lorentzBilin a b X X := by
  let S : ℝ := reciprocalSum u a
  have hS : 0 < S := by
    dsimp [S, reciprocalSum]
    apply Finset.sum_pos
    · intro i _
      exact div_pos (sq_pos_of_ne_zero (hu i)) (ha i)
    · exact Finset.univ_nonempty
  have hg : ∀ i ∈ (Finset.univ : Finset iota), 0 < u i ^ 2 / a i := by
    intro i _
    exact div_pos (sq_pos_of_ne_zero (hu i)) (ha i)
  have hcs := Finset.sq_sum_div_le_sum_sq_div
    (Finset.univ : Finset iota) (fun i ↦ u i * X.1 i) hg
  have hrhs : (∑ i, (u i * X.1 i) ^ 2 / (u i ^ 2 / a i)) =
      ∑ i, a i * X.1 i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    field_simp [hu i, ne_of_gt (ha i)]
  rw [hrhs] at hcs
  change (∑ i, u i * X.1 i) ^ 2 / S ≤ ∑ i, a i * X.1 i ^ 2 at hcs
  have hrelation : (∑ i, u i * X.1 i) + 2 * (v * X.2).re = 0 := by
    simpa only [LinearMap.mem_ker, lorentzRelation_apply, relationFunctional_apply]
      using hX
  have hsquare : (∑ i, u i * X.1 i) ^ 2 = (2 * (v * X.2).re) ^ 2 := by
    have heq : (∑ i, u i * X.1 i) = -(2 * (v * X.2).re) := by linarith
    rw [heq]
    ring
  rw [hsquare] at hcs
  have hscalar : S + 2 * (v ^ 2 / b).re = 0 := by
    exact hrec
  have hc := complex_null_inequality S v b X.2 hS hb hscalar
  rw [lorentzBilin_apply, diagonalBilin_apply, complexSquareBilin_apply]
  simp only [pow_two] at hcs hc ⊢
  ring_nf at hcs hc ⊢
  linarith

theorem lorentz_psd_on_hyperplane
    {iota : Type*} [Fintype iota] [Nonempty iota] [DecidableEq iota]
    (u a : iota → ℝ) (v b : ℂ)
    (hu : ∀ i, u i ≠ 0) (ha : ∀ i, 0 < a i) (hb : b ≠ 0)
    (hrec : lorentzReciprocalSum u a v b = 0) :
    ((lorentzBilin a b).restrict
      (LinearMap.ker (lorentzRelation u v))).IsPosSemidef := by
  refine ⟨(lorentzBilin_isSymm a b).restrict _, ?_⟩
  constructor
  intro X
  exact lorentz_nonneg_on_hyperplane u a v b hu ha hb hrec X X.property

theorem lorentz_reciprocal_zero_of_radical_eq_span
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (u a : iota → ℝ) (v b : ℂ)
    (hrad : (LinearMap.ker ((lorentzBilin a b).restrict
      (LinearMap.ker (lorentzRelation u v)))).map
        (LinearMap.ker (lorentzRelation u v)).subtype =
      ℝ ∙ lorentzReciprocal u a v b) :
    lorentzReciprocalSum u a v b = 0 := by
  have hrho : lorentzReciprocal u a v b ∈ ℝ ∙ lorentzReciprocal u a v b :=
    Submodule.mem_span_singleton_self _
  rw [← hrad] at hrho
  rcases hrho with ⟨Y, _, hval⟩
  have hmem : lorentzReciprocal u a v b ∈
      LinearMap.ker (lorentzRelation u v) := by
    rw [← hval]
    exact Y.property
  have hz := LinearMap.mem_ker.mp hmem
  rw [lorentzRelation_reciprocal] at hz
  exact hz

/-- The Lorentzian hyperplane lemma (Lemma 7.3): when all real diagonal
coefficients are positive, the kernel-face condition is equivalent to the single
real reciprocal identity. -/
theorem lorentz_kernel_face_classification
    {iota : Type*} [Fintype iota] [Nonempty iota] [DecidableEq iota]
    (u a : iota → ℝ) (v b : ℂ)
    (hu : ∀ i, u i ≠ 0) (ha : ∀ i, 0 < a i) (hb : b ≠ 0) :
    (((lorentzBilin a b).restrict
        (LinearMap.ker (lorentzRelation u v))).IsPosSemidef ∧
      (LinearMap.ker ((lorentzBilin a b).restrict
        (LinearMap.ker (lorentzRelation u v)))).map
          (LinearMap.ker (lorentzRelation u v)).subtype =
        ℝ ∙ lorentzReciprocal u a v b) ↔
      lorentzReciprocalSum u a v b = 0 := by
  constructor
  · rintro ⟨_, hrad⟩
    exact lorentz_reciprocal_zero_of_radical_eq_span u a v b hrad
  · intro hrec
    have ha0 : ∀ i, a i ≠ 0 := fun i ↦ ne_of_gt (ha i)
    exact ⟨lorentz_psd_on_hyperplane u a v b hu ha hb hrec,
      lorentz_hyperplane_radical u a v b hu ha0 hb hrec⟩

/-- A nonzero complex block already supplies the unique negative direction allowed
by a PSD hyperplane restriction, so every nonzero real diagonal coefficient must
be positive. -/
theorem lorentz_real_coefficients_positive_of_psd
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (u a : iota → ℝ) (v b : ℂ)
    (hu : ∀ i, u i ≠ 0) (ha0 : ∀ i, a i ≠ 0) (hb : b ≠ 0)
    (hpsd : ((lorentzBilin a b).restrict
      (LinearMap.ker (lorentzRelation u v))).IsPosSemidef) :
    ∀ i, 0 < a i := by
  intro i
  apply lt_of_le_of_ne
  · by_contra hn
    push Not at hn
    have hai : a i < 0 := hn
    obtain ⟨w, hw⟩ := complexSquareBilin_exists_negative b hb
    let x : iota → ℝ := Pi.single i (-(2 * (v * w).re) / u i)
    let X : (iota → ℝ) × ℂ := (x, w)
    have hrel : X ∈ LinearMap.ker (lorentzRelation u v) := by
      rw [LinearMap.mem_ker]
      simp only [lorentzRelation_apply, relationFunctional_apply, X, x,
        Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      field_simp [hu i]
      ring
    have hnonneg := hpsd.isNonneg.nonneg ⟨X, hrel⟩
    change 0 ≤ lorentzBilin a b X X at hnonneg
    rw [lorentzBilin_apply, diagonalBilin_apply] at hnonneg
    have hdiag : (∑ j, a j * X.1 j * X.1 j) ≤ 0 := by
      simp only [X, x, Pi.single_apply, mul_ite, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      have hp := mul_nonpos_of_nonpos_of_nonneg (le_of_lt hai)
        (sq_nonneg (-(2 * (v * w).re) / u i))
      simpa [pow_two, mul_assoc] using hp
    linarith
  · exact Ne.symm (ha0 i)

/-- Finite-dimensional coefficient classification for one conjugate pair: the
kernel-face condition is equivalent to positivity of all real coefficients and the
single Lorentzian reciprocal identity.  This is the linear-algebraic core of
Theorem 7.4 before its geometric evaluation bridge and final normalization. -/
theorem lorentz_one_pair_kernel_face_classification
    {iota : Type*} [Fintype iota] [Nonempty iota] [DecidableEq iota]
    (u a : iota → ℝ) (v b : ℂ)
    (hu : ∀ i, u i ≠ 0) (ha0 : ∀ i, a i ≠ 0) (hb : b ≠ 0) :
    (((lorentzBilin a b).restrict
        (LinearMap.ker (lorentzRelation u v))).IsPosSemidef ∧
      (LinearMap.ker ((lorentzBilin a b).restrict
        (LinearMap.ker (lorentzRelation u v)))).map
          (LinearMap.ker (lorentzRelation u v)).subtype =
        ℝ ∙ lorentzReciprocal u a v b) ↔
      (∀ i, 0 < a i) ∧ lorentzReciprocalSum u a v b = 0 := by
  constructor
  · rintro ⟨hpsd, hrad⟩
    exact ⟨lorentz_real_coefficients_positive_of_psd u a v b hu ha0 hb hpsd,
      lorentz_reciprocal_zero_of_radical_eq_span u a v b hrad⟩
  · rintro ⟨ha, hrec⟩
    exact (lorentz_kernel_face_classification u a v b hu ha hb).mpr hrec

end DelPezzoBlekherman
