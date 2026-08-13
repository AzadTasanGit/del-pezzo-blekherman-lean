import DelPezzoBlekherman.Fiber.ReciprocalHyperplane
import Mathlib.Analysis.Complex.Basic

noncomputable section

universe u

open scoped BigOperators ComplexConjugate
open Finset

namespace MixedReciprocalHyperplane

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- The unique real relation for `ι` real points and one complex-conjugate pair. -/
def relation (u : ι → ℝ) (v : ℂ) : Module.Dual ℝ ((ι → ℝ) × ℂ) where
  toFun x := ∑ i, u i * x.1 i + 2 * (v * x.2).re
  map_add' x y := by
    simp only [Prod.fst_add, Pi.add_apply, mul_add, Finset.sum_add_distrib, Prod.snd_add,
      Complex.add_re]
    ring
  map_smul' r x := by
    simp only [Prod.smul_fst, Pi.smul_apply, smul_eq_mul, Prod.smul_snd,
      Complex.real_smul]
    simp [mul_left_comm, mul_comm]
    conv_rhs => rw [mul_add, Finset.mul_sum]
    ring

/-- The mixed diagonal pairing associated to real coefficients `a` and complex coefficient `b`. -/
def diagonalPairing (a : ι → ℝ) (b : ℂ) (z : (ι → ℝ) × ℂ) :
    Module.Dual ℝ ((ι → ℝ) × ℂ) where
  toFun x := ∑ i, (a i * z.1 i) * x.1 i + 2 * (b * z.2 * x.2).re
  map_add' x y := by
    simp only [Prod.fst_add, Pi.add_apply, mul_add, Finset.sum_add_distrib, Prod.snd_add,
      Complex.add_re]
    ring
  map_smul' r x := by
    simp only [Prod.smul_fst, Pi.smul_apply, smul_eq_mul, Prod.smul_snd,
      Complex.real_smul]
    simp [mul_assoc, mul_left_comm, mul_comm]
    conv_rhs => rw [mul_add, Finset.mul_sum]
    ring

@[simp]
theorem relation_apply (u : ι → ℝ) (v : ℂ) (x : (ι → ℝ) × ℂ) :
    relation u v x = ∑ i, u i * x.1 i + 2 * (v * x.2).re :=
  rfl

@[simp]
theorem diagonalPairing_apply (a : ι → ℝ) (b : ℂ) (z x : (ι → ℝ) × ℂ) :
    diagonalPairing a b z x =
      ∑ i, (a i * z.1 i) * x.1 i + 2 * (b * z.2 * x.2).re :=
  rfl

/-- Expansion of the complex reciprocal contribution for `b = α + β I`. -/
theorem two_mul_re_sq_div_mk (v : ℂ) (α β : ℝ) :
    2 * (v ^ 2 / (⟨α, β⟩ : ℂ)).re =
      2 * (((v.re ^ 2 - v.im ^ 2) * α + 2 * v.re * v.im * β) /
        (α ^ 2 + β ^ 2)) := by
  rw [Complex.div_re]
  simp only [pow_two, Complex.normSq_mk, Complex.mul_re, Complex.mul_im]
  field_simp
  ring

/-- The mixed reciprocal identity in explicit real coordinates when `b = α + β I`. -/
theorem reciprocal_identity_mk_iff
    (u : ι → ℝ) (v : ℂ) (a : ι → ℝ) (α β : ℝ) :
    ((∑ i, u i ^ 2 / a i) + 2 * (v ^ 2 / (⟨α, β⟩ : ℂ)).re = 0) ↔
      ((∑ i, u i ^ 2 / a i) +
        2 * (((v.re ^ 2 - v.im ^ 2) * α + 2 * v.re * v.im * β) /
          (α ^ 2 + β ^ 2)) = 0) := by
  rw [two_mul_re_sq_div_mk v α β]

/-- After normalizing the complex coefficient of the relation to `1`, nonnegativity of the
mixed diagonal form on that hyperplane forces the real part of `b` to be nonpositive. -/
theorem re_nonpos_of_nonnegative_on_relation_one
    (u : ι → ℝ) (a : ι → ℝ) (b : ℂ)
    (hnonneg : ∀ x, relation u 1 x = 0 → 0 ≤ diagonalPairing a b x x) :
    b.re ≤ 0 := by
  let q : (ι → ℝ) × ℂ := (0, Complex.I)
  have hqH : relation u 1 q = 0 := by
    simp [q, relation]
  have hq := hnonneg q hqH
  simp [q, diagonalPairing, Complex.mul_re] at hq
  linarith

/-- The preceding sign is strict when the pure-imaginary direction is not isotropic. -/
theorem re_neg_of_nonnegative_on_relation_one
    (u : ι → ℝ) (a : ι → ℝ) (b : ℂ)
    (hnonneg : ∀ x, relation u 1 x = 0 → 0 ≤ diagonalPairing a b x x)
    (hnonzero : diagonalPairing a b (0, Complex.I) (0, Complex.I) ≠ 0) :
    b.re < 0 := by
  have hle := re_nonpos_of_nonnegative_on_relation_one u a b hnonneg
  have hne : b.re ≠ 0 := by
    intro hre
    apply hnonzero
    simp [diagonalPairing, Complex.mul_re, hre]
  exact lt_of_le_of_ne hle hne

/-- A nonzero radical vector of the mixed diagonal form on the relation hyperplane forces the
one-conjugate-pair reciprocal identity. -/
theorem reciprocal_identity_of_radical
    (u : ι → ℝ) (v : ℂ) (a : ι → ℝ) (b : ℂ) (z : (ι → ℝ) × ℂ)
    (ha : ∀ i, a i ≠ 0) (hb : b ≠ 0) (hz : z ≠ 0)
    (hzH : relation u v z = 0)
    (hrad : ∀ x, relation u v x = 0 → diagonalPairing a b z x = 0) :
    (∑ i, u i ^ 2 / a i) + 2 * (v ^ 2 / b).re = 0 := by
  have hker : LinearMap.ker (relation u v) ≤ LinearMap.ker (diagonalPairing a b z) := by
    intro x hx
    exact LinearMap.mem_ker.mpr (hrad x (LinearMap.mem_ker.mp hx))
  obtain ⟨t, ht⟩ := LinearMap.exists_smul_of_ker_le_ker
    (relation u v) (diagonalPairing a b z) hker
  have hreal (i : ι) : a i * z.1 i = t * u i := by
    have hi := LinearMap.congr_fun ht (Pi.single i 1, 0)
    simpa [relation, diagonalPairing, Pi.single_apply] using hi.symm
  have hcomplex : b * z.2 = (t : ℂ) * v := by
    apply Complex.ext
    · have h1 := LinearMap.congr_fun ht (0, 1)
      simp [relation, diagonalPairing] at h1
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      linarith
    · have hI := LinearMap.congr_fun ht (0, Complex.I)
      simp [relation, diagonalPairing] at hI
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
      linarith
  have ht0 : t ≠ 0 := by
    intro ht0
    apply hz
    apply Prod.ext
    · funext i
      apply (mul_eq_zero.mp ?_).resolve_left (ha i)
      simpa [ht0] using hreal i
    · apply (mul_eq_zero.mp ?_).resolve_left hb
      simpa [ht0] using hcomplex
  have hzH' : (∑ i, u i * z.1 i) + 2 * (v * z.2).re = 0 := hzH
  have hscaled : t * ((∑ i, u i ^ 2 / a i) + 2 * (v ^ 2 / b).re) = 0 := by
    calc
      t * ((∑ i, u i ^ 2 / a i) + 2 * (v ^ 2 / b).re) =
          (∑ i, u i * z.1 i) + 2 * (v * z.2).re := by
        rw [mul_add, Finset.mul_sum]
        congr 1
        · apply Finset.sum_congr rfl
          intro i _
          calc
            t * (u i ^ 2 / a i) = (t * u i) * u i / a i := by ring
            _ = (a i * z.1 i) * u i / a i := by rw [hreal i]
            _ = u i * z.1 i := by field_simp [ha i]
        · have hc : (t : ℂ) * (v ^ 2 / b) = v * z.2 := by
            calc
              (t : ℂ) * (v ^ 2 / b) = ((t : ℂ) * v) * v / b := by ring
              _ = (b * z.2) * v / b := by rw [hcomplex]
              _ = v * z.2 := by field_simp [hb]
          rw [← hc]
          simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
          ring
      _ = 0 := hzH'
  exact (mul_eq_zero.mp hscaled).resolve_left ht0

/-- Conversely, the mixed reciprocal identity constructs the radical vector
`((uᵢ/aᵢ)ᵢ, v/b)`. -/
theorem radical_of_reciprocal_identity
    (u : ι → ℝ) (v : ℂ) (a : ι → ℝ) (b : ℂ)
    (huv : u ≠ 0 ∨ v ≠ 0) (ha : ∀ i, a i ≠ 0) (hb : b ≠ 0)
    (hrecip : (∑ i, u i ^ 2 / a i) + 2 * (v ^ 2 / b).re = 0) :
    let z : (ι → ℝ) × ℂ := (fun i ↦ u i / a i, v / b)
    z ≠ 0 ∧ relation u v z = 0 ∧
      ∀ x, relation u v x = 0 → diagonalPairing a b z x = 0 := by
  let z : (ι → ℝ) × ℂ := (fun i ↦ u i / a i, v / b)
  have hz : z ≠ 0 := by
    rcases huv with hu | hv
    · intro hz0
      apply hu
      funext i
      have hi : u i / a i = 0 := congrFun (congrArg Prod.fst hz0) i
      exact (div_eq_zero_iff.mp hi).resolve_right (ha i)
    · intro hz0
      apply hv
      have hi : v / b = 0 := congrArg Prod.snd hz0
      exact (div_eq_zero_iff.mp hi).resolve_right hb
  refine ⟨hz, ?_, ?_⟩
  · simpa [z, relation_apply, pow_two, mul_div_assoc] using hrecip
  · intro x hx
    simpa [z, diagonalPairing_apply, ha, hb, mul_div_cancel₀] using hx

end MixedReciprocalHyperplane
