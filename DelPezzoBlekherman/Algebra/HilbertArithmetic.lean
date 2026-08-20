/-
Copyright (c) 2026 Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import Mathlib.Data.Int.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Hilbert-series arithmetic

This file records the polynomial arithmetic in Proposition 2.1.  The expressions
are doubled to avoid division by two: `n(n-1)` is twice the dimension of quadratic
forms on an `n`-dimensional space.
-/

namespace DelPezzoBlekherman

open PowerSeries

/-- The coefficient of `t` in `(1 + c t + t²)/(1-t)^(m+1)`. -/
def hilbertDegreeOne (m c : ℕ) : ℕ := m + 1 + c

/-- The coefficient of `t²` in `(1 + c t + t²)/(1-t)^(m+1)`. -/
def hilbertDegreeTwo (m c : ℕ) : ℕ :=
  (m + 2) * (m + 1) / 2 + c * (m + 1) + 1

/-- The exact formal power series
`(1 + c t + t²) / (1 - t)^(m+1)` from PDF equation (1), with integer coefficients. -/
noncomputable def delPezzoHilbertSeries (m c : ℕ) : PowerSeries ℤ :=
  (1 + C (c : ℤ) * X + X ^ 2) * (invOneSubPow ℤ (m + 1)).val

/-- The Hilbert series of the Artinian reduction in Proposition 2.2. -/
noncomputable def delPezzoHilbertNumerator (c : ℕ) : PowerSeries ℤ :=
  1 + C (c : ℤ) * X + X ^ 2

private theorem coeff_natCast_of_pos (c n : ℕ) (hn : 0 < n) :
    coeff n (c : PowerSeries ℤ) = 0 := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [Nat.cast_succ, map_add, ih]
    simp [coeff_one, hn.ne']

/-- Multiplication by the denominator cancels equation (1) and gives the Artinian numerator
`1+c t+t²`, exactly as used after quotienting by a linear regular sequence. -/
theorem delPezzoHilbertSeries_mul_one_sub_pow (m c : ℕ) :
    delPezzoHilbertSeries m c * (1 - X) ^ (m + 1) =
      delPezzoHilbertNumerator c := by
  rw [delPezzoHilbertSeries, delPezzoHilbertNumerator, mul_assoc,
    ← invOneSubPow_inv_eq_one_sub_pow]
  rw [(invOneSubPow ℤ (m + 1)).val_inv, mul_one]

/-- The Artinian numerator has degree-zero coefficient one. -/
theorem coeff_zero_delPezzoHilbertNumerator (c : ℕ) :
    coeff 0 (delPezzoHilbertNumerator c) = 1 := by
  simp [delPezzoHilbertNumerator]

/-- The Artinian numerator has degree-one coefficient `c`. -/
theorem coeff_one_delPezzoHilbertNumerator (c : ℕ) :
    coeff 1 (delPezzoHilbertNumerator c) = c := by
  norm_num [delPezzoHilbertNumerator, coeff_mul, Finset.Nat.antidiagonal_succ]

/-- The Artinian numerator has degree-two coefficient one. -/
theorem coeff_two_delPezzoHilbertNumerator (c : ℕ) :
    coeff 2 (delPezzoHilbertNumerator c) = 1 := by
  norm_num [delPezzoHilbertNumerator, coeff_mul, Finset.Nat.antidiagonal_succ,
    PowerSeries.coeff_X, PowerSeries.coeff_C]
  rw [coeff_natCast_of_pos c 1 (by omega)]

/-- All coefficients of the Artinian numerator above degree two vanish. -/
theorem coeff_delPezzoHilbertNumerator_eq_zero_of_three_le
    (c : ℕ) {d : ℕ} (hd : 3 ≤ d) :
    coeff d (delPezzoHilbertNumerator c) = 0 := by
  have hcx : coeff d ((c : PowerSeries ℤ) * X) = 0 := by
    rw [show (X : PowerSeries ℤ) = X ^ 1 by simp, coeff_mul_X_pow']
    rw [if_pos (by omega)]
    exact coeff_natCast_of_pos c (d - 1) (by omega)
  simp [delPezzoHilbertNumerator, hcx, coeff_X_pow,
    show d ≠ 0 by omega, show d ≠ 2 by omega]

/-- The constant coefficient of the PDF Hilbert series is one. -/
theorem coeff_zero_delPezzoHilbertSeries (m c : ℕ) :
    coeff 0 (delPezzoHilbertSeries m c) = 1 := by
  simp [delPezzoHilbertSeries, invOneSubPow_val_succ_eq_mk_add_choose]

/-- Formal coefficient extraction in degree one gives `m+c+1`. -/
theorem coeff_one_delPezzoHilbertSeries (m c : ℕ) :
    coeff 1 (delPezzoHilbertSeries m c) = hilbertDegreeOne m c := by
  norm_num [delPezzoHilbertSeries, hilbertDegreeOne,
    invOneSubPow_val_succ_eq_mk_add_choose, coeff_mul, Finset.Nat.antidiagonal_succ]

/-- Formal coefficient extraction in degree two gives the quadratic expression used in
Proposition 2.1. -/
theorem coeff_two_delPezzoHilbertSeries (m c : ℕ) :
    coeff 2 (delPezzoHilbertSeries m c) = hilbertDegreeTwo m c := by
  rw [show hilbertDegreeTwo m c = Nat.choose (m + 2) 2 + c * (m + 1) + 1 by
    simp [hilbertDegreeTwo, Nat.choose_two_right]]
  norm_num [delPezzoHilbertSeries, invOneSubPow_val_succ_eq_mk_add_choose, coeff_mul,
    Finset.Nat.antidiagonal_succ, PowerSeries.coeff_X, PowerSeries.coeff_C]
  rw [Nat.choose_symm_add (a := m) (b := 2)]
  have hc : PowerSeries.coeff 1 (c : PowerSeries ℤ) = 0 := by
    induction c with
    | zero => simp
    | succ c ih =>
      rw [Nat.cast_succ, map_add, ih]
      simp
  rw [hc]
  omega

section GradedComponents

universe u v

variable {K : Type u} {A : Type v}
variable [Field K] [AddCommGroup A] [Module K A]

/-- A concrete bridge from a family of homogeneous components to equation (1): the integer
coefficient of the PDF's formal Hilbert series equals the finrank of every component.  This
isolates the missing construction of a Hilbert series for an internally graded algebra while
making all coefficient consequences machine-checked. -/
structure DelPezzoHilbertSeriesCertificate
    (𝒜 : ℕ → Submodule K A) (m c : ℕ) : Prop where
  finrank_eq_coeff : ∀ d,
    (Module.finrank K (𝒜 d) : ℤ) = coeff d (delPezzoHilbertSeries m c)

/-- Componentwise Hilbert-series certificate for the Artinian reduction of Proposition 2.2. -/
structure ArtinianReductionHilbertSeriesCertificate
    (𝒜 : ℕ → Submodule K A) (c : ℕ) : Prop where
  finrank_eq_coeff : ∀ d,
    (Module.finrank K (𝒜 d) : ℤ) = coeff d (delPezzoHilbertNumerator c)

/-- Equation (1) forces the degree-zero component to have dimension one. -/
theorem DelPezzoHilbertSeriesCertificate.finrank_zero
    {𝒜 : ℕ → Submodule K A} {m c : ℕ}
    (h : DelPezzoHilbertSeriesCertificate 𝒜 m c) :
    Module.finrank K (𝒜 0) = 1 := by
  have hd := h.finrank_eq_coeff 0
  rw [coeff_zero_delPezzoHilbertSeries] at hd
  exact_mod_cast hd

/-- Equation (1) forces `dim R₁ = m+c+1`. -/
theorem DelPezzoHilbertSeriesCertificate.finrank_one
    {𝒜 : ℕ → Submodule K A} {m c : ℕ}
    (h : DelPezzoHilbertSeriesCertificate 𝒜 m c) :
    Module.finrank K (𝒜 1) = hilbertDegreeOne m c := by
  have hd := h.finrank_eq_coeff 1
  rw [coeff_one_delPezzoHilbertSeries] at hd
  exact_mod_cast hd

/-- The positive degree-one coefficient also supplies finite-dimensionality of `R₁`; callers
need not assume `Module.Finite` separately. -/
theorem DelPezzoHilbertSeriesCertificate.moduleFinite_one
    {𝒜 : ℕ → Submodule K A} {m c : ℕ}
    (h : DelPezzoHilbertSeriesCertificate 𝒜 m c) :
    Module.Finite K (𝒜 1) :=
  Module.finite_of_finrank_pos <| by
    rw [h.finrank_one]
    simp [hilbertDegreeOne]

/-- Equation (1) forces the degree-two dimension formula in Proposition 2.1. -/
theorem DelPezzoHilbertSeriesCertificate.finrank_two
    {𝒜 : ℕ → Submodule K A} {m c : ℕ}
    (h : DelPezzoHilbertSeriesCertificate 𝒜 m c) :
    Module.finrank K (𝒜 2) = hilbertDegreeTwo m c := by
  have hd := h.finrank_eq_coeff 2
  rw [coeff_two_delPezzoHilbertSeries] at hd
  exact_mod_cast hd

/-- The Artinian reduction has Hilbert function value one in degree zero. -/
theorem ArtinianReductionHilbertSeriesCertificate.finrank_zero
    {𝒜 : ℕ → Submodule K A} {c : ℕ}
    (h : ArtinianReductionHilbertSeriesCertificate 𝒜 c) :
    Module.finrank K (𝒜 0) = 1 := by
  have hd := h.finrank_eq_coeff 0
  rw [coeff_zero_delPezzoHilbertNumerator] at hd
  exact_mod_cast hd

/-- The Artinian reduction has Hilbert function value `c` in degree one. -/
theorem ArtinianReductionHilbertSeriesCertificate.finrank_one
    {𝒜 : ℕ → Submodule K A} {c : ℕ}
    (h : ArtinianReductionHilbertSeriesCertificate 𝒜 c) :
    Module.finrank K (𝒜 1) = c := by
  have hd := h.finrank_eq_coeff 1
  rw [coeff_one_delPezzoHilbertNumerator] at hd
  exact_mod_cast hd

/-- The Artinian reduction has its one-dimensional socle in degree two. -/
theorem ArtinianReductionHilbertSeriesCertificate.finrank_two
    {𝒜 : ℕ → Submodule K A} {c : ℕ}
    (h : ArtinianReductionHilbertSeriesCertificate 𝒜 c) :
    Module.finrank K (𝒜 2) = 1 := by
  have hd := h.finrank_eq_coeff 2
  rw [coeff_two_delPezzoHilbertNumerator] at hd
  exact_mod_cast hd

/-- The positive degree-two coefficient supplies finite-dimensionality of the socle component. -/
theorem ArtinianReductionHilbertSeriesCertificate.moduleFinite_two
    {𝒜 : ℕ → Submodule K A} {c : ℕ}
    (h : ArtinianReductionHilbertSeriesCertificate 𝒜 c) :
    Module.Finite K (𝒜 2) :=
  Module.finite_of_finrank_pos <| by rw [h.finrank_two]; simp

end GradedComponents

/-- Twice the quadratic-dimension computation in Proposition 2.1. -/
theorem quadratic_deficiency_one_twice (m c : ℤ) :
    (m + c + 2) * (m + c + 1) -
        ((m + 2) * (m + 1) + 2 * c * (m + 1) + 2) =
      c * (c + 1) - 2 := by
  ring

/-- Evaluating the Hilbert numerator at one gives the asserted degree `c + 2`. -/
theorem hilbert_numerator_at_one (c : ℤ) : 1 + c + 1 = c + 2 := by
  ring

/-- The `a`-invariant arithmetic: numerator degree minus Krull dimension. -/
theorem gorenstein_a_invariant_arithmetic (m : ℤ) :
    2 - (m + 1) = 1 - m := by
  ring

end DelPezzoBlekherman
