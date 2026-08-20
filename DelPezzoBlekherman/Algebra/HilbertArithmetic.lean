/-
Copyright (c) 2026 Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import Mathlib.Data.Int.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
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

/-- Formal power series attached to an abstract natural-valued Hilbert function. -/
noncomputable def hilbertFunctionSeries (h : ℕ → ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun d ↦ (h d : ℤ)

@[simp]
theorem coeff_hilbertFunctionSeries (h : ℕ → ℕ) (d : ℕ) :
    coeff d (hilbertFunctionSeries h) = h d :=
  by simp [hilbertFunctionSeries]

/-- The component-dimension recurrence arising from the short exact sequence for quotienting
by one degree-one nonzerodivisor: the quotient agrees in degree zero and, in degree `d+1`, its
dimension plus the preceding ambient dimension equals the ambient dimension in degree `d+1`. -/
structure DegreeOneReductionFinrankRelation (h reduced : ℕ → ℕ) : Prop where
  zero : reduced 0 = h 0
  succ : ∀ d, reduced (d + 1) + h d = h (d + 1)

/-- Componentwise data of the short exact sequence obtained by quotienting a graded module
by one degree-one nonzerodivisor.  The quotient in positive degree is presented as the cokernel
of multiplication by that element; keeping the cokernel equivalence explicit makes this usable
with any concrete model of homogeneous components. -/
structure DegreeOneReductionComponentExactSequence
    (K : Type u) {A : Type v} {B : Type w}
    [Field K] [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
    (𝒜 : ℕ → Submodule K A) (ℬ : ℕ → Submodule K B) where
  finite : ∀ d, Module.Finite K (𝒜 d)
  reducedFinite : ∀ d, Module.Finite K (ℬ d)
  zeroEquiv : 𝒜 0 ≃ₗ[K] ℬ 0
  multiplication : ∀ d, 𝒜 d →ₗ[K] 𝒜 (d + 1)
  multiplication_injective : ∀ d, Function.Injective (multiplication d)
  cokernelEquiv : ∀ d,
    (𝒜 (d + 1) ⧸ LinearMap.range (multiplication d)) ≃ₗ[K] ℬ (d + 1)

/-- The finite-dimensional degreewise short exact sequence for a degree-one nonzerodivisor
implies the numerical recurrence used by the Hilbert-series argument. -/
theorem DegreeOneReductionComponentExactSequence.toFinrankRelation
    {K : Type u} {A : Type v} {B : Type w}
    [Field K] [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
    {𝒜 : ℕ → Submodule K A} {ℬ : ℕ → Submodule K B}
    (h : DegreeOneReductionComponentExactSequence K 𝒜 ℬ) :
    DegreeOneReductionFinrankRelation
      (fun d ↦ Module.finrank K (𝒜 d))
      (fun d ↦ Module.finrank K (ℬ d)) := by
  classical
  refine ⟨?_, fun d ↦ ?_⟩
  · exact h.zeroEquiv.finrank_eq.symm
  · letI : Module.Finite K (𝒜 d) := h.finite d
    letI : Module.Finite K (𝒜 (d + 1)) := h.finite (d + 1)
    letI : Module.Finite K (ℬ (d + 1)) := h.reducedFinite (d + 1)
    calc
      Module.finrank K (ℬ (d + 1)) + Module.finrank K (𝒜 d) =
          Module.finrank K (𝒜 (d + 1) ⧸ LinearMap.range (h.multiplication d)) +
            Module.finrank K (LinearMap.range (h.multiplication d)) := by
        rw [h.cokernelEquiv d |>.finrank_eq,
          LinearMap.finrank_range_of_inj (h.multiplication_injective d)]
      _ = Module.finrank K (𝒜 (d + 1)) :=
        Submodule.finrank_quotient_add_finrank (LinearMap.range (h.multiplication d))

/-- One degree-one reduction multiplies the Hilbert series by `1-X`. -/
theorem DegreeOneReductionFinrankRelation.hilbertFunctionSeries_eq_mul_one_sub_X
    {h reduced : ℕ → ℕ} (hr : DegreeOneReductionFinrankRelation h reduced) :
    hilbertFunctionSeries reduced = hilbertFunctionSeries h * (1 - X) := by
  ext d
  cases d with
  | zero =>
      rw [mul_sub, mul_one, map_sub, coeff_hilbertFunctionSeries, coeff_zero_mul_X]
      simp only [coeff_hilbertFunctionSeries, sub_zero]
      exact_mod_cast hr.zero
  | succ d =>
      rw [mul_sub, mul_one, map_sub]
      simp only [coeff_hilbertFunctionSeries]
      rw [show (X : PowerSeries ℤ) = X ^ 1 by simp, coeff_mul_X_pow]
      rw [coeff_hilbertFunctionSeries]
      have hd := hr.succ d
      omega

/-- A chain of the component-dimension recurrences produced by successively quotienting by
degree-one nonzerodivisors. -/
structure SuccessiveLinearReductionFinrankRelations
    (h : ℕ → ℕ → ℕ) (n : ℕ) : Prop where
  step : ∀ i, i < n → DegreeOneReductionFinrankRelation (h i) (h (i + 1))

/-- Degreewise short exact sequences for all stages of a sequence of degree-one reductions.
The carriers are allowed to vary from stage to stage, as they do for successive quotient
modules. -/
structure SuccessiveDegreeOneReductionComponentExactSequences
    (K : Type u) (n : ℕ) (C : Fin (n + 1) → Type v)
    [Field K] [∀ i, AddCommGroup (C i)] [∀ i, Module K (C i)]
    (𝒞 : ∀ i, ℕ → Submodule K (C i)) where
  exactSequence : ∀ i (hi : i < n),
    DegreeOneReductionComponentExactSequence K
      (𝒞 ⟨i, by omega⟩) (𝒞 ⟨i + 1, by omega⟩)

/-- A family of finite-dimensional degreewise short exact sequences gives the numerical
recurrence package for all successive linear reductions. -/
theorem SuccessiveDegreeOneReductionComponentExactSequences.toFinrankRelations
    {K : Type u} {n : ℕ} {C : Fin (n + 1) → Type v}
    [Field K] [∀ i, AddCommGroup (C i)] [∀ i, Module K (C i)]
    {𝒞 : ∀ i, ℕ → Submodule K (C i)}
    (h : SuccessiveDegreeOneReductionComponentExactSequences K n C 𝒞) :
    SuccessiveLinearReductionFinrankRelations
      (fun i d ↦ Module.finrank K (𝒞 ⟨min i n, by omega⟩ d)) n := by
  refine ⟨fun i hi ↦ ?_⟩
  have hi_le : i ≤ n := Nat.le_of_lt hi
  have hsucc_le : i + 1 ≤ n := by omega
  convert (h.exactSequence i hi).toFinrankRelation using 1
  · funext d
    have hindex : (⟨min i n, by omega⟩ : Fin (n + 1)) = ⟨i, by omega⟩ :=
      Fin.ext (Nat.min_eq_left hi_le)
    rw [hindex]
  · funext d
    have hindex : (⟨min (i + 1) n, by omega⟩ : Fin (n + 1)) = ⟨i + 1, by omega⟩ :=
      Fin.ext (Nat.min_eq_left hsucc_le)
    rw [hindex]

/-- Iterating `n` degree-one reductions multiplies the initial Hilbert series by `(1-X)^n`. -/
theorem SuccessiveLinearReductionFinrankRelations.hilbertFunctionSeries_eq_mul_pow
    {h : ℕ → ℕ → ℕ} {n : ℕ}
    (hr : SuccessiveLinearReductionFinrankRelations h n) :
    hilbertFunctionSeries (h n) = hilbertFunctionSeries (h 0) * (1 - X) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [(hr.step n (by omega)).hilbertFunctionSeries_eq_mul_one_sub_X]
      have hprefix : SuccessiveLinearReductionFinrankRelations h n :=
        ⟨fun i hi ↦ hr.step i (by omega)⟩
      rw [ih hprefix, pow_succ, mul_assoc]

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

universe u v w

variable {K : Type u} {A : Type v} {B : Type w}
variable [Field K] [AddCommGroup A] [Module K A]
variable [AddCommGroup B] [Module K B]

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

/-- The exact Hilbert-series relation supplied by quotienting by an `(m+1)`-term linear
regular sequence in Proposition 2.2.  This structure deliberately records only the numerical
consequence: constructing it from an actual regular sequence is the remaining commutative-
algebra bridge. -/
structure ArtinianReductionDenominatorRelation
    (𝒜 : ℕ → Submodule K A) (m c : ℕ) : Prop where
  finrank_eq_coeff : ∀ d,
    (Module.finrank K (𝒜 d) : ℤ) =
      coeff d (delPezzoHilbertSeries m c * (1 - X) ^ (m + 1))

/-- Component-dimension data for the successive quotients by the chosen linear parameters.
The intermediate carriers need not be identified: only their Hilbert functions and the exact
one-step recurrences are retained. -/
structure SuccessiveLinearReductionComponentsRelation
    (𝒜 : ℕ → Submodule K A) (ℬ : ℕ → Submodule K B) (n : ℕ) where
  hilbertFunctions : ℕ → ℕ → ℕ
  initial : ∀ d, hilbertFunctions 0 d = Module.finrank K (𝒜 d)
  final : ∀ d, hilbertFunctions n d = Module.finrank K (ℬ d)
  reductions : SuccessiveLinearReductionFinrankRelations hilbertFunctions n

/-- The exact-sequence data for a succession of quotient modules supplies the component
relation consumed by the regular-reduction Hilbert-series argument. -/
noncomputable def SuccessiveDegreeOneReductionComponentExactSequences.toComponentsRelation
    {K : Type u} {n : ℕ} {C : Fin (n + 1) → Type v}
    [Field K] [∀ i, AddCommGroup (C i)] [∀ i, Module K (C i)]
    {𝒞 : ∀ i, ℕ → Submodule K (C i)}
    (h : SuccessiveDegreeOneReductionComponentExactSequences K n C 𝒞) :
    SuccessiveLinearReductionComponentsRelation
      (𝒞 0) (𝒞 ⟨n, by omega⟩) n where
  hilbertFunctions i d := Module.finrank K (𝒞 ⟨min i n, by omega⟩ d)
  initial d := by rfl
  final d := by
    have hindex : (⟨min n n, by omega⟩ : Fin (n + 1)) = ⟨n, by omega⟩ :=
      Fin.ext (by simp)
    rw [hindex]
  reductions := h.toFinrankRelations

/-- Successive one-step finrank recurrences, starting from equation (1), construct the exact
denominator relation for the final reduction. -/
theorem SuccessiveLinearReductionComponentsRelation.toArtinianReductionDenominatorRelation
    {𝒜 : ℕ → Submodule K A} {ℬ : ℕ → Submodule K B} {m c : ℕ}
    (h : SuccessiveLinearReductionComponentsRelation 𝒜 ℬ (m + 1))
    (hHilbert : DelPezzoHilbertSeriesCertificate 𝒜 m c) :
    ArtinianReductionDenominatorRelation ℬ m c := by
  have hinitial : hilbertFunctionSeries (h.hilbertFunctions 0) =
      delPezzoHilbertSeries m c := by
    ext d
    rw [coeff_hilbertFunctionSeries, ← hHilbert.finrank_eq_coeff d]
    exact_mod_cast h.initial d
  have hseries := h.reductions.hilbertFunctionSeries_eq_mul_pow
  refine ⟨fun d ↦ ?_⟩
  calc
    (Module.finrank K (ℬ d) : ℤ) =
        coeff d (hilbertFunctionSeries (h.hilbertFunctions (m + 1))) := by
          rw [coeff_hilbertFunctionSeries]
          exact_mod_cast (h.final d).symm
    _ = coeff d (hilbertFunctionSeries (h.hilbertFunctions 0) * (1 - X) ^ (m + 1)) :=
      congrArg (coeff d) hseries
    _ = coeff d (delPezzoHilbertSeries m c * (1 - X) ^ (m + 1)) := by
      rw [hinitial]

/-- The regular-sequence denominator relation and the checked cancellation identity construct
the Artinian reduction's `(1,c,1)` Hilbert-series certificate. -/
theorem ArtinianReductionDenominatorRelation.toHilbertSeriesCertificate
    {𝒜 : ℕ → Submodule K A} {m c : ℕ}
    (h : ArtinianReductionDenominatorRelation 𝒜 m c) :
    ArtinianReductionHilbertSeriesCertificate 𝒜 c where
  finrank_eq_coeff d := by
    rw [← delPezzoHilbertSeries_mul_one_sub_pow m c]
    exact h.finrank_eq_coeff d

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
