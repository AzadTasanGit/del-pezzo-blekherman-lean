/-
Copyright (c) 2026 Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Projectivization.Basic
import DelPezzoBlekherman.Fiber.RealDiagonal

/-!
# Finite evaluation algebra

This file isolates the finite-dimensional consequences used in Proposition 5.2:
an injective evaluation map with the expected dimension has hyperplane image or is
an isomorphism, and perfectness of the quotient multiplication pairing forces every
coefficient of the unique evaluation relation to be nonzero.
-/

namespace DelPezzoBlekherman

open scoped LinearAlgebra.Projectivization

/-- Every functional is a uniquely determined weighted coordinate sum after a
finite-dimensional evaluation isomorphism.  This is the coordinate-existence
part of Proposition 5.4. -/
theorem linearFunctional_coordinate_representation
    {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype ι]
    (e : V ≃ₗ[K] (ι → K)) (ell : V →ₗ[K] K) :
    ∃ a : ι → K, ∀ x, ell x = ∑ i, a i * e x i := by
  classical
  let a : ι → K := fun i => ell (e.symm (Pi.single i 1))
  refine ⟨a, ?_⟩
  intro x
  have hcoord : (∑ i, Pi.single i (e x i)) = e x := by
    ext j
    rw [Finset.sum_apply]
    exact Fintype.sum_pi_single j (e x)
  calc
    ell x = ell (e.symm (e x)) := by rw [e.symm_apply_apply]
    _ = ell (e.symm (∑ i, Pi.single i (e x i))) := by rw [hcoord]
    _ = ∑ i, a i * e x i := by
      simp only [map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hsingle : Pi.single i (e x i) = (e x i) • Pi.single i 1 := by
        ext j
        by_cases hji : j = i
        · subst j
          simp
        · simp [hji]
      rw [hsingle, map_smul, map_smul]
      simp [a, mul_comm]

theorem linearFunctional_coordinate_representation_unique
    {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype ι]
    (e : V ≃ₗ[K] (ι → K)) (ell : V →ₗ[K] K)
    {a b : ι → K}
    (ha : ∀ x, ell x = ∑ i, a i * e x i)
    (hb : ∀ x, ell x = ∑ i, b i * e x i) :
    a = b := by
  classical
  funext j
  have h := (ha (e.symm (Pi.single j 1))).symm.trans
    (hb (e.symm (Pi.single j 1)))
  simpa [Pi.single_apply] using h

/-- A linear functional whose kernel contains the kernel of a nonzero functional
is a scalar multiple of it.  Equivalently, the annihilator of a hyperplane is a
line. -/
theorem linearFunctional_eq_smul_of_ker_le
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (f g : V →ₗ[K] K) (hf : f ≠ 0)
    (hker : LinearMap.ker f ≤ LinearMap.ker g) :
    ∃ c : K, g = c • f := by
  have hex : ∃ w : V, f w ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hf
    ext w
    exact hn w
  obtain ⟨w, hw⟩ := hex
  let v : V := (f w)⁻¹ • w
  have hv : f v = 1 := by simp [v, hw]
  refine ⟨g v, ?_⟩
  ext x
  let k : V := x - f x • v
  have hfk : f k = 0 := by simp [k, hv]
  have hgk : g k = 0 := LinearMap.mem_ker.mp (hker (LinearMap.mem_ker.mpr hfk))
  have hx : x = f x • v + k := by simp [k]
  calc
    g x = g (f x • v + k) := congrArg g hx
    _ = g v * f x := by simp [hgk, mul_comm]
    _ = ((g v) • f) x := by simp

/-- A functional vanishes on a hyperplane exactly when it is proportional to
the functional defining that hyperplane.  Applied to point evaluation, this is
the linear-algebra identity saying that the common zero set of `ker f` is the
projective fiber over `[f]`. -/
theorem vanishes_on_ker_iff_eq_smul
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (f g : V →ₗ[K] K) (hf : f ≠ 0) :
    (∀ v, f v = 0 → g v = 0) ↔ ∃ c : K, g = c • f := by
  constructor
  · intro h
    apply linearFunctional_eq_smul_of_ker_le f g hf
    intro v hv
    exact LinearMap.mem_ker.mpr (h v (LinearMap.mem_ker.mp hv))
  · rintro ⟨c, rfl⟩ v hv
    simp [hv]

/-- If the hyperplane `ker f` is basepoint-free for an evaluation family,
then the projective point `[f]` is omitted by that family: no evaluation
functional is proportional to `f`. -/
theorem no_evaluation_eq_smul_of_ker_basepointFree
    {K V X : Type*} [Field K] [AddCommGroup V] [Module K V]
    (f : V →ₗ[K] K) (ev : X → V →ₗ[K] K)
    (hbasepointFree : ∀ x, ∃ v, f v = 0 ∧ ev x v ≠ 0) :
    ∀ x, ¬∃ c : K, ev x = c • f := by
  intro x
  rintro ⟨c, hc⟩
  obtain ⟨v, hfv, hev⟩ := hbasepointFree x
  apply hev
  rw [hc]
  simp [hfv]

/-- Projectivized form of `no_evaluation_eq_smul_of_ker_basepointFree`.
A basepoint-free hyperplane `ker f` supplies a well-defined projectivized
evaluation map whose range omits the point `[f]`. -/
theorem exists_projective_evaluation_omitting_hyperplane
    {K V X : Type*} [Field K] [AddCommGroup V] [Module K V]
    (f : V →ₗ[K] K) (hf : f ≠ 0) (ev : X → V →ₗ[K] K)
    (hbasepointFree : ∀ x, ∃ v, f v = 0 ∧ ev x v ≠ 0) :
    ∃ hev : ∀ x, ev x ≠ 0,
      Projectivization.mk K f hf ∉ Set.range
        (fun x ↦ Projectivization.mk K (ev x) (hev x)) := by
  have hev : ∀ x, ev x ≠ 0 := by
    intro x heq
    obtain ⟨v, _, hv⟩ := hbasepointFree x
    apply hv
    rw [heq]
    rfl
  refine ⟨hev, ?_⟩
  rintro ⟨x, hx⟩
  have hproportional : ∃ c : K, ev x = c • f := by
    obtain ⟨c, hc⟩ :=
      (Projectivization.mk_eq_mk_iff' K (ev x) f (hev x) hf).mp hx
    exact ⟨c, hc.symm⟩
  exact no_evaluation_eq_smul_of_ker_basepointFree f ev hbasepointFree x hproportional

/-- If two nonzero conjugation-compatible coordinate vectors differ by a complex
scalar, that scalar is real.  The map `tau` models the permutation exchanging every
conjugate pair (and fixing real coordinates). -/
theorem scalar_real_of_conjugation_fixed_vectors
    {iota : Type*} (tau : iota → iota) (u w : iota → ℂ) (kappa : ℂ)
    (hu : ∃ i, u i ≠ 0)
    (hufix : ∀ i, u (tau i) = star (u i))
    (hwfix : ∀ i, w (tau i) = star (w i))
    (hscale : w = kappa • u) : kappa.im = 0 := by
  obtain ⟨i, hui⟩ := hu
  have hui' : u (tau i) ≠ 0 := by rw [hufix]; simp [hui]
  have hi := congr_fun hscale i
  have ht := congr_fun hscale (tau i)
  have hstar := congrArg star hi
  simp only [Pi.smul_apply, smul_eq_mul] at hi ht
  change star (w i) = star (kappa * u i) at hstar
  rw [star_mul] at hstar
  rw [← hwfix i, ← hufix i] at hstar
  have hstar' : w (tau i) = star kappa * u (tau i) :=
    hstar.trans (mul_comm _ _)
  have hkstar : kappa = star kappa := by
    apply mul_right_cancel₀ hui'
    exact ht.symm.trans hstar'
  have hre := congrArg Complex.im hkstar
  simp at hre
  linarith

theorem injective_finrank_eq_sub_one_has_hyperplane_range
    {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (e : V →ₗ[K] W) (he : Function.Injective e)
    (hdim : Module.finrank K V + 1 = Module.finrank K W) :
    Module.finrank K (LinearMap.range e) + 1 = Module.finrank K W := by
  rw [LinearMap.finrank_range_of_inj he]
  exact hdim

/-- An injective evaluation map between spaces of equal finite dimension, bundled
as the resulting linear equivalence. -/
noncomputable def evaluationLinearEquivOfInjective
    {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (e : V →ₗ[K] W) (he : Function.Injective e)
    (hdim : Module.finrank K V = Module.finrank K W) : V ≃ₗ[K] W :=
  LinearEquiv.ofBijective e ⟨he, by
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    exact (LinearMap.finrank_range_of_inj he).trans hdim⟩

/-- Cayley--Bacharach coefficient nonvanishing in the linear-algebra form used in
Proposition 5.2(b).  The hypothesis says that the radical of the weighted pairing
on the relation hyperplane is precisely the constant line. -/
theorem relation_coefficients_ne_zero_of_radical_line
    {iota : Type*} [Fintype iota]
    (u : iota → ℂ)
    (hother : ∀ j : iota, ∃ k : iota, k ≠ j)
    (hrad : ∀ x : iota → ℂ,
      (∑ i, u i * x i = 0) →
      (∀ y : iota → ℂ, (∑ i, u i * y i = 0) →
        ∑ i, u i * x i * y i = 0) →
      x ∈ ℂ ∙ (1 : iota → ℂ)) :
    ∀ j, u j ≠ 0 := by
  classical
  intro j huj
  let e : iota → ℂ := Pi.single j 1
  have heH : ∑ i, u i * e i = 0 := by
    simp only [e, Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, huj]
    norm_num
  have heRad : ∀ y : iota → ℂ, (∑ i, u i * y i = 0) →
      ∑ i, u i * e i * y i = 0 := by
    intro y _
    simp only [e, Pi.single_apply]
    rw [Finset.sum_eq_single j]
    · simp [huj]
    · intro i _ hij
      simp [hij]
    · simp
  have hespan := hrad e heH heRad
  rw [Submodule.mem_span_singleton] at hespan
  obtain ⟨c, hc⟩ := hespan
  obtain ⟨k, hkj⟩ := hother j
  have hcj : c = 1 := by
    simpa only [Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one, e,
      Pi.single_apply, if_pos rfl, if_true] using congr_fun hc j
  have hck : c = 0 := by
    simpa only [Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one, e,
      Pi.single_apply, if_neg hkj, if_false] using congr_fun hc k
  rw [hcj] at hck
  norm_num at hck

end DelPezzoBlekherman
