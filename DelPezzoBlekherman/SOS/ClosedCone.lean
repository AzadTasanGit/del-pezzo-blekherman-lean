/-
Copyright (c) 2026 Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import DelPezzoBlekherman.Convexity.GramCone
import DelPezzoBlekherman.SOS.DualCone
import DelPezzoBlekherman.Algebra.StandardGradedMultiplication
import Mathlib.LinearAlgebra.Basis.Bilinear

/-!
# Closed Gram-represented SOS cones

This module transfers the closedness theorem for finite sums of squares to the
convex-cone realization used by `SOSConeDual`.
-/

namespace SOSConeDual

noncomputable section

open scoped BigOperators MatrixOrder

local instance {m n : Type*} [Fintype m] [Fintype n] :
    NormedAddCommGroup (Matrix m n ℝ) := Matrix.normedAddCommGroup

local instance {m n : Type*} [Fintype m] [Fintype n] :
    NormedSpace ℝ (Matrix m n ℝ) := Matrix.normedSpace

/-- A Gram representation with no nonzero positive semidefinite kernel element
makes the corresponding SOS convex cone closed. -/
theorem sosCone_isClosed_of_gram
    {n W : Type*} [Fintype n]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (sq : (n → ℝ) → W) (T : Matrix n n ℝ →L[ℝ] W)
    (hgram : ∀ q, T (DelPezzoBlekherman.rankOneGram q) = sq q)
    (hker : ∀ A ∈ DelPezzoBlekherman.realGramCone n, T A = 0 → A = 0) :
    IsClosed (sosCone sq : Set W) := by
  rw [sosCone_eq_finiteSumCone sq]
  · exact DelPezzoBlekherman.finiteSumCone_isClosed_of_gram sq T hgram hker
  · intro a ha q
    refine ⟨Real.sqrt a • q, ?_⟩
    rw [← hgram, DelPezzoBlekherman.rankOneGram_smul, map_smul,
      Real.sq_sqrt ha, hgram]

/-- The SOS cone of a finite-dimensional multiplication space is closed when point
evaluations separate degree one and turn multiplication into ordinary multiplication of
values.  The coordinate basis and Gram map used in the proof are constructed internally;
neither a Gram representation nor a Gram-kernel hypothesis is part of this interface. -/
theorem sosCone_isClosed_of_separating_multiplicative_evaluations
    {X V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (mul : V →ₗ[ℝ] V →ₗ[ℝ] W)
    (evalV : X → V →ₗ[ℝ] ℝ) (evalW : X → W →ₗ[ℝ] ℝ)
    (heval : ∀ x u v, evalW x (mul u v) = evalV x u * evalV x v)
    (hseparate : ∀ u, (∀ x, evalV x u = 0) → u = 0) :
    IsClosed (sosCone (fun u => mul u u) : Set W) := by
  classical
  let n := Fin (Module.finrank ℝ V)
  let b : Module.Basis n ℝ V := Module.finBasis ℝ V
  let sq : (n → ℝ) → W := fun q => mul (b.equivFun.symm q) (b.equivFun.symm q)
  let Tlin : Matrix n n ℝ →ₗ[ℝ] W :=
    { toFun := fun A => ∑ i, ∑ j, A i j • mul (b i) (b j)
      map_add' := by
        intro A B
        change (∑ i, ∑ j, (A i j + B i j) • mul (b i) (b j)) = _
        simp only [add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro r A
        change (∑ i, ∑ j, (r * A i j) • mul (b i) (b j)) =
          r • ∑ i, ∑ j, A i j • mul (b i) (b j)
        simp only [Finset.smul_sum, smul_smul] }
  let T : Matrix n n ℝ →L[ℝ] W := LinearMap.toContinuousLinearMap Tlin
  let e : X → (n → ℝ) := fun x i => evalV x (b i)
  have hgram : ∀ q, T (DelPezzoBlekherman.rankOneGram q) = sq q := by
    intro q
    change (∑ i, ∑ j, (q i * q j) • mul (b i) (b j)) =
      mul (b.equivFun.symm q) (b.equivFun.symm q)
    rw [Module.Basis.equivFun_symm_apply]
    simp_rw [map_sum, map_smul]
    simp_rw [LinearMap.sum_apply]
    simp_rw [LinearMap.smul_apply, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  have he_span : Submodule.span ℝ (Set.range e) = ⊤ := by
    apply DelPezzoBlekherman.span_evaluations_eq_top_of_functionals_separate e
    intro f hf
    let u : V := b.equivFun.symm (fun i => f (Pi.basisFun ℝ n i))
    have hu : u = 0 := by
      apply hseparate u
      intro x
      have hfx := hf x
      change f (fun i => evalV x (b i)) = 0 at hfx
      rw [← (Pi.basisFun ℝ n).sum_repr (fun i => evalV x (b i)), map_sum] at hfx
      change evalV x (b.equivFun.symm (fun i => f (Pi.basisFun ℝ n i))) = 0
      rw [Module.Basis.equivFun_symm_apply, map_sum]
      simpa only [map_smul, Pi.basisFun_repr, smul_eq_mul, mul_comm] using hfx
    apply (Pi.basisFun ℝ n).ext
    intro i
    have hcoeff : (fun j => f (Pi.basisFun ℝ n j)) = 0 := by
      apply b.equivFun.symm.injective
      simpa [u] using hu
    exact congrFun hcoeff i
  have hvanish : ∀ A, T A = 0 →
      ∀ x, dotProduct (e x) (Matrix.mulVec A (e x)) = 0 := by
    intro A hA x
    have hzero := congrArg (evalW x) hA
    change evalW x (Tlin A) = evalW x 0 at hzero
    change evalW x (∑ i, ∑ j, A i j • mul (b i) (b j)) = evalW x 0 at hzero
    simp only [map_zero] at hzero
    simp only [map_sum, map_smul, heval, smul_eq_mul] at hzero
    calc
      dotProduct (e x) (Matrix.mulVec A (e x)) =
          ∑ i, ∑ j, A i j * (evalV x (b i) * evalV x (b j)) := by
        simp only [dotProduct, Matrix.mulVec, e, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = 0 := hzero
  have hclosed : IsClosed (DelPezzoBlekherman.finiteSumCone sq) :=
    DelPezzoBlekherman.finiteSumCone_isClosed_of_gram_of_spanning_evaluations
      sq T hgram e he_span hvanish
  have hcones : DelPezzoBlekherman.finiteSumCone (fun u => mul u u) =
      DelPezzoBlekherman.finiteSumCone sq := by
    have hsquare_to : ∀ u, sq (b.equivFun u) = mul u u := by
      intro u
      simp only [sq, b.equivFun.symm_apply_apply]
    have hsquare_from : ∀ q, mul (b.equivFun.symm q) (b.equivFun.symm q) = sq q := by
      intro q
      rfl
    ext w
    constructor
    · rintro ⟨qs, rfl⟩
      refine ⟨qs.map b.equivFun, ?_⟩
      induction qs with
      | nil => rfl
      | cons u qs ih =>
          simp only [List.map_cons, List.sum_cons]
          rw [hsquare_to, ih]
    · rintro ⟨qs, rfl⟩
      refine ⟨qs.map b.equivFun.symm, ?_⟩
      induction qs with
      | nil => rfl
      | cons q qs ih =>
          simp only [List.map_cons, List.sum_cons]
          rw [hsquare_from, ih]
  rw [sosCone_eq_finiteSumCone (fun u => mul u u)]
  · rw [hcones]
    exact hclosed
  · intro a ha u
    refine ⟨Real.sqrt a • u, ?_⟩
    simp only [map_smul, LinearMap.smul_apply, smul_smul]
    rw [Real.mul_self_sqrt ha]

/-- Coordinate-ring specialization of
`sosCone_isClosed_of_separating_multiplicative_evaluations`.  Zariski density is used only
through its concrete degree-one consequence that real point evaluations separate sections. -/
theorem gradedSOSCone_isClosed_of_separating_evaluations
    {X A : Type*} [NormedCommRing A] [NormedAlgebra ℝ A]
    (𝒜 : ℕ → Submodule ℝ A) [SetLike.GradedMonoid 𝒜]
    [FiniteDimensional ℝ (𝒜 1)]
    (eval : X → A →ₐ[ℝ] ℝ)
    (hseparate : ∀ u : 𝒜 1, (∀ x, eval x u = 0) → u = 0) :
    IsClosed (sosCone (fun u =>
      ArtinianGorensteinDegreeOneCertificate.gradedDegreeOneMultiplication 𝒜 u u) :
      Set (𝒜 2)) := by
  apply sosCone_isClosed_of_separating_multiplicative_evaluations
    (ArtinianGorensteinDegreeOneCertificate.gradedDegreeOneMultiplication 𝒜)
    (fun x => (eval x).toLinearMap.comp (𝒜 1).subtype)
    (fun x => (eval x).toLinearMap.comp (𝒜 2).subtype)
  · intro x u v
    change eval x ((u : A) * (v : A)) = eval x (u : A) * eval x (v : A)
    exact map_mul (eval x) (u : A) (v : A)
  · intro u hu
    exact hseparate u hu

end

end SOSConeDual
