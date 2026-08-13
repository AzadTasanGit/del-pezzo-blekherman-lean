/-
Copyright (c) 2026 Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Analysis.Normed.Affine.AddTorsorBases

/-!
# Dual of a finite sums-of-squares cone

This file proves the algebraic dual-cone identity in Proposition 3.1 without tying
it to a particular graded-ring representation.  A linear functional is nonnegative
on every finite sum of values of `sq` exactly when it is nonnegative on each single
value `sq q`.
-/

namespace DelPezzoBlekherman

/-- The set of finite sums of elements `sq q`. -/
def finiteSumCone {V W : Type*} [AddCommMonoid W] (sq : V → W) : Set W :=
  {w | ∃ qs : List V, w = (qs.map sq).sum}

theorem zero_mem_finiteSumCone {V W : Type*} [AddCommMonoid W] (sq : V → W) :
    0 ∈ finiteSumCone sq := by
  exact ⟨[], rfl⟩

theorem finiteSumCone_add {V W : Type*} [AddCommMonoid W] (sq : V → W)
    {x y : W} (hx : x ∈ finiteSumCone sq) (hy : y ∈ finiteSumCone sq) :
    x + y ∈ finiteSumCone sq := by
  obtain ⟨xs, rfl⟩ := hx
  obtain ⟨ys, rfl⟩ := hy
  refine ⟨xs ++ ys, ?_⟩
  simp

theorem finiteSumCone_finset_sum
    {ι V W : Type*} [AddCommMonoid W] (sq : V → W)
    (s : Finset ι) (q : ι → V) :
    (∑ i ∈ s, sq (q i)) ∈ finiteSumCone sq := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero_mem_finiteSumCone sq
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact finiteSumCone_add sq ⟨[q i], by simp⟩ ih

/-- If every nonnegative multiple of a generator is again a generator, then
the finite-sum set is closed under nonnegative scalar multiplication.  For a
genuine square map this follows by scaling by a square root. -/
theorem finiteSumCone_smul
    {V W : Type*} [AddCommMonoid W] [Module ℝ W]
    (sq : V → W)
    (hsq : ∀ (a : ℝ), 0 ≤ a → ∀ q, ∃ r, sq r = a • sq q)
    {a : ℝ} (ha : 0 ≤ a) {x : W} (hx : x ∈ finiteSumCone sq) :
    a • x ∈ finiteSumCone sq := by
  obtain ⟨qs, rfl⟩ := hx
  choose rs hrs using fun q : V => hsq a ha q
  refine ⟨qs.map rs, ?_⟩
  induction qs with
  | nil => simp
  | cons q qs ih => simp [hrs, ih, smul_add]

/-- Under the square-root scaling property, finite sums of squares form a
convex cone. -/
theorem finiteSumCone_convex
    {V W : Type*} [AddCommMonoid W] [Module ℝ W]
    (sq : V → W)
    (hsq : ∀ (a : ℝ), 0 ≤ a → ∀ q, ∃ r, sq r = a • sq q) :
    Convex ℝ (finiteSumCone sq) := by
  intro x hx y hy a b ha hb hab
  exact finiteSumCone_add sq
    (finiteSumCone_smul sq hsq ha hx) (finiteSumCone_smul sq hsq hb hy)

/-- If the square values linearly span the target, then their convex cone is
full-dimensional. -/
theorem finiteSumCone_interior_nonempty_of_span_eq_top
    {V W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W]
    (sq : V → W)
    (hsq : ∀ (a : ℝ), 0 ≤ a → ∀ q, ∃ r, sq r = a • sq q)
    (hspan : Submodule.span ℝ (Set.range sq) = ⊤) :
    (interior (finiteSumCone sq)).Nonempty := by
  rw [(finiteSumCone_convex sq hsq).interior_nonempty_iff_affineSpan_eq_top]
  have hsubset : insert 0 (Set.range sq) ⊆ finiteSumCone sq := by
    intro x hx
    rcases hx with rfl | ⟨q, rfl⟩
    · exact zero_mem_finiteSumCone sq
    · exact ⟨[q], by simp⟩
  have haff : affineSpan ℝ (insert 0 (Set.range sq)) = ⊤ := by
    apply SetLike.coe_injective
    rw [affineSpan_insert_zero, hspan]
    rfl
  exact top_unique (haff ▸ affineSpan_mono ℝ hsubset)

/-- The exact dual identity: testing a linear functional on all finite sums is
equivalent to testing it on one square at a time. -/
theorem nonnegative_on_finiteSumCone_iff
    {V W : Type*} [AddCommMonoid W] [Module ℝ W]
    (sq : V → W) (ell : W →ₗ[ℝ] ℝ) :
    (∀ w ∈ finiteSumCone sq, 0 ≤ ell w) ↔ ∀ q, 0 ≤ ell (sq q) := by
  constructor
  · intro h q
    exact h (sq q) ⟨[q], by simp⟩
  · intro h w hw
    obtain ⟨qs, rfl⟩ := hw
    simp only [map_list_sum, List.map_map]
    apply List.sum_nonneg
    intro r hr
    rw [List.mem_map] at hr
    obtain ⟨q, _, rfl⟩ := hr
    exact h q

/-- If a nonnegative functional supports a sum of squares, it vanishes on
every square in that representation.  This is the first Gram-nullspace step in
Theorem 8.3. -/
theorem support_vanishes_on_each_square
    {ι V W : Type*} [Fintype ι]
    [AddCommMonoid W] [Module ℝ W]
    (sq : V → W) (ell : W →ₗ[ℝ] ℝ)
    (hnonneg : ∀ q, 0 ≤ ell (sq q))
    (q : ι → V) {p : W}
    (hp : p = ∑ i, sq (q i)) (hellp : ell p = 0) :
    ∀ i, ell (sq (q i)) = 0 := by
  have hsum : (∑ i, ell (sq (q i))) = 0 := by
    rw [hp, map_sum] at hellp
    exact hellp
  have hall := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i hi => hnonneg (q i))).mp hsum
  exact fun i => hall i (Finset.mem_univ i)

end DelPezzoBlekherman
