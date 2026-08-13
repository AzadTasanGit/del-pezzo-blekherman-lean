/-
Copyright (c) 2026 Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import DelPezzoBlekherman.Fiber.Perturbation
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Real.Basic

/-!
# Geometric obstruction interface for short SOS families

This module packages the exact output required from the finite kernel morphism
in the lower-bound proof of Theorem 8.3.
-/

namespace DelPezzoBlekherman

/-- A subspace has no common zero for the specified evaluation family. -/
def IsBasepointFreeForEvaluation
    {V X : Type*} [AddCommGroup V] [Module ℝ V]
    (ev : X → (V →ₗ[ℝ] ℝ)) (U : Submodule ℝ V) : Prop :=
  ∀ x, ∃ u, u ∈ U ∧ ev x u ≠ 0

/-- The finite-fiber perturbation data rule out every basepoint-free `m`-plane
inside `K`.  Surjectivity is forced by compactness, density, and the incompatible
fiber pair bounds, contradicting the target point omitted by such a plane. -/
theorem no_basepointFree_submodule_of_dense_fiber_pair_bounds
    {V X Y : Type*} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [T2Space Y]
    (ev : X → (V →ₗ[ℝ] ℝ)) (K : Submodule ℝ V) (m : ℕ)
    (phi : X → Y) (hphi : Continuous phi)
    (Omega : Set Y) (hOmega : Dense Omega) (pairCount : Y → ℕ)
    (hcard : ∀ y ∈ Omega, y ∉ Set.range phi → 3 ≤ 2 * pairCount y)
    (hatMostOne : ∀ y ∈ Omega, pairCount y ≤ 1)
    (pointOfPlane : Submodule ℝ V → Y)
    (homitted : ∀ U, U ≤ K → Module.finrank ℝ U = m →
      IsBasepointFreeForEvaluation ev U → pointOfPlane U ∉ Set.range phi) :
    ∀ U : Submodule ℝ V, U ≤ K → Module.finrank ℝ U = m →
      IsBasepointFreeForEvaluation ev U → False := by
  have hsurjective : Function.Surjective phi :=
    surjective_of_dense_fiber_pair_bounds
      phi hphi Omega hOmega pairCount hcard hatMostOne
  intro U hUK hUdim hbase
  exact homitted U hUK hUdim hbase (hsurjective (pointOfPlane U))

end DelPezzoBlekherman
