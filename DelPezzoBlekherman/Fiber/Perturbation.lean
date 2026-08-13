/-
Copyright (c) 2026 Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import DelPezzoBlekherman.Fiber.ConjugatePairs
import Mathlib.Topology.Separation.Hausdorff

/-!
# Perturbing to a good fiber

The topological and finite-counting core of the perturbation in Theorem 8.3.
The geometric input is exposed explicitly as compactness of the real-fiber
image and density of the reduced-fiber locus.
-/

open Set

namespace DelPezzoBlekherman

/-- A dense set meets the complement of a compact set whenever that complement
contains a point.  In the paper, the compact set is the image of the real locus
and the dense set is the real reduced-fiber locus. -/
theorem exists_mem_dense_not_mem_compact
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {C Omega : Set Y} (hC : IsCompact C) (hOmega : Dense Omega)
    {y0 : Y} (hy0 : y0 ∉ C) :
    ∃ y, y ∈ Omega ∧ y ∉ C := by
  have hopen : IsOpen Cᶜ := hC.isClosed.isOpen_compl
  have hnonempty : Cᶜ.Nonempty := ⟨y0, hy0⟩
  obtain ⟨y, hyOmega, hyC⟩ := hOmega.exists_mem_open hopen hnonempty
  exact ⟨y, hyOmega, hyC⟩

/-- Abstract terminal perturbation contradiction from Theorem 8.3.  If every
good fiber outside the real image has at least three geometric points arranged
in conjugate pairs, while the inertia theorem allows at most one pair, then the
compact real image has no exterior point. -/
theorem compact_eq_univ_of_dense_fiber_pair_bounds
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (C Omega : Set Y) (hC : IsCompact C) (hOmega : Dense Omega)
    (pairCount : Y → ℕ)
    (hcard : ∀ y ∈ Omega, y ∉ C → 3 ≤ 2 * pairCount y)
    (hatMostOne : ∀ y ∈ Omega, pairCount y ≤ 1) :
    C = Set.univ := by
  apply Set.eq_univ_of_forall
  intro y
  by_contra hy
  obtain ⟨z, hzOmega, hzC⟩ :=
    exists_mem_dense_not_mem_compact hC hOmega hy
  have htwo : 2 ≤ pairCount z :=
    two_le_conjugatePairCount_of_three_le_total _ (hcard z hzOmega hzC)
  have hone := hatMostOne z hzOmega
  omega

/-- Continuous-image form of the terminal perturbation argument.  If the real
source is compact, density plus the incompatible fiber-pair bounds force the
map on real points to be surjective.  Thus any separately constructed omitted
point gives the contradiction used in Theorem 8.3. -/
theorem surjective_of_dense_fiber_pair_bounds
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [T2Space Y]
    (phi : X → Y) (hphi : Continuous phi) (Omega : Set Y) (hOmega : Dense Omega)
    (pairCount : Y → ℕ)
    (hcard : ∀ y ∈ Omega, y ∉ Set.range phi → 3 ≤ 2 * pairCount y)
    (hatMostOne : ∀ y ∈ Omega, pairCount y ≤ 1) :
    Function.Surjective phi := by
  have hrange : Set.range phi = Set.univ :=
    compact_eq_univ_of_dense_fiber_pair_bounds
      (Set.range phi) Omega (isCompact_range hphi) hOmega pairCount hcard hatMostOne
  intro y
  have hy : y ∈ Set.range phi := by rw [hrange]; exact Set.mem_univ y
  exact hy

end DelPezzoBlekherman
