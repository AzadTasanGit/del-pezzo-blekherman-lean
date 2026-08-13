/-
Copyright (c) 2026 Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The perfect-pairing kernel argument

This file formalizes the finite-dimensional algebraic mechanism at the end of
Theorem 4.3. The subspace `U` represents the chosen homogeneous parameter space in
degree one, and `C` is any complement identifying the quotient `R₁ / U` with a
concrete vector space. Nondegeneracy of the induced Gorenstein pairing forces the
entire Hankel radical to be exactly `U` and computes its rank.
-/

open LinearMap (BilinForm)

namespace DelPezzoBlekherman

/-- A bilinear form whose radical contains `U` and whose restriction to a complement
is nondegenerate has radical exactly `U`.

This is the linear-algebra conclusion of the Artinian Gorenstein reduction in
Theorem 4.3, expressed without choosing a quotient representative. -/
theorem ker_eq_of_complement_restrict_nondegenerate
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : BilinForm ℝ V) (U C : Submodule ℝ V)
    (hU : U ≤ LinearMap.ker B) (hcompl : IsCompl U C)
    (hperfect : (B.restrict C).Nondegenerate) :
    LinearMap.ker B = U := by
  apply le_antisymm
  · intro x hx
    obtain ⟨u, c, hu, hc, huc⟩ :=
      Submodule.codisjoint_iff_exists_add_eq.mp hcompl.codisjoint x
    have hcker : c ∈ LinearMap.ker B := by
      have huker := hU hu
      rw [← huc] at hx
      simpa using sub_mem hx huker
    have hc0 : (⟨c, hc⟩ : C) = 0 := by
      apply hperfect.1
      intro y
      simp only [LinearMap.BilinForm.restrict_apply]
      have hz := LinearMap.congr_fun (LinearMap.mem_ker.mp hcker) y
      exact hz
    have : c = 0 := by simpa using congr_arg Subtype.val hc0
    rw [this, add_zero] at huc
    exact huc ▸ hu
  · exact hU

/-- The corresponding kernel-dimension statement. -/
theorem finrank_ker_eq_of_perfect_quotient
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (B : BilinForm ℝ V) (U C : Submodule ℝ V)
    (hU : U ≤ LinearMap.ker B) (hcompl : IsCompl U C)
    (hperfect : (B.restrict C).Nondegenerate) :
    Module.finrank ℝ (LinearMap.ker B) = Module.finrank ℝ U := by
  rw [ker_eq_of_complement_restrict_nondegenerate B U C hU hcompl hperfect]

/-- The rank of the Hankel form is the ambient dimension minus the parameter-space
dimension, once the quotient pairing is perfect. -/
theorem rank_from_perfect_quotient
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (B : BilinForm ℝ V) (U C : Submodule ℝ V)
    (hU : U ≤ LinearMap.ker B) (hcompl : IsCompl U C)
    (hperfect : (B.restrict C).Nondegenerate) :
    Module.finrank ℝ (LinearMap.range B) = Module.finrank ℝ V - Module.finrank ℝ U := by
  have hrank := B.finrank_range_add_finrank_ker
  rw [ker_eq_of_complement_restrict_nondegenerate B U C hU hcompl hperfect] at hrank
  omega

/-- Numerical form of Theorem 4.3: if the ambient degree-one space has
dimension `m+c+1` and the parameter space has dimension `m+1`, the perfect
quotient pairing forces radical dimension `m+1` and rank `c`. -/
theorem kernel_dimension_and_rank_from_perfect_quotient
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (B : BilinForm ℝ V) (U C : Submodule ℝ V)
    (hU : U ≤ LinearMap.ker B) (hcompl : IsCompl U C)
    (hperfect : (B.restrict C).Nondegenerate)
    (m c : ℕ)
    (hdimV : Module.finrank ℝ V = m + c + 1)
    (hdimU : Module.finrank ℝ U = m + 1) :
    Module.finrank ℝ (LinearMap.ker B) = m + 1 ∧
      Module.finrank ℝ (LinearMap.range B) = c := by
  constructor
  · rw [finrank_ker_eq_of_perfect_quotient B U C hU hcompl hperfect, hdimU]
  · rw [rank_from_perfect_quotient B U C hU hcompl hperfect, hdimV, hdimU]
    omega

end DelPezzoBlekherman
