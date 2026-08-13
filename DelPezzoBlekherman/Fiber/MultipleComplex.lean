/-
Copyright (c) 2026 Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import DelPezzoBlekherman.Fiber.Lorentzian

/-!
# Multiple complex evaluation blocks

This file proves the finite-dimensional inertia assertion behind Proposition 6.2:
a hyperplane restriction of an orthogonal sum of nonzero complex square blocks can
be positive semidefinite only when there is at most one block.
-/

open LinearMap (BilinForm)

namespace DelPezzoBlekherman

/-- The orthogonal sum of complex square blocks indexed by `kappa`. -/
noncomputable def complexDiagonalBilin {kappa : Type*} [Fintype kappa]
    (b : kappa → ℂ) : BilinForm ℝ (kappa → ℂ) :=
  LinearMap.mk₂ ℝ (fun W Z ↦ ∑ k, complexSquareBilin (b k) (W k) (Z k))
    (by intro W₁ W₂ Z; simp only [Pi.add_apply, map_add, LinearMap.add_apply,
      Finset.sum_add_distrib])
    (by intro c W Z; simp only [Pi.smul_apply, map_smul, LinearMap.smul_apply,
      Finset.smul_sum])
    (by intro W Z₁ Z₂; simp only [Pi.add_apply, map_add, Finset.sum_add_distrib])
    (by intro c W Z; simp only [Pi.smul_apply, map_smul, Finset.smul_sum])

@[simp] theorem complexDiagonalBilin_apply {kappa : Type*} [Fintype kappa]
    (b : kappa → ℂ) (W Z : kappa → ℂ) :
    complexDiagonalBilin b W Z = ∑ k, complexSquareBilin (b k) (W k) (Z k) := rfl

theorem complexDiagonalBilin_isSymm {kappa : Type*} [Fintype kappa]
    (b : kappa → ℂ) : (complexDiagonalBilin b).IsSymm := by
  rw [LinearMap.BilinForm.isSymm_def]
  intro W Z
  simp only [complexDiagonalBilin_apply]
  apply Finset.sum_congr rfl
  intro k _
  exact (complexSquareBilin_isSymm (b k)).eq _ _

/-- At most one nonzero complex square block can remain PSD after restriction to
the kernel of any real linear functional.  This is the linear-algebraic content of
Proposition 6.2 once the fiber evaluation representation is supplied. -/
theorem complexDiagonal_at_most_one_pair
    {kappa : Type*} [Fintype kappa]
    (b : kappa → ℂ) (hb : ∀ k, b k ≠ 0)
    (L : (kappa → ℂ) →ₗ[ℝ] ℝ)
    (hpsd : ((complexDiagonalBilin b).restrict (LinearMap.ker L)).IsPosSemidef) :
    Subsingleton kappa := by
  classical
  rw [subsingleton_iff]
  intro j k
  by_contra hjk
  obtain ⟨wj, hwj⟩ := complexSquareBilin_exists_negative (b j) (hb j)
  obtain ⟨wk, hwk⟩ := complexSquareBilin_exists_negative (b k) (hb k)
  let X : kappa → ℂ := Pi.single j wj
  let Y : kappa → ℂ := Pi.single k wk
  have hXneg : complexDiagonalBilin b X X < 0 := by
    simp only [complexDiagonalBilin_apply, X, Pi.single_apply]
    rw [Finset.sum_eq_single j]
    · simpa
    · intro i _ hij
      simp [hij]
    · simp
  have hYneg : complexDiagonalBilin b Y Y < 0 := by
    simp only [complexDiagonalBilin_apply, Y, Pi.single_apply]
    rw [Finset.sum_eq_single k]
    · simpa
    · intro i _ hik
      simp [hik]
    · simp
  by_cases hLX : L X = 0
  · have h := hpsd.isNonneg.nonneg ⟨X, LinearMap.mem_ker.mpr hLX⟩
    exact (not_lt_of_ge h) hXneg
  · let Z : kappa → ℂ := (L Y) • X - (L X) • Y
    have hLZ : Z ∈ LinearMap.ker L := by
      rw [LinearMap.mem_ker]
      simp [Z]
      ring
    have hXY : complexDiagonalBilin b X Y = 0 := by
      simp only [complexDiagonalBilin_apply, X, Y, Pi.single_apply]
      apply Finset.sum_eq_zero
      intro i _
      by_cases hij : i = j
      · subst i
        simp [hjk]
      · simp [hij]
    have hYX : complexDiagonalBilin b Y X = 0 := by
      rw [(complexDiagonalBilin_isSymm b).eq]
      exact hXY
    have hZeval : complexDiagonalBilin b Z Z =
        (L Y) ^ 2 * complexDiagonalBilin b X X +
          (L X) ^ 2 * complexDiagonalBilin b Y Y := by
      simp only [Z, map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
      rw [hXY, hYX]
      ring
    have hsecond : (L X) ^ 2 * complexDiagonalBilin b Y Y < 0 :=
      mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hLX) hYneg
    have hfirst : (L Y) ^ 2 * complexDiagonalBilin b X X ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (le_of_lt hXneg)
    have hZneg : complexDiagonalBilin b Z Z < 0 := by rw [hZeval]; linarith
    have h := hpsd.isNonneg.nonneg ⟨Z, hLZ⟩
    exact (not_lt_of_ge h) hZneg

end DelPezzoBlekherman
