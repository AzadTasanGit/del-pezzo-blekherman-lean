import DelPezzoBlekherman.LinearAlgebra.NonrealPairInertia

noncomputable section

universe u v

namespace QuadraticForm.NonrealPairNegativeDirections

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
variable {P : Type v} [Fintype P] [DecidableEq P]

/-- A coordinate builder for the negative-direction certificate.  It is enough to identify a
subspace with one real coordinate per conjugate pair and show that the restricted form is a
diagonal sum with strictly negative weights. -/
def ofWeightedCoordinates
    (Q : QuadraticForm ℝ V) (W : Submodule ℝ V)
    (e : (P → ℝ) ≃ₗ[ℝ] W) (w : P → ℝ)
    (hw : ∀ p, w p < 0)
    (hQ : ∀ x, Q (e x : V) = ∑ p, w p * (x p) ^ 2) :
    NonrealPairNegativeDirections Q P where
  space := W
  finrank_eq_card := by
    rw [← e.finrank_eq, Module.finrank_pi, ← Nat.card_eq_fintype_card]
  negDef := by
    rintro ⟨y, hyW⟩ hy
    let x : P → ℝ := e.symm ⟨y, hyW⟩
    have hx : x ≠ 0 := by
      intro hx0
      apply hy
      have : (⟨y, hyW⟩ : W) = 0 := by
        rw [← e.apply_symm_apply ⟨y, hyW⟩]
        simp [x, hx0]
      exact this
    have hex : ∃ p, x p ≠ 0 := by
      by_contra h
      apply hx
      funext p
      exact not_ne_iff.mp (not_exists.mp h p)
    simp only [QuadraticMap.restrict_apply, neg_apply]
    have hey : (e x : V) = y := by
      exact congrArg Subtype.val (e.apply_symm_apply ⟨y, hyW⟩)
    rw [← hey, hQ x]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_pos'
    · intro p hp
      simpa using mul_nonneg (le_of_lt (neg_pos.mpr (hw p))) (sq_nonneg (x p))
    · obtain ⟨p, hp⟩ := hex
      refine ⟨p, Finset.mem_univ p, ?_⟩
      simpa using mul_pos (neg_pos.mpr (hw p)) (sq_pos_of_ne_zero hp)

end QuadraticForm.NonrealPairNegativeDirections
