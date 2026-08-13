import ProjectivePolynomialDenseScratch

noncomputable section

open Set

namespace MvPolynomial

variable {I W : Type*}
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- A projective target direction has good coordinates for `p` when it is represented, through
the coordinate equivalence, by a nonzero vector where `p` does not vanish. -/
def HasGoodCoordinates (e : (I → ℝ) ≃L[ℝ] W) (p : MvPolynomial I ℝ)
    (y : RealProjectiveTopology.Direction W) : Prop :=
  ∃ x : I → ℝ, eval x p ≠ 0 ∧ ∃ hx : e x ≠ 0,
    RealProjectiveTopology.directionOf W ⟨e x, hx⟩ = y

/-- Good-coordinate directions for a nonzero polynomial are Euclidean dense. -/
theorem dense_setOf_hasGoodCoordinates
    [Fintype I] (e : (I → ℝ) ≃L[ℝ] W) (p : MvPolynomial I ℝ) (hp : p ≠ 0) :
    Dense {y | HasGoodCoordinates e p y} := by
  apply Dense.mono ?_ (dense_directionOf_image_equiv_eval_ne_zero e p hp)
  rintro y ⟨w, ⟨x, hx, hxw⟩, rfl⟩
  have hex : e x ≠ 0 := by
    intro hzero
    apply w.2
    rw [← hxw]
    exact hzero
  refine ⟨x, hx, hex, ?_⟩
  apply congr_arg (RealProjectiveTopology.directionOf W)
  apply Subtype.ext
  exact hxw

/-- Choose good affine coordinates on the good locus, with zero as an irrelevant fallback outside
that locus. -/
def goodCoordinates (e : (I → ℝ) ≃L[ℝ] W) (p : MvPolynomial I ℝ)
    (y : RealProjectiveTopology.Direction W) : I → ℝ := by
  classical
  exact if h : HasGoodCoordinates e p y then Classical.choose h else 0

theorem eval_goodCoordinates_ne_zero
    (e : (I → ℝ) ≃L[ℝ] W) (p : MvPolynomial I ℝ)
    {y : RealProjectiveTopology.Direction W} (hy : HasGoodCoordinates e p y) :
    eval (goodCoordinates e p y) p ≠ 0 := by
  rw [goodCoordinates, dif_pos hy]
  exact (Classical.choose_spec hy).1

theorem goodCoordinates_ne_zero
    (e : (I → ℝ) ≃L[ℝ] W) (p : MvPolynomial I ℝ)
    {y : RealProjectiveTopology.Direction W} (hy : HasGoodCoordinates e p y) :
    e (goodCoordinates e p y) ≠ 0 := by
  rw [goodCoordinates, dif_pos hy]
  exact Classical.choose (Classical.choose_spec hy).2

theorem directionOf_goodCoordinates
    (e : (I → ℝ) ≃L[ℝ] W) (p : MvPolynomial I ℝ)
    {y : RealProjectiveTopology.Direction W} (hy : HasGoodCoordinates e p y) :
    RealProjectiveTopology.directionOf W
      ⟨e (goodCoordinates e p y), goodCoordinates_ne_zero e p hy⟩ = y := by
  simpa only [goodCoordinates, dif_pos hy] using
    Classical.choose_spec (Classical.choose_spec hy).2

end MvPolynomial
