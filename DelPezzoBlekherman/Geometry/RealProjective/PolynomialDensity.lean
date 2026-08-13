import DelPezzoBlekherman.Analysis.AnalyticNonvanishing
import DelPezzoBlekherman.Geometry.RealProjective.Topology

noncomputable section

open Set

namespace MvPolynomial

variable {σ : Type*} [Fintype σ]

/-- Projective directions represented by the nonvanishing locus of a nonzero real polynomial are
Euclidean dense in the compact real projective target. -/
theorem dense_directionOf_image_eval_ne_zero (p : MvPolynomial σ ℝ) (hp : p ≠ 0) :
    Dense (RealProjectiveTopology.directionOf (σ → ℝ) ''
      {v : {v : σ → ℝ // v ≠ 0} | eval (v : σ → ℝ) p ≠ 0}) :=
  RealProjectiveTopology.dense_image_directionOf_of_dense (σ → ℝ)
    (dense_setOf_eval_ne_zero p hp)

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Polynomial nonvanishing density transported from coordinates to any continuously linearly
equivalent finite-dimensional real target. -/
theorem dense_directionOf_image_equiv_eval_ne_zero
    (e : (σ → ℝ) ≃L[ℝ] W) (p : MvPolynomial σ ℝ) (hp : p ≠ 0) :
    Dense (RealProjectiveTopology.directionOf W ''
      {w : {w : W // w ≠ 0} |
        (w : W) ∈ e '' {x : σ → ℝ | eval x p ≠ 0}}) :=
  RealProjectiveTopology.dense_image_directionOf_continuousLinearEquiv e
    (dense_setOf_eval_ne_zero p hp)

end MvPolynomial
