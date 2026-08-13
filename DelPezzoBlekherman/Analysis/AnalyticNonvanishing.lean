import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Algebra.MvPolynomial.Funext

noncomputable section

open Set Filter Topology

namespace AnalyticNonzeroDense

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [PreconnectedSpace E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A globally analytic function on a preconnected normed space which is nonzero somewhere has
dense nonzero locus. -/
theorem dense_setOf_ne_zero_of_analytic
    {f : E → F} (hf : AnalyticOnNhd 𝕜 f univ) {z : E} (hz : f z ≠ 0) :
    Dense {x | f x ≠ 0} := by
  rw [dense_iff_closure_eq]
  apply eq_univ_of_forall
  intro x
  rw [mem_closure_iff]
  intro U hU hxU
  by_contra hnone
  have hzeroU : ∀ y ∈ U, f y = 0 := by
    intro y hy
    by_contra hyzero
    exact hnone ⟨y, hy, hyzero⟩
  have heventually : f =ᶠ[𝓝 x] 0 := by
    filter_upwards [hU.mem_nhds hxU] with y hy
    exact hzeroU y hy
  have hglobal : Set.EqOn f 0 univ :=
    hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (mem_univ x) heventually
  exact hz (hglobal (mem_univ z))

end AnalyticNonzeroDense

namespace MvPolynomial

variable {σ : Type*} [Fintype σ]

/-- The Euclidean nonvanishing locus of a nonzero real multivariate polynomial is dense. -/
theorem dense_setOf_eval_ne_zero (p : MvPolynomial σ ℝ) (hp : p ≠ 0) :
    Dense {x : σ → ℝ | eval x p ≠ 0} := by
  have hexists : ∃ z : σ → ℝ, eval z p ≠ 0 := by
    by_contra hnone
    have hnone' : ∀ z : σ → ℝ, eval z p = 0 :=
      fun z ↦ not_ne_iff.mp (not_exists.mp hnone z)
    apply hp
    apply MvPolynomial.funext
    intro x
    simpa using hnone' x
  obtain ⟨z, hz⟩ := hexists
  exact AnalyticNonzeroDense.dense_setOf_ne_zero_of_analytic
    (AnalyticOnNhd.eval_mvPolynomial p) hz

end MvPolynomial
