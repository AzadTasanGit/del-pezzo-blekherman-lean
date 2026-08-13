import SOSLengthContinuousDenseScratch

noncomputable section

universe u v w

namespace SOSKernelLength

variable {X : Type u} [TopologicalSpace X]
variable {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- In finite dimension, continuity of an evaluation-functional family can be checked on the
vectors of any finite basis. -/
theorem continuous_dual_evaluation_of_continuous_on_basis
    {I : Type w} [Fintype I] [DecidableEq I]
    (b : Module.Basis I ℝ V) (evalV : X → Module.Dual ℝ V)
    (hcoord : ∀ i, Continuous (fun x ↦ evalV x (b i))) :
    Continuous (fun x ↦ LinearMap.toContinuousLinearMap (evalV x)) := by
  let e : (I → ℝ) ≃L[ℝ] (V →L[ℝ] ℝ) :=
    ((b.constr ℝ).trans LinearMap.toContinuousLinearMap).toContinuousLinearEquiv
  have hpi : Continuous (fun x i ↦ evalV x (b i)) := continuous_pi hcoord
  have heval : (fun x ↦ LinearMap.toContinuousLinearMap (evalV x)) =
      fun x ↦ e (fun i ↦ evalV x (b i)) := by
    funext x
    change LinearMap.toContinuousLinearMap (evalV x) =
      LinearMap.toContinuousLinearMap ((b.constr ℝ) (fun i ↦ evalV x (b i)))
    apply congrArg (fun f : Module.Dual ℝ V ↦ LinearMap.toContinuousLinearMap f)
    apply b.ext
    intro i
    simp
  rw [heval]
  exact e.continuous.comp hpi

end SOSKernelLength
