import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.Cone.Dual

noncomputable section

universe u

open Set

namespace ExtremeSeparator

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]

/-- A continuous linear functional which is negative somewhere on a nonempty compact convex set
is already negative at an extreme point of that set.  This is the compact-base reduction used to
choose an extreme supporting ray. -/
theorem exists_extremePoint_apply_neg
    {B : Set E} (hBcompact : IsCompact B)
    (f : StrongDual ℝ E) {x : E} (hxB : x ∈ B) (hfx : f x < 0) :
    ∃ y, y ∈ B.extremePoints ℝ ∧ f y < 0 := by
  obtain ⟨z, hzB, hzmin⟩ :=
    hBcompact.exists_isMinOn ⟨x, hxB⟩ f.continuous.continuousOn
  let T : Set E := {y ∈ B | ∀ w ∈ B, (-f) w ≤ (-f) y}
  have hTexp : IsExposed ℝ B T := by
    intro h
    exact ⟨-f, rfl⟩
  have hzT : z ∈ T := by
    refine ⟨hzB, ?_⟩
    intro w hwB
    simpa using hzmin hwB
  obtain ⟨y, hyT⟩ := (hTexp.isCompact hBcompact).extremePoints_nonempty ⟨z, hzT⟩
  have hyBext : y ∈ B.extremePoints ℝ :=
    hTexp.isExtreme.extremePoints_subset_extremePoints hyT
  have hy_le : f y ≤ f x := by
    have := hyT.1.2 x hxB
    simpa using this
  exact ⟨y, hyBext, hy_le.trans_lt hfx⟩

/-- Farkas separation for a proper cone, recorded in the sign convention used for SOS cones. -/
theorem properCone_separates
    (C : ProperCone ℝ E) {x : E} (hx : x ∉ C) :
    ∃ f : StrongDual ℝ E, (∀ y ∈ C, 0 ≤ f y) ∧ f x < 0 :=
  C.hyperplane_separation_point hx

end ExtremeSeparator
