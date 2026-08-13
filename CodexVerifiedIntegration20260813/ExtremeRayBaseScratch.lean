import Mathlib.Analysis.Convex.Extreme
import Mathlib.Geometry.Convex.Cone.Basic
import Mathlib.Data.Real.Basic
import ExtremeSeparatorScratch

noncomputable section

universe u

open Set

namespace ExtremeRayBase

variable {V : Type u} [AddCommGroup V] [Module ℝ V]

/-- A faithful additive definition of an extreme ray of a convex cone. -/
def IsExtremeRay (C : ConvexCone ℝ V) (y : V) : Prop :=
  y ∈ C ∧ y ≠ 0 ∧
    ∀ a ∈ C, ∀ b ∈ C, a + b = y →
      (∃ r : ℝ, 0 ≤ r ∧ a = r • y) ∧
      ∃ s : ℝ, 0 ≤ s ∧ b = s • y

/-- An extreme point of a strictly positive affine base of a cone generates an extreme ray. -/
theorem isExtremeRay_of_extremePoint_base
    (C : ConvexCone ℝ V) (tau : V →ₗ[ℝ] ℝ)
    (hpos : ∀ x ∈ C, x ≠ 0 → 0 < tau x)
    {y : V}
    (hy : y ∈ ({x : V | x ∈ C ∧ tau x = 1}).extremePoints ℝ) :
    IsExtremeRay C y := by
  have hyBraw : y ∈ ({x : V | x ∈ C ∧ tau x = 1} : Set V) :=
    extremePoints_subset hy
  have hyB : y ∈ C ∧ tau y = 1 := hyBraw
  have hy0 : y ≠ 0 := by
    intro hy0
    subst y
    simpa using hyB.2
  refine ⟨hyB.1, hy0, ?_⟩
  intro a ha b hb hab
  let ra : ℝ := tau a
  let rb : ℝ := tau b
  have hra : 0 ≤ ra := by
    by_cases ha0 : a = 0
    · simp [ra, ha0]
    · exact (hpos a ha ha0).le
  have hrb : 0 ≤ rb := by
    by_cases hb0 : b = 0
    · simp [rb, hb0]
    · exact (hpos b hb hb0).le
  have hrsum : ra + rb = 1 := by
    change tau a + tau b = 1
    rw [← map_add, hab, hyB.2]
  by_cases hra0 : ra = 0
  · have ha0 : a = 0 := by
      by_contra ha0
      exact (hpos a ha ha0).ne' hra0
    subst a
    have hb_y : b = y := by simpa using hab
    exact ⟨⟨0, le_rfl, by simp⟩, ⟨1, zero_le_one, by simpa using hb_y⟩⟩
  by_cases hrb0 : rb = 0
  · have hb0 : b = 0 := by
      by_contra hb0
      exact (hpos b hb hb0).ne' hrb0
    subst b
    have ha_y : a = y := by simpa using hab
    exact ⟨⟨1, zero_le_one, by simpa using ha_y⟩, ⟨0, le_rfl, by simp⟩⟩
  have hra' : 0 < ra := lt_of_le_of_ne hra (Ne.symm hra0)
  have hrb' : 0 < rb := lt_of_le_of_ne hrb (Ne.symm hrb0)
  let a' : V := ra⁻¹ • a
  let b' : V := rb⁻¹ • b
  have ha'B : a' ∈ {x : V | x ∈ C ∧ tau x = 1} := by
    constructor
    · exact C.smul_mem (inv_pos.mpr hra') ha
    · simp [a', ra, hra0]
  have hb'B : b' ∈ {x : V | x ∈ C ∧ tau x = 1} := by
    constructor
    · exact C.smul_mem (inv_pos.mpr hrb') hb
    · simp [b', rb, hrb0]
  have hyseg : y ∈ openSegment ℝ a' b' := by
    refine ⟨ra, rb, hra', hrb', hrsum, ?_⟩
    simp only [a', b', smul_smul]
    rw [mul_inv_cancel₀ hra0, mul_inv_cancel₀ hrb0, one_smul, one_smul, hab]
  have hab_eq := (mem_extremePoints.mp hy).2 a' ha'B b' hb'B hyseg
  have ha_scale : a = ra • y := by
    rw [← hab_eq.1]
    simp [a', smul_smul, hra0]
  have hb_scale : b = rb • y := by
    rw [← hab_eq.2]
    simp [b', smul_smul, hrb0]
  exact ⟨⟨ra, hra, ha_scale⟩, ⟨rb, hrb, hb_scale⟩⟩

section Topological

variable [TopologicalSpace V] [T2Space V] [IsTopologicalAddGroup V]
  [ContinuousSMul ℝ V] [LocallyConvexSpace ℝ V]

/-- A negative point in a compact strictly positive base can be replaced by a negative generator
of an extreme ray. -/
theorem exists_extremeRay_apply_neg_of_compact_base
    (C : ConvexCone ℝ V) (tau : V →ₗ[ℝ] ℝ)
    (hpos : ∀ x ∈ C, x ≠ 0 → 0 < tau x)
    (hcompact : IsCompact {x : V | x ∈ C ∧ tau x = 1})
    (f : StrongDual ℝ V) {x : V}
    (hx : x ∈ C) (htau : tau x = 1) (hfx : f x < 0) :
    ∃ y, IsExtremeRay C y ∧ tau y = 1 ∧ f y < 0 := by
  obtain ⟨y, hyext, hfy⟩ := ExtremeSeparator.exists_extremePoint_apply_neg
    hcompact f ⟨hx, htau⟩ hfx
  have hybaseRaw : y ∈ ({z : V | z ∈ C ∧ tau z = 1} : Set V) :=
    extremePoints_subset hyext
  have hybase : y ∈ C ∧ tau y = 1 := hybaseRaw
  exact ⟨y, isExtremeRay_of_extremePoint_base C tau hpos hyext, hybase.2, hfy⟩

end Topological

end ExtremeRayBase
