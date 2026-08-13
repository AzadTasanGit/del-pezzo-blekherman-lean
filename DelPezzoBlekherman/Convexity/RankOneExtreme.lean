import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Data.Real.Basic

noncomputable section

universe u

namespace PSDRangeOneExtreme

variable {V : Type u} [AddCommGroup V] [Module ℝ V]

/-- The symmetric rank-one form `f ⊗ f`. -/
def rankOne (f : Module.Dual ℝ V) : LinearMap.BilinForm ℝ V :=
  LinearMap.mk₂ ℝ (fun x y ↦ f x * f y)
    (by simp [add_mul]) (by simp [mul_assoc])
    (by simp [mul_add]) (by simp [mul_left_comm])

@[simp]
theorem rankOne_apply (f : Module.Dual ℝ V) (x y : V) :
    rankOne f x y = f x * f y := rfl

theorem rankOne_isPosSemidef (f : Module.Dual ℝ V) : (rankOne f).IsPosSemidef where
  isSymm := ⟨by intro x y; simp [rankOne, mul_comm]⟩
  isNonneg := ⟨fun x ↦ mul_self_nonneg (f x)⟩

theorem exists_apply_eq_one (f : Module.Dual ℝ V) (hf : f ≠ 0) :
    ∃ e : V, f e = 1 := by
  have hex : ∃ x, f x ≠ 0 := by
    by_contra h
    apply hf
    ext x
    exact not_ne_iff.mp (not_exists.mp h x)
  obtain ⟨x, hx⟩ := hex
  refine ⟨(f x)⁻¹ • x, ?_⟩
  simp [hx]

theorem ker_rankOne (f : Module.Dual ℝ V) (hf : f ≠ 0) :
    LinearMap.ker (rankOne f) = LinearMap.ker f := by
  obtain ⟨e, he⟩ := exists_apply_eq_one f hf
  ext x
  constructor
  · intro hx
    have hxe := LinearMap.congr_fun (LinearMap.mem_ker.mp hx) e
    simpa [he] using hxe
  · intro hx
    apply LinearMap.mem_ker.mpr
    ext y
    simp [LinearMap.mem_ker.mp hx]

/-- Kernel-face criterion for PSD forms: the kernel of a sum is the intersection of kernels. -/
theorem ker_add_eq_inf
    (B C : LinearMap.BilinForm ℝ V) (hB : B.IsPosSemidef) (hC : C.IsPosSemidef) :
    LinearMap.ker (B + C) = LinearMap.ker B ⊓ LinearMap.ker C := by
  ext x
  constructor
  · intro hx
    have hsum : B x x + C x x = 0 := by
      have hx0 := LinearMap.mem_ker.mp hx
      have hxx := LinearMap.congr_fun hx0 x
      simpa using hxx
    have hBx : B x x = 0 := by
      linarith [hB.isNonneg.nonneg x, hC.isNonneg.nonneg x]
    have hCx : C x x = 0 := by
      linarith [hB.isNonneg.nonneg x, hC.isNonneg.nonneg x]
    exact ⟨(B.apply_apply_same_eq_zero_iff hB.isNonneg.nonneg hB.isSymm).mp hBx,
      (C.apply_apply_same_eq_zero_iff hC.isNonneg.nonneg hC.isSymm).mp hCx⟩
  · rintro ⟨hxB, hxC⟩
    apply LinearMap.mem_ker.mpr
    simp [LinearMap.mem_ker.mp hxB, LinearMap.mem_ker.mp hxC]

/-- A symmetric bilinear form whose left kernel contains `ker f` is a scalar multiple of
`f ⊗ f`. -/
theorem eq_smul_rankOne_of_ker_le
    (f : Module.Dual ℝ V) (hf : f ≠ 0)
    (B : LinearMap.BilinForm ℝ V) (hBsymm : B.IsSymm)
    (hker : LinearMap.ker f ≤ LinearMap.ker B) :
    ∃ t : ℝ, B = t • rankOne f := by
  obtain ⟨e, he⟩ := exists_apply_eq_one f hf
  let t : ℝ := B e e
  have hleft (x : V) : B x = f x • B e := by
    have hxker : x - f x • e ∈ LinearMap.ker f := by
      apply LinearMap.mem_ker.mpr
      simp [he]
    have hxB := LinearMap.mem_ker.mp (hker hxker)
    have := congrArg (fun g : Module.Dual ℝ V ↦ g + f x • B e) hxB
    simpa using this
  have heval (y : V) : B e y = t * f y := by
    have hyker : y - f y • e ∈ LinearMap.ker f := by
      apply LinearMap.mem_ker.mpr
      simp [he]
    have hyB := LinearMap.mem_ker.mp (hker hyker)
    have hzero : B (y - f y • e) e = 0 := by
      simpa using LinearMap.congr_fun hyB e
    have hsymm : B e (y - f y • e) = 0 := by
      have heq : B e (y - f y • e) = B (y - f y • e) e := by
        simpa using hBsymm.eq e (y - f y • e)
      rw [heq]
      exact hzero
    have hsymm' : B e y - f y * B e e = 0 := by simpa using hsymm
    simpa [t, mul_comm] using sub_eq_zero.mp hsymm'
  refine ⟨t, ?_⟩
  ext x y
  have hxy := LinearMap.congr_fun (hleft x) y
  calc
    B x y = f x * B e y := by simpa using hxy
    _ = f x * (t * f y) := by rw [heval]
    _ = (t • rankOne f) x y := by simp [rankOne]; ring

theorem scalar_nonnegative_of_isPosSemidef
    (f : Module.Dual ℝ V) (hf : f ≠ 0) (t : ℝ)
    (hPSD : (t • rankOne f).IsPosSemidef) : 0 ≤ t := by
  obtain ⟨e, he⟩ := exists_apply_eq_one f hf
  simpa [he] using hPSD.isNonneg.nonneg e

/-- Rank-one positive evaluation forms generate extreme rays of the PSD cone. -/
theorem rankOne_extreme_decomposition
    (f : Module.Dual ℝ V) (hf : f ≠ 0)
    (B C : LinearMap.BilinForm ℝ V)
    (hB : B.IsPosSemidef) (hC : C.IsPosSemidef)
    (hsum : B + C = rankOne f) :
    (∃ a : ℝ, 0 ≤ a ∧ B = a • rankOne f) ∧
      ∃ b : ℝ, 0 ≤ b ∧ C = b • rankOne f := by
  have hkerBC := ker_add_eq_inf B C hB hC
  have hker : LinearMap.ker f ≤ LinearMap.ker B ⊓ LinearMap.ker C := by
    rw [← hkerBC, hsum, ker_rankOne f hf]
  obtain ⟨a, ha⟩ := eq_smul_rankOne_of_ker_le f hf B hB.isSymm
    (fun x hx ↦ (hker hx).1)
  obtain ⟨b, hb⟩ := eq_smul_rankOne_of_ker_le f hf C hC.isSymm
    (fun x hx ↦ (hker hx).2)
  refine ⟨⟨a, ?_, ha⟩, ⟨b, ?_, hb⟩⟩
  · rw [ha] at hB
    exact scalar_nonnegative_of_isPosSemidef f hf a hB
  · rw [hb] at hC
    exact scalar_nonnegative_of_isPosSemidef f hf b hC

end PSDRangeOneExtreme
