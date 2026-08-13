import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Data.Real.Basic

noncomputable section

universe u v

namespace ProjectiveBasepoint

variable {V : Type u} [AddCommGroup V] [Module ℝ V]

/-- Every proper subspace of a real vector space admits a nonzero annihilating functional. -/
theorem exists_nonzero_annihilator (U : Submodule ℝ V) (hU : U < ⊤) :
    ∃ phi : Module.Dual ℝ V, phi ≠ 0 ∧ ∀ u ∈ U, phi u = 0 := by
  have hne : U.dualAnnihilator ≠ ⊥ := by
    intro hbot
    have htop : U = ⊤ :=
      (Submodule.dualAnnihilator_eq_bot_iff (W := U)).mp hbot
    exact hU.ne htop
  obtain ⟨phi, hphi⟩ := Submodule.nonzero_mem_of_bot_lt
    (bot_lt_iff_ne_bot.mpr hne)
  refine ⟨(phi : Module.Dual ℝ V), ?_, ?_⟩
  intro hzero
  apply hphi
  exact Subtype.ext hzero
  exact (Submodule.mem_dualAnnihilator (phi : Module.Dual ℝ V)).mp phi.2

/-- Restriction of an ambient evaluation functional to a linear system `W`. -/
def restrictedEval {X : Type v} (eval : X → Module.Dual ℝ V) (W : Submodule ℝ V) :
    X → Module.Dual ℝ W := fun x ↦ W.dualRestrict (eval x)

/-- Surjectivity on projective evaluation directions implies the exact basepoint property used in
the SOS-length proof: every proper subspace of the linear system has a common zero.

The hypothesis says that every nonzero functional on `W` occurs, up to a nonzero real scalar, as
evaluation at some point.  This is the set-level content of surjectivity of `X → P(W*)`. -/
theorem proper_subspace_has_common_zero_of_projective_surjective
    {X : Type v} (eval : X → Module.Dual ℝ V) (W : Submodule ℝ V)
    (hprojective : ∀ phi : Module.Dual ℝ W, phi ≠ 0 →
      ∃ x : X, ∃ a : ℝ, a ≠ 0 ∧ restrictedEval eval W x = a • phi) :
    ∀ U : Submodule ℝ V, U < W →
      ∃ x : X, ∀ g ∈ U, eval x g = 0 := by
  intro U hU
  let UW : Submodule ℝ W := U.comap W.subtype
  have hUW : UW < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro htop
    have hWU : W ≤ U := by
      intro w hw
      have hmem : (⟨w, hw⟩ : W) ∈ UW := by rw [htop]; trivial
      exact hmem
    exact hU.2 hWU
  obtain ⟨phi, hphi, hphiU⟩ := exists_nonzero_annihilator UW hUW
  obtain ⟨x, a, ha, hx⟩ := hprojective phi hphi
  refine ⟨x, ?_⟩
  intro g hg
  let gw : W := ⟨g, hU.le hg⟩
  have hzero : phi gw = 0 := hphiU gw hg
  have happ := LinearMap.congr_fun hx gw
  simpa only [restrictedEval, Submodule.dualRestrict_apply, LinearMap.smul_apply,
    smul_eq_mul, hzero, mul_zero] using happ

end ProjectiveBasepoint
