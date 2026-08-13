import DelPezzoBlekherman.Algebra.ArtinianGorenstein
import Mathlib.LinearAlgebra.Dual.Lemmas

noncomputable section

universe u v w

open LinearMap

namespace ArtinianGorensteinDegreeOneCertificate

variable {K : Type u} {V : Type v} {S : Type w}
variable [Field K] [AddCommGroup V] [Module K V]
variable [AddCommGroup S] [Module K S]

/-- If the Hankel form pulled back from a socle functional is nonzero, then the socle
functional itself is nonzero.  This packages the implication used in the paper after observing
that a nonzero degree-two functional gives a nonzero Hankel form in a standard graded ring. -/
theorem socleFunctional_ne_zero_of_pullbackQuotient_ne_zero
    {U : Type v} [AddCommGroup U] [Module K U]
    (W : Submodule K U)
    (mul11 : (U ⧸ W) →ₗ[K] (U ⧸ W) →ₗ[K] S)
    (ellBar : S →ₗ[K] K)
    (hHankel :
      LinearMap.BilinForm.pullbackQuotient W (mul11.compr₂ ellBar) ≠ 0) :
    ellBar ≠ 0 := by
  intro hellBar
  apply hHankel
  ext x y
  simp [hellBar, LinearMap.BilinForm.pullbackQuotient]

variable [Module.Free K S]

/-- A symmetric degree-one multiplication map has a nondegenerate socle pairing as soon as no
nonzero degree-one element annihilates all degree-one elements.  This is the special
socle-annihilator characterization needed from the Artinian Gorenstein quotient. -/
theorem nondegenerate_soclePairing_of_annihilator
    (mul11 : V →ₗ[K] V →ₗ[K] S)
    (hsymm : ∀ x y, mul11 x y = mul11 y x)
    (hS : Module.finrank K S = 1)
    (hann : ∀ x, (∀ y, mul11 x y = 0) → x = 0) :
    (mul11.compr₂ (socleEquivOfFinrankEqOne hS).toLinearMap).Nondegenerate := by
  constructor
  · intro x hx
    apply hann x
    intro y
    apply (socleEquivOfFinrankEqOne hS).injective
    exact (hx y).trans (map_zero _).symm
  · intro y hy
    apply hann y
    intro x
    rw [hsymm]
    apply (socleEquivOfFinrankEqOne hS).injective
    exact (hy x).trans (map_zero _).symm

/-- A nonzero functional on a one-dimensional socle is injective.  This is the precise
linear-algebra fact used in Theorem 4.3 when the induced functional `ellBar : A₂ → K` is
substituted for an arbitrary identification `A₂ ≃ K`. -/
theorem socleFunctional_injective
    (hS : Module.finrank K S = 1)
    (ellBar : S →ₗ[K] K) (hellBar : ellBar ≠ 0) :
    Function.Injective ellBar := by
  let _ : Module.Finite K S := Module.finite_of_finrank_pos (by omega)
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := ellBar) (by simpa only [Module.finrank_self] using hS)).mpr
  exact LinearMap.surjective hellBar

/-- The perfect degree-one multiplication pairing remains perfect after composing with the
specific nonzero functional induced on the one-dimensional socle.  Unlike
`nondegenerate_soclePairing_of_annihilator`, this theorem does not choose a socle coordinate:
its conclusion is about the actual functional appearing in the Hankel form. -/
theorem nondegenerate_soclePairing_of_nonzero_functional
    (mul11 : V →ₗ[K] V →ₗ[K] S)
    (hsymm : ∀ x y, mul11 x y = mul11 y x)
    (hS : Module.finrank K S = 1)
    (hann : ∀ x, (∀ y, mul11 x y = 0) → x = 0)
    (ellBar : S →ₗ[K] K) (hellBar : ellBar ≠ 0) :
    (mul11.compr₂ ellBar).Nondegenerate := by
  have hinjective := socleFunctional_injective hS ellBar hellBar
  constructor
  · intro x hx
    apply hann x
    intro y
    apply hinjective
    exact (hx y).trans (map_zero ellBar).symm
  · intro y hy
    apply hann y
    intro x
    rw [hsymm]
    apply hinjective
    exact (hy x).trans (map_zero ellBar).symm

/-- Thus Hilbert value `dim S = 1`, symmetric multiplication, and the Gorenstein
socle-annihilator property construct the perfect-pairing certificate used by the kernel/rank
theorem. -/
noncomputable def ofSocleAnnihilator
    (mul11 : V →ₗ[K] V →ₗ[K] S)
    (hsymm : ∀ x y, mul11 x y = mul11 y x)
    (hS : Module.finrank K S = 1)
    (hann : ∀ x, (∀ y, mul11 x y = 0) → x = 0) :
    ArtinianGorensteinDegreeOneCertificate K V S :=
  ofMulOfSocleFinrankOne mul11 hS
    (nondegenerate_soclePairing_of_annihilator mul11 hsymm hS hann)

/-- End-to-end special Gorenstein kernel theorem.  Suppose `V/W` is the degree-one part of the
Artinian quotient, `S` is its one-dimensional degree-two socle, multiplication is symmetric,
and no nonzero degree-one element annihilates all degree-one elements.  With the Hilbert
dimensions from the paper, the pulled-back Hankel form then has radical dimension `m + 1` and
rank `c`. -/
theorem parameterSpace_finrank_and_hankelRank_of_socleAnnihilator
    {U : Type v} [AddCommGroup U] [Module K U] [Module.Finite K U]
    (W : Submodule K U)
    (mul11 : (U ⧸ W) →ₗ[K] (U ⧸ W) →ₗ[K] S)
    (hsymm : ∀ x y, mul11 x y = mul11 y x)
    (hS : Module.finrank K S = 1)
    (hann : ∀ x, (∀ y, mul11 x y = 0) → x = 0)
    {m c : ℕ}
    (hU : Module.finrank K U = m + c + 1)
    (hQ : Module.finrank K (U ⧸ W) = c) :
    Module.finrank K W = m + 1 ∧
      LinearMap.BilinForm.finiteRank
        (hankelForm W (ofSocleAnnihilator mul11 hsymm hS hann)) = c :=
  parameterSpace_finrank_and_hankelRank W
    (ofSocleAnnihilator mul11 hsymm hS hann) hU hQ

/-- Paper-faithful form of the Artinian Gorenstein step in Theorem 4.3.  The functional on the
degree-two socle is supplied explicitly and assumed only nonzero.  The theorem proves that the
Hankel form obtained by pulling its multiplication pairing back to the original degree-one space
has radical dimension `m + 1` and rank `c`.

This removes the auxiliary choice of a socle coordinate from the rank theorem's conclusion. -/
theorem parameterSpace_finrank_and_hankelRank_of_nonzeroSocleFunctional
    {U : Type v} [AddCommGroup U] [Module K U] [Module.Finite K U]
    (W : Submodule K U)
    (mul11 : (U ⧸ W) →ₗ[K] (U ⧸ W) →ₗ[K] S)
    (hsymm : ∀ x y, mul11 x y = mul11 y x)
    (hS : Module.finrank K S = 1)
    (hann : ∀ x, (∀ y, mul11 x y = 0) → x = 0)
    (ellBar : S →ₗ[K] K) (hellBar : ellBar ≠ 0)
    {m c : ℕ}
    (hU : Module.finrank K U = m + c + 1)
    (hQ : Module.finrank K (U ⧸ W) = c) :
    Module.finrank K W = m + 1 ∧
      LinearMap.BilinForm.finiteRank
        (LinearMap.BilinForm.pullbackQuotient W (mul11.compr₂ ellBar)) = c := by
  have hperfect :=
    nondegenerate_soclePairing_of_nonzero_functional mul11 hsymm hS hann ellBar hellBar
  exact ⟨finrank_parameterSpace_eq_add_one W hU hQ,
    (LinearMap.BilinForm.finiteRank_pullbackQuotient_eq W
      (mul11.compr₂ ellBar) hperfect).trans hQ⟩

/-- Rank theorem with the paper's nonzeroness input expressed at the level of the actual Hankel
form.  The induced socle functional is proved nonzero internally, so no chosen socle coordinate
and no separate functional-nonzeroness assumption appears in the result. -/
theorem parameterSpace_finrank_and_hankelRank_of_nonzeroHankel
    {U : Type v} [AddCommGroup U] [Module K U] [Module.Finite K U]
    (W : Submodule K U)
    (mul11 : (U ⧸ W) →ₗ[K] (U ⧸ W) →ₗ[K] S)
    (hsymm : ∀ x y, mul11 x y = mul11 y x)
    (hS : Module.finrank K S = 1)
    (hann : ∀ x, (∀ y, mul11 x y = 0) → x = 0)
    (ellBar : S →ₗ[K] K)
    (hHankel :
      LinearMap.BilinForm.pullbackQuotient W (mul11.compr₂ ellBar) ≠ 0)
    {m c : ℕ}
    (hU : Module.finrank K U = m + c + 1)
    (hQ : Module.finrank K (U ⧸ W) = c) :
    Module.finrank K W = m + 1 ∧
      LinearMap.BilinForm.finiteRank
        (LinearMap.BilinForm.pullbackQuotient W (mul11.compr₂ ellBar)) = c :=
  parameterSpace_finrank_and_hankelRank_of_nonzeroSocleFunctional
    W mul11 hsymm hS hann ellBar
      (socleFunctional_ne_zero_of_pullbackQuotient_ne_zero W mul11 ellBar hHankel)
    hU hQ

end ArtinianGorensteinDegreeOneCertificate
