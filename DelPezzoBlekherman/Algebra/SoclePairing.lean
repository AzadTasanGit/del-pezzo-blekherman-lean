import DelPezzoBlekherman.Algebra.ArtinianGorenstein

noncomputable section

universe u v w

open LinearMap

namespace ArtinianGorensteinDegreeOneCertificate

variable {K : Type u} {V : Type v} {S : Type w}
variable [Field K] [AddCommGroup V] [Module K V]
variable [AddCommGroup S] [Module K S] [Module.Free K S]

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

end ArtinianGorensteinDegreeOneCertificate
