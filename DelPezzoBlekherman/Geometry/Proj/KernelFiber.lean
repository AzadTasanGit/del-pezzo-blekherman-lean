import DelPezzoBlekherman.Geometry.Proj.Finite
import DelPezzoBlekherman.Algebra.GenericFiber

noncomputable section

universe u

open AlgebraicGeometry

namespace AlgebraicGeometry.Proj

/-- A homogeneous free-module basis of cardinality `c + 2` is a single certificate for both
the finiteness of the induced projective morphism and the degree of every reduced geometric
fiber.  The second conclusion uses the same polynomial-to-coordinate-ring algebra structure
as the first, so no independent rank hypothesis is required. -/
theorem projectiveAevalOfRadical_isFinite_and_reduced_fiber_card_eq_add_two_of_basis
    {K C I : Type u} [Field K] [CommRing C] [Algebra K C]
    (𝒞 : ℕ → Submodule K C) [GradedRing 𝒞]
    (g : I → C) (hg : ∀ i, g i ∈ 𝒞 1)
    (hbasepointFree : (HomogeneousIdeal.irrelevant 𝒞).toIdeal ≤
      (Ideal.span (Set.range g)).radical)
    {c : ℕ}
    (b : let f := MvPolynomial.standardGradedAevalHom 𝒞 g hg
      letI := f.toRingHom.toAlgebra
      Module.Basis (Fin (c + 2)) (MvPolynomial I K) C)
    (p : Ideal (MvPolynomial I K)) [p.IsPrime] [IsAlgClosed p.ResidueField]
    (hred : let f := MvPolynomial.standardGradedAevalHom 𝒞 g hg
      letI := f.toRingHom.toAlgebra
      _root_.IsReduced (p.Fiber C)) :
    IsFinite (projectiveAevalOfRadical 𝒞 g hg hbasepointFree) ∧
      (let f := MvPolynomial.standardGradedAevalHom 𝒞 g hg
       letI := f.toRingHom.toAlgebra
       Nat.card (PrimeSpectrum (p.Fiber C)) = c + 2) := by
  let f := MvPolynomial.standardGradedAevalHom 𝒞 g hg
  let _ : Algebra (MvPolynomial I K) C := f.toRingHom.toAlgebra
  let _ : Module.Free (MvPolynomial I K) C := Module.Free.of_basis b
  let _ : Module.Finite (MvPolynomial I K) C := Module.Finite.of_basis b
  let _ : _root_.IsReduced (p.Fiber C) := hred
  constructor
  · exact (projectiveAevalOfRadical_isFinite_and_finrank_eq_add_two_of_basis
      𝒞 g hg hbasepointFree b).1
  · apply Ideal.natCard_primeSpectrum_fiber_eq_add_two p
    simpa using Module.finrank_eq_card_basis b

/-- The preceding reducedness hypothesis is automatic off the discriminant hypersurface.
Consequently a basis of size `c + 2` gives a finite projective morphism whose geometric fibers
away from that hypersurface consist of exactly `c + 2` points. -/
theorem projectiveAevalOfRadical_isFinite_and_fiber_card_eq_add_two_of_discr_not_mem
    {K C I : Type u} [Field K] [CommRing C] [Algebra K C]
    (𝒞 : ℕ → Submodule K C) [GradedRing 𝒞]
    (g : I → C) (hg : ∀ i, g i ∈ 𝒞 1)
    (hbasepointFree : (HomogeneousIdeal.irrelevant 𝒞).toIdeal ≤
      (Ideal.span (Set.range g)).radical)
    {c : ℕ}
    (b : let f := MvPolynomial.standardGradedAevalHom 𝒞 g hg
      letI := f.toRingHom.toAlgebra
      Module.Basis (Fin (c + 2)) (MvPolynomial I K) C)
    (p : Ideal (MvPolynomial I K)) [p.IsPrime] [IsAlgClosed p.ResidueField]
    (hdisc : let f := MvPolynomial.standardGradedAevalHom 𝒞 g hg
      letI := f.toRingHom.toAlgebra
      Algebra.discr (MvPolynomial I K) b ∉ p) :
    IsFinite (projectiveAevalOfRadical 𝒞 g hg hbasepointFree) ∧
      (let f := MvPolynomial.standardGradedAevalHom 𝒞 g hg
       letI := f.toRingHom.toAlgebra
       Nat.card (PrimeSpectrum (p.Fiber C)) = c + 2) := by
  let f := MvPolynomial.standardGradedAevalHom 𝒞 g hg
  let _ : Algebra (MvPolynomial I K) C := f.toRingHom.toAlgebra
  let _ : _root_.IsReduced (p.Fiber C) :=
    Ideal.isReduced_fiber_of_discr_not_mem b p hdisc
  exact projectiveAevalOfRadical_isFinite_and_reduced_fiber_card_eq_add_two_of_basis
    𝒞 g hg hbasepointFree b p inferInstance

/-- For a characteristic-zero domain coordinate ring, a basis of size `c + 2` produces both a
finite projective morphism and a nonzero discriminant.  Freeness of positive rank makes the
polynomial action faithful automatically.  Hence the reduced `c + 2`-point fiber locus from the
preceding theorem is a nonempty principal open. -/
theorem projectiveAevalOfRadical_isFinite_and_discr_ne_zero_of_basis
    {K C I : Type u} [Field K] [CharZero K] [CommRing C] [IsDomain C] [Algebra K C]
    (𝒞 : ℕ → Submodule K C) [GradedRing 𝒞]
    (g : I → C) (hg : ∀ i, g i ∈ 𝒞 1)
    (hbasepointFree : (HomogeneousIdeal.irrelevant 𝒞).toIdeal ≤
      (Ideal.span (Set.range g)).radical)
    {c : ℕ}
    (b : let f := MvPolynomial.standardGradedAevalHom 𝒞 g hg
      letI := f.toRingHom.toAlgebra
      Module.Basis (Fin (c + 2)) (MvPolynomial I K) C) :
    IsFinite (projectiveAevalOfRadical 𝒞 g hg hbasepointFree) ∧
      (let f := MvPolynomial.standardGradedAevalHom 𝒞 g hg
       letI := f.toRingHom.toAlgebra
       Algebra.discr (MvPolynomial I K) b ≠ 0) := by
  let f := MvPolynomial.standardGradedAevalHom 𝒞 g hg
  let _ : Algebra (MvPolynomial I K) C := f.toRingHom.toAlgebra
  let _ : Module.Free (MvPolynomial I K) C := Module.Free.of_basis b
  constructor
  · exact (projectiveAevalOfRadical_isFinite_and_finrank_eq_add_two_of_basis
      𝒞 g hg hbasepointFree b).1
  · exact Ideal.discr_ne_zero_of_finite_of_isDomain_of_charZero b

end AlgebraicGeometry.Proj
