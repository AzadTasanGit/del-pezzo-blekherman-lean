import DelPezzoBlekherman.Geometry.Proj.KernelFiber

noncomputable section

universe u

/-- The three blocks in the `h`-vector `(1, c, 1)`: one degree-zero generator, `c`
degree-one generators, and one degree-two generator. -/
abbrev HVectorOneCOneIndex (c : ℕ) := Fin 1 ⊕ (Fin c ⊕ Fin 1)

/-- The `(1, c, 1)` index type has cardinality `c + 2`. -/
noncomputable def hVectorOneCOneIndexEquivFin (c : ℕ) :
    HVectorOneCOneIndex c ≃ Fin (c + 2) :=
  ((Equiv.sumCongr (Equiv.refl (Fin 1)) finSumFinEquiv).trans finSumFinEquiv).trans
    (finCongr (by omega))

/-- A concrete graded free-module certificate realizing Hilbert numerator `1 + c t + t²`.
This is the exact algebraic datum needed downstream from the Cohen--Macaulay/Hilbert-series
argument: a polynomial-module basis with one generator in degree zero, `c` in degree one, and
one in degree two. -/
structure HVectorOneCOneFreeCertificate
    (K P C : Type u) [Field K] [CommRing P] [CommRing C]
    [Algebra K C] [Module P C]
    (𝒞 : ℕ → Submodule K C) (c : ℕ) where
  basis : Module.Basis (HVectorOneCOneIndex c) P C
  degreeZero : ∀ i : Fin 1, basis (Sum.inl i) ∈ 𝒞 0
  degreeOne : ∀ i : Fin c, basis (Sum.inr (Sum.inl i)) ∈ 𝒞 1
  degreeTwo : ∀ i : Fin 1, basis (Sum.inr (Sum.inr i)) ∈ 𝒞 2

namespace HVectorOneCOneFreeCertificate

variable {K P C : Type u} [Field K] [CommRing P] [CommRing C]
variable [Algebra K C] [Module P C]
variable {𝒞 : ℕ → Submodule K C} {c : ℕ}

/-- Forgetting the degree labels and reindexing gives the `Fin (c + 2)` basis used by the
finite-morphism and fiber-degree theorems. -/
noncomputable def finBasis (h : HVectorOneCOneFreeCertificate K P C 𝒞 c) :
    Module.Basis (Fin (c + 2)) P C :=
  h.basis.reindex (hVectorOneCOneIndexEquivFin c)

end HVectorOneCOneFreeCertificate

open AlgebraicGeometry

namespace AlgebraicGeometry.Proj

/-- An `(1, c, 1)` graded free-module certificate over the chosen degree-one polynomial
subring yields a finite projective evaluation morphism and a nonzero discriminant. -/
theorem projectiveAevalOfRadical_isFinite_and_discr_ne_zero_of_hVectorOneCOne
    {K C I : Type u} [Field K] [CharZero K] [CommRing C] [IsDomain C] [Algebra K C]
    (𝒞 : ℕ → Submodule K C) [GradedRing 𝒞]
    (g : I → C) (hg : ∀ i, g i ∈ 𝒞 1)
    (hbasepointFree : (HomogeneousIdeal.irrelevant 𝒞).toIdeal ≤
      (Ideal.span (Set.range g)).radical)
    {c : ℕ}
    (h : let f := MvPolynomial.standardGradedAevalHom 𝒞 g hg
      letI := f.toRingHom.toAlgebra
      HVectorOneCOneFreeCertificate K (MvPolynomial I K) C 𝒞 c) :
    IsFinite (projectiveAevalOfRadical 𝒞 g hg hbasepointFree) ∧
      (let f := MvPolynomial.standardGradedAevalHom 𝒞 g hg
       letI := f.toRingHom.toAlgebra
       Algebra.discr (MvPolynomial I K) h.finBasis ≠ 0) := by
  let f := MvPolynomial.standardGradedAevalHom 𝒞 g hg
  let _ : Algebra (MvPolynomial I K) C := f.toRingHom.toAlgebra
  exact projectiveAevalOfRadical_isFinite_and_discr_ne_zero_of_basis
    𝒞 g hg hbasepointFree h.finBasis

/-- Full geometric-fiber consequence of the `(1, c, 1)` certificate: the projective map is
finite, its discriminant is globally nonzero, and every geometric base point outside that
discriminant has a reduced fiber with exactly `c + 2` points. -/
theorem projectiveAevalOfRadical_hVectorOneCOne_fiber_card_eq_add_two
    {K C I : Type u} [Field K] [CharZero K] [CommRing C] [IsDomain C] [Algebra K C]
    (𝒞 : ℕ → Submodule K C) [GradedRing 𝒞]
    (g : I → C) (hg : ∀ i, g i ∈ 𝒞 1)
    (hbasepointFree : (HomogeneousIdeal.irrelevant 𝒞).toIdeal ≤
      (Ideal.span (Set.range g)).radical)
    {c : ℕ}
    (h : let f := MvPolynomial.standardGradedAevalHom 𝒞 g hg
      letI := f.toRingHom.toAlgebra
      HVectorOneCOneFreeCertificate K (MvPolynomial I K) C 𝒞 c)
    (p : Ideal (MvPolynomial I K)) [p.IsPrime] [IsAlgClosed p.ResidueField]
    (hp : let f := MvPolynomial.standardGradedAevalHom 𝒞 g hg
      letI := f.toRingHom.toAlgebra
      Algebra.discr (MvPolynomial I K) h.finBasis ∉ p) :
    IsFinite (projectiveAevalOfRadical 𝒞 g hg hbasepointFree) ∧
      (let f := MvPolynomial.standardGradedAevalHom 𝒞 g hg
       letI := f.toRingHom.toAlgebra
       Algebra.discr (MvPolynomial I K) h.finBasis ≠ 0 ∧
         Nat.card (PrimeSpectrum (p.Fiber C)) = c + 2) := by
  let f := MvPolynomial.standardGradedAevalHom 𝒞 g hg
  let _ : Algebra (MvPolynomial I K) C := f.toRingHom.toAlgebra
  have hfiniteDiscr :=
    projectiveAevalOfRadical_isFinite_and_discr_ne_zero_of_hVectorOneCOne
      𝒞 g hg hbasepointFree h
  have hfiber :=
    projectiveAevalOfRadical_isFinite_and_fiber_card_eq_add_two_of_discr_not_mem
      𝒞 g hg hbasepointFree h.finBasis p hp
  exact ⟨hfiniteDiscr.1, hfiniteDiscr.2, hfiber.2⟩

end AlgebraicGeometry.Proj
