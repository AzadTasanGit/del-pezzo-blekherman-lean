import HVectorBasisScratch
import ProjectivePolynomialDenseScratch

noncomputable section

universe u

open Set

namespace AlgebraicGeometry.Proj

/-- The real discriminant polynomial attached to an `(1,c,1)` free-basis certificate. -/
def realHVectorDiscr
    {C I : Type} [CommRing C] [IsDomain C] [Algebra ℝ C]
    (𝒞 : ℕ → Submodule ℝ C) [GradedRing 𝒞]
    (g : I → C) (hg : ∀ i, g i ∈ 𝒞 1) {c : ℕ}
    (h : let f := MvPolynomial.standardGradedAevalHom 𝒞 g hg
      letI := f.toRingHom.toAlgebra
      HVectorOneCOneFreeCertificate ℝ (MvPolynomial I ℝ) C 𝒞 c) :
    MvPolynomial I ℝ := by
  let f := MvPolynomial.standardGradedAevalHom 𝒞 g hg
  let _ : Algebra (MvPolynomial I ℝ) C := f.toRingHom.toAlgebra
  exact Algebra.discr (MvPolynomial I ℝ) h.finBasis

theorem realHVectorDiscr_ne_zero
    {C I : Type} [CommRing C] [IsDomain C] [Algebra ℝ C]
    (𝒞 : ℕ → Submodule ℝ C) [GradedRing 𝒞]
    (g : I → C) (hg : ∀ i, g i ∈ 𝒞 1)
    (hbasepointFree : (HomogeneousIdeal.irrelevant 𝒞).toIdeal ≤
      (Ideal.span (Set.range g)).radical)
    {c : ℕ}
    (h : let f := MvPolynomial.standardGradedAevalHom 𝒞 g hg
      letI := f.toRingHom.toAlgebra
      HVectorOneCOneFreeCertificate ℝ (MvPolynomial I ℝ) C 𝒞 c) :
    realHVectorDiscr 𝒞 g hg h ≠ 0 := by
  let f := MvPolynomial.standardGradedAevalHom 𝒞 g hg
  let _ : Algebra (MvPolynomial I ℝ) C := f.toRingHom.toAlgebra
  exact (projectiveAevalOfRadical_isFinite_and_discr_ne_zero_of_hVectorOneCOne
    𝒞 g hg hbasepointFree h).2

/-- The projective nonvanishing locus of the certificate discriminant after basis transport. -/
def realHVectorOmega
    {C I : Type} {W : Type u} [Fintype I] [CommRing C] [IsDomain C] [Algebra ℝ C]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (b : Module.Basis I ℝ W)
    (𝒞 : ℕ → Submodule ℝ C) [GradedRing 𝒞]
    (g : I → C) (hg : ∀ i, g i ∈ 𝒞 1) {c : ℕ}
    (h : let f := MvPolynomial.standardGradedAevalHom 𝒞 g hg
      letI := f.toRingHom.toAlgebra
      HVectorOneCOneFreeCertificate ℝ (MvPolynomial I ℝ) C 𝒞 c) :
    Set (RealProjectiveTopology.Direction W) :=
  RealProjectiveTopology.directionOf W ''
    {w : {w : W // w ≠ 0} |
      (w : W) ∈ RealProjectiveTopology.basisContinuousLinearEquiv b ''
        {x : I → ℝ | MvPolynomial.eval x (realHVectorDiscr 𝒞 g hg h) ≠ 0}}

theorem dense_realHVectorOmega
    {C I : Type} {W : Type u} [Fintype I] [CommRing C] [IsDomain C] [Algebra ℝ C]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (b : Module.Basis I ℝ W)
    (𝒞 : ℕ → Submodule ℝ C) [GradedRing 𝒞]
    (g : I → C) (hg : ∀ i, g i ∈ 𝒞 1)
    (hbasepointFree : (HomogeneousIdeal.irrelevant 𝒞).toIdeal ≤
      (Ideal.span (Set.range g)).radical)
    {c : ℕ}
    (h : let f := MvPolynomial.standardGradedAevalHom 𝒞 g hg
      letI := f.toRingHom.toAlgebra
      HVectorOneCOneFreeCertificate ℝ (MvPolynomial I ℝ) C 𝒞 c) :
    Dense (realHVectorOmega b 𝒞 g hg h) :=
  MvPolynomial.dense_directionOf_image_equiv_eval_ne_zero
    (RealProjectiveTopology.basisContinuousLinearEquiv b)
    (realHVectorDiscr 𝒞 g hg h)
    (realHVectorDiscr_ne_zero 𝒞 g hg hbasepointFree h)

/-- The `(1,c,1)` free-basis certificate makes the reduced-fiber discriminant locus Euclidean
dense in the concrete compact real projective coordinate space. -/
theorem dense_real_projective_discr_locus_of_hVectorOneCOne
    {C I : Type} [Fintype I] [CommRing C] [IsDomain C] [Algebra ℝ C]
    (𝒞 : ℕ → Submodule ℝ C) [GradedRing 𝒞]
    (g : I → C) (hg : ∀ i, g i ∈ 𝒞 1)
    (hbasepointFree : (HomogeneousIdeal.irrelevant 𝒞).toIdeal ≤
      (Ideal.span (Set.range g)).radical)
    {c : ℕ}
    (h : let f := MvPolynomial.standardGradedAevalHom 𝒞 g hg
      letI := f.toRingHom.toAlgebra
      HVectorOneCOneFreeCertificate ℝ (MvPolynomial I ℝ) C 𝒞 c) :
    let f := MvPolynomial.standardGradedAevalHom 𝒞 g hg
    letI := f.toRingHom.toAlgebra
    Dense (RealProjectiveTopology.directionOf (I → ℝ) ''
      {v : {v : I → ℝ // v ≠ 0} |
        MvPolynomial.eval (v : I → ℝ)
          (Algebra.discr (MvPolynomial I ℝ) h.finBasis) ≠ 0}) := by
  let f := MvPolynomial.standardGradedAevalHom 𝒞 g hg
  let _ : Algebra (MvPolynomial I ℝ) C := f.toRingHom.toAlgebra
  have hdisc : Algebra.discr (MvPolynomial I ℝ) h.finBasis ≠ 0 :=
    (projectiveAevalOfRadical_isFinite_and_discr_ne_zero_of_hVectorOneCOne
      𝒞 g hg hbasepointFree h).2
  exact MvPolynomial.dense_directionOf_image_eval_ne_zero _ hdisc

/-- The same dense discriminant locus transported from polynomial coordinates to any continuous
linear coordinate model, in particular the continuous dual of a Hankel radical. -/
theorem dense_real_projective_discr_locus_equiv_of_hVectorOneCOne
    {C I : Type} {W : Type u} [Fintype I] [CommRing C] [IsDomain C] [Algebra ℝ C]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (e : (I → ℝ) ≃L[ℝ] W)
    (𝒞 : ℕ → Submodule ℝ C) [GradedRing 𝒞]
    (g : I → C) (hg : ∀ i, g i ∈ 𝒞 1)
    (hbasepointFree : (HomogeneousIdeal.irrelevant 𝒞).toIdeal ≤
      (Ideal.span (Set.range g)).radical)
    {c : ℕ}
    (h : let f := MvPolynomial.standardGradedAevalHom 𝒞 g hg
      letI := f.toRingHom.toAlgebra
      HVectorOneCOneFreeCertificate ℝ (MvPolynomial I ℝ) C 𝒞 c) :
    let f := MvPolynomial.standardGradedAevalHom 𝒞 g hg
    letI := f.toRingHom.toAlgebra
    Dense (RealProjectiveTopology.directionOf W ''
      {w : {w : W // w ≠ 0} |
        (w : W) ∈ e '' {x : I → ℝ |
          MvPolynomial.eval x
            (Algebra.discr (MvPolynomial I ℝ) h.finBasis) ≠ 0}}) := by
  let f := MvPolynomial.standardGradedAevalHom 𝒞 g hg
  let _ : Algebra (MvPolynomial I ℝ) C := f.toRingHom.toAlgebra
  have hdisc : Algebra.discr (MvPolynomial I ℝ) h.finBasis ≠ 0 :=
    (projectiveAevalOfRadical_isFinite_and_discr_ne_zero_of_hVectorOneCOne
      𝒞 g hg hbasepointFree h).2
  exact MvPolynomial.dense_directionOf_image_equiv_eval_ne_zero e _ hdisc

/-- Basis-indexed version of the transported discriminant-density theorem. -/
theorem dense_real_projective_discr_locus_basis_of_hVectorOneCOne
    {C I : Type} {W : Type u} [Fintype I] [CommRing C] [IsDomain C] [Algebra ℝ C]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (b : Module.Basis I ℝ W)
    (𝒞 : ℕ → Submodule ℝ C) [GradedRing 𝒞]
    (g : I → C) (hg : ∀ i, g i ∈ 𝒞 1)
    (hbasepointFree : (HomogeneousIdeal.irrelevant 𝒞).toIdeal ≤
      (Ideal.span (Set.range g)).radical)
    {c : ℕ}
    (h : let f := MvPolynomial.standardGradedAevalHom 𝒞 g hg
      letI := f.toRingHom.toAlgebra
      HVectorOneCOneFreeCertificate ℝ (MvPolynomial I ℝ) C 𝒞 c) :
    let f := MvPolynomial.standardGradedAevalHom 𝒞 g hg
    letI := f.toRingHom.toAlgebra
    Dense (RealProjectiveTopology.directionOf W ''
      {w : {w : W // w ≠ 0} |
        (w : W) ∈ RealProjectiveTopology.basisContinuousLinearEquiv b ''
          {x : I → ℝ | MvPolynomial.eval x
            (Algebra.discr (MvPolynomial I ℝ) h.finBasis) ≠ 0}}) :=
  dense_real_projective_discr_locus_equiv_of_hVectorOneCOne
    (RealProjectiveTopology.basisContinuousLinearEquiv b)
    𝒞 g hg hbasepointFree h

end AlgebraicGeometry.Proj
