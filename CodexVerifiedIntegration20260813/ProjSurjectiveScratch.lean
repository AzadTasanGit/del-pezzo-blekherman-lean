import HVectorBasisScratch
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.RingTheory.Spectrum.Prime.Topology

universe u

open HomogeneousIdeal HomogeneousLocalization TopologicalSpace CategoryTheory Graded
open AlgebraicGeometry ProjectiveSpectrum

namespace AlgebraicGeometry.Proj

variable {A B σ τ : Type u}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
variable {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- Injectivity of a graded ring map descends to every degree-zero homogeneous localization. -/
theorem awayMap_injective_of_injective (f : 𝒜 →+*ᵍ ℬ)
    (hinj : Function.Injective f) (s : A) :
    Function.Injective (Away.map f s) := by
  intro x y hxy
  obtain ⟨cx, rfl⟩ := HomogeneousLocalization.mk_surjective x
  obtain ⟨cy, rfl⟩ := HomogeneousLocalization.mk_surjective y
  have hval := congrArg HomogeneousLocalization.val hxy
  simp only [HomogeneousLocalization.Away.map, HomogeneousLocalization.map_mk,
    HomogeneousLocalization.val_mk] at hval
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mk]
  rw [Localization.mk_eq_mk_iff, Localization.r_eq_r'] at hval ⊢
  obtain ⟨t, ht⟩ := hval
  obtain ⟨n, hn⟩ := t.2
  refine ⟨⟨s ^ n, ⟨n, rfl⟩⟩, ?_⟩
  apply hinj
  simpa only [map_mul, map_pow, hn] using ht

/-- A radical-condition projective morphism is surjective if it is surjective on every member of
a degree-one standard-open cover. -/
theorem mapOfRadical_surjective_of_degreeOne_cover
    (f : 𝒜 →+*ᵍ ℬ)
    (hf : (HomogeneousIdeal.irrelevant ℬ).toIdeal ≤
      (HomogeneousIdeal.map f (HomogeneousIdeal.irrelevant 𝒜)).toIdeal.radical)
    {J : Type*} (s : J → A) (hs : ∀ j, s j ∈ 𝒜 1)
    (hcover : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ Ideal.span (Set.range s))
    (hsurj : ∀ j, Function.Surjective
      (PrimeSpectrum.comap (Away.map f (s j)))) :
    Surjective (mapOfRadical f hf) := by
  let P : MorphismProperty Scheme.{u} := @Surjective
  change P (mapOfRadical f hf)
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := P)
    (fun j ↦ basicOpen 𝒜 (s j))
  · exact iSup_basicOpen_eq_top 𝒜 s hcover
  · intro j
    apply (MorphismProperty.arrow_mk_iso_iff P
      (mapOfRadicalRestrictArrowIso f hf Nat.zero_lt_one (s j) (hs j))).mpr
    apply (surjective_iff (Spec.map (CommRingCat.ofHom (Away.map f (s j))))).2
    exact hsurj j

/-- Finite and injective degree-zero localization maps give surjectivity by lying over. -/
theorem mapOfRadical_surjective_of_degreeOne_cover_of_away_finite_injective
    (f : 𝒜 →+*ᵍ ℬ)
    (hf : (HomogeneousIdeal.irrelevant ℬ).toIdeal ≤
      (HomogeneousIdeal.map f (HomogeneousIdeal.irrelevant 𝒜)).toIdeal.radical)
    {J : Type*} (s : J → A) (hs : ∀ j, s j ∈ 𝒜 1)
    (hcover : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ Ideal.span (Set.range s))
    (hfin : ∀ j, RingHom.Finite (Away.map f (s j)))
    (hinj : ∀ j, Function.Injective (Away.map f (s j))) :
    Surjective (mapOfRadical f hf) := by
  apply mapOfRadical_surjective_of_degreeOne_cover f hf s hs hcover
  intro j
  exact (RingHom.IsIntegral.of_finite (hfin j)).comap_surjective (hinj j)

/-- A finite graded map which is injective induces a surjective map on `Proj`, provided a
degree-one standard-open family covers the target. -/
theorem mapOfRadical_surjective_of_degreeOne_cover_of_finite_injective
    (f : 𝒜 →+*ᵍ ℬ)
    (hf : (HomogeneousIdeal.irrelevant ℬ).toIdeal ≤
      (HomogeneousIdeal.map f (HomogeneousIdeal.irrelevant 𝒜)).toIdeal.radical)
    {J : Type*} (s : J → A) (hs : ∀ j, s j ∈ 𝒜 1)
    (hcover : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ Ideal.span (Set.range s))
    (hfin : ∀ j, RingHom.Finite (Away.map f (s j)))
    (hinj : Function.Injective f) :
    Surjective (mapOfRadical f hf) := by
  apply mapOfRadical_surjective_of_degreeOne_cover_of_away_finite_injective
    f hf s hs hcover hfin
  intro j
  exact awayMap_injective_of_injective f hinj (s j)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A finite injective polynomial-to-coordinate-ring map makes the basepoint-free projective
evaluation morphism surjective. -/
theorem projectiveAevalOfRadical_surjective_of_toRingHom_finite_injective
    {K C I : Type u} [CommRing K] [CommRing C] [Algebra K C]
    (𝒞 : ℕ → Submodule K C) [GradedRing 𝒞]
    (g : I → C) (hg : ∀ i, g i ∈ 𝒞 1)
    (hbasepointFree : (HomogeneousIdeal.irrelevant 𝒞).toIdeal ≤
      (Ideal.span (Set.range g)).radical)
    (hfinite : (MvPolynomial.standardGradedAevalHom 𝒞 g hg).toRingHom.Finite)
    (hinjective : Function.Injective
      (MvPolynomial.standardGradedAevalHom 𝒞 g hg).toRingHom) :
    Surjective (projectiveAevalOfRadical 𝒞 g hg hbasepointFree) := by
  let f := MvPolynomial.standardGradedAevalHom 𝒞 g hg
  let hf := MvPolynomial.irrelevant_le_radical_map_of_le_radical_span_range 𝒞 f g
    (MvPolynomial.standardGradedAevalHom_apply_X 𝒞 g hg) hbasepointFree
  change Surjective (mapOfRadical f hf)
  apply mapOfRadical_surjective_of_degreeOne_cover_of_finite_injective f hf
    MvPolynomial.X (fun i ↦ MvPolynomial.isHomogeneous_X (R := K) i)
    MvPolynomial.irrelevant_toIdeal_le_span_range_X
  · intro i
    exact HomogeneousLocalization.Away.map_finite_of_toRingHom_finite f hfinite
      (MvPolynomial.isHomogeneous_X (R := K) i)
  · exact hinjective

/-- Over a domain coordinate ring, a nonempty finite free basis supplies injectivity as well as
finiteness.  Hence the `(1,c,1)`-style basis certificate gives a finite surjective projective
morphism of algebraic rank `c+2`. -/
theorem projectiveAevalOfRadical_isFinite_surjective_and_finrank_eq_add_two_of_basis
    {K C I : Type u} [Field K] [CommRing C] [IsDomain C] [Algebra K C]
    (𝒞 : ℕ → Submodule K C) [GradedRing 𝒞]
    (g : I → C) (hg : ∀ i, g i ∈ 𝒞 1)
    (hbasepointFree : (HomogeneousIdeal.irrelevant 𝒞).toIdeal ≤
      (Ideal.span (Set.range g)).radical)
    {c : ℕ}
    (b : let f := MvPolynomial.standardGradedAevalHom 𝒞 g hg
      letI := f.toRingHom.toAlgebra
      Module.Basis (Fin (c + 2)) (MvPolynomial I K) C) :
    IsFinite (projectiveAevalOfRadical 𝒞 g hg hbasepointFree) ∧
      Surjective (projectiveAevalOfRadical 𝒞 g hg hbasepointFree) ∧
      (let f := MvPolynomial.standardGradedAevalHom 𝒞 g hg
       letI := f.toRingHom.toAlgebra
       Module.finrank (MvPolynomial I K) C = c + 2) := by
  let f := MvPolynomial.standardGradedAevalHom 𝒞 g hg
  let _ : Algebra (MvPolynomial I K) C := f.toRingHom.toAlgebra
  let _ : Module.Free (MvPolynomial I K) C := Module.Free.of_basis b
  let _ : Module.Finite (MvPolynomial I K) C := Module.Finite.of_basis b
  have hfinite : f.toRingHom.Finite :=
    (RingHom.finite_algebraMap.mpr inferInstance : f.toRingHom.Finite)
  have hinjective : Function.Injective f.toRingHom :=
    FaithfulSMul.algebraMap_injective (MvPolynomial I K) C
  refine ⟨?_, ?_, ?_⟩
  · exact projectiveAevalOfRadical_isFinite_of_toRingHom_finite
      𝒞 g hg hbasepointFree hfinite
  · exact projectiveAevalOfRadical_surjective_of_toRingHom_finite_injective
      𝒞 g hg hbasepointFree hfinite hinjective
  · simpa using Module.finrank_eq_card_basis b

/-- The complete scheme-level consequence presently available from the `(1,c,1)` certificate:
the kernel morphism is finite and surjective, has algebraic rank `c+2`, and has nonzero
discriminant in characteristic zero. -/
theorem projectiveAevalOfRadical_isFinite_surjective_discr_and_rank_of_hVectorOneCOne
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
      Surjective (projectiveAevalOfRadical 𝒞 g hg hbasepointFree) ∧
      (let f := MvPolynomial.standardGradedAevalHom 𝒞 g hg
       letI := f.toRingHom.toAlgebra
       Algebra.discr (MvPolynomial I K) h.finBasis ≠ 0 ∧
         Module.finrank (MvPolynomial I K) C = c + 2) := by
  let f := MvPolynomial.standardGradedAevalHom 𝒞 g hg
  let _ : Algebra (MvPolynomial I K) C := f.toRingHom.toAlgebra
  have hfiniteDiscr :=
    projectiveAevalOfRadical_isFinite_and_discr_ne_zero_of_hVectorOneCOne
      𝒞 g hg hbasepointFree h
  have hfiniteSurjRank :=
    projectiveAevalOfRadical_isFinite_surjective_and_finrank_eq_add_two_of_basis
      𝒞 g hg hbasepointFree h.finBasis
  exact ⟨hfiniteDiscr.1, hfiniteSurjRank.2.1, hfiniteDiscr.2, hfiniteSurjRank.2.2⟩

end AlgebraicGeometry.Proj
