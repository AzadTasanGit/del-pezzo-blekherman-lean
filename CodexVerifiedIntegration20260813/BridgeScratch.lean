import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.AlgebraicGeometry.Morphisms.Finite

namespace MvPolynomial

universe uR uB uM uσ uτ

variable {R : Type uR} {B : Type uB} {M : Type uM} {σ : Type uσ} {τ : Type uτ}
variable [CommSemiring R] [CommSemiring B] [AddCommMonoid M]
variable [SetLike τ B] [AddSubmonoidClass τ B]

/-- Evaluating weighted polynomial variables at homogeneous elements gives a graded ring hom. -/
noncomputable def gradedEval₂Hom
    (w : σ → M) (ℬ : M → τ) [SetLike.GradedMonoid ℬ]
    (f : R →+* B) (g : σ → B)
    (hf : ∀ r, f r ∈ ℬ 0) (hg : ∀ i, g i ∈ ℬ (w i)) :
    weightedHomogeneousSubmodule R w →+*ᵍ ℬ :=
  GradedRingHom.mk (eval₂Hom f g) <| by
    intro m p hp
    rw [mem_weightedHomogeneousSubmodule] at hp
    induction hp using IsWeightedHomogeneous.induction_on with
    | zero => exact zero_mem (ℬ m)
    | add p q hp hq ihp ihq => simpa using add_mem ihp ihq
    | monomial d r hr =>
      rw [eval₂Hom_monomial]
      have hprod : d.prod (fun i n ↦ g i ^ n) ∈ ℬ ((Finsupp.weight w) d) := by
        simpa only [Finsupp.prod, Finsupp.weight_apply, Finsupp.sum] using
          (SetLike.prod_pow_mem_graded ℬ w g d fun i _ ↦ hg i)
      simpa [hr] using SetLike.mul_mem_graded (hf r) hprod

/-- Algebra evaluation at homogeneous elements, bundled as a graded ring homomorphism. -/
noncomputable def gradedAevalHom
    [Algebra R B] (w : σ → M) (ℬ : M → Submodule R B) [SetLike.GradedMonoid ℬ]
    (g : σ → B) (hg : ∀ i, g i ∈ ℬ (w i)) :
    weightedHomogeneousSubmodule R w →+*ᵍ ℬ :=
  gradedEval₂Hom w ℬ (algebraMap R B) g (fun r ↦ by
    rw [Algebra.algebraMap_eq_smul_one]
    exact (ℬ 0).smul_mem r (SetLike.one_mem_graded ℬ)) hg

/-- The usual polynomial grading maps to any grading when variables map to degree one. -/
noncomputable def standardGradedAevalHom
    [Algebra R B] (ℬ : ℕ → Submodule R B) [SetLike.GradedMonoid ℬ]
    (g : σ → B) (hg : ∀ i, g i ∈ ℬ 1) :
    homogeneousSubmodule σ R →+*ᵍ ℬ :=
  gradedAevalHom (fun _ ↦ 1) ℬ g hg

@[simp]
theorem standardGradedAevalHom_apply_X
    [Algebra R B] (ℬ : ℕ → Submodule R B) [SetLike.GradedMonoid ℬ]
    (g : σ → B) (hg : ∀ i, g i ∈ ℬ 1) (i : σ) :
    standardGradedAevalHom ℬ g hg (X i) = g i := by
  change (eval₂Hom (algebraMap R B) g) (X i) = g i
  exact eval₂Hom_X' _ _ _

end MvPolynomial

namespace MvPolynomial

universe uK uC uI

variable {K : Type uK} {C : Type uC} {I : Type uI}

attribute [local instance] gradedAlgebra

/-- If degree-one images generate the target irrelevant ideal, polynomial evaluation
induces a map on projective spectra. -/
theorem irrelevant_le_map_of_span_range
    [CommRing K] [CommRing C] [Algebra K C]
    (ℬ : ℕ → Submodule K C) [GradedRing ℬ]
    (f : homogeneousSubmodule I K →+*ᵍ ℬ)
    (g : I → C) (hX : ∀ i, f (X i) = g i)
    (hspan : (HomogeneousIdeal.irrelevant ℬ).toIdeal ≤ Ideal.span (Set.range g)) :
    HomogeneousIdeal.irrelevant ℬ ≤
      HomogeneousIdeal.map f
        (HomogeneousIdeal.irrelevant (homogeneousSubmodule I K)) := by
  change (HomogeneousIdeal.irrelevant ℬ).toIdeal ≤
    (HomogeneousIdeal.map f
      (HomogeneousIdeal.irrelevant (homogeneousSubmodule I K))).toIdeal
  rw [HomogeneousIdeal.toIdeal_map]
  refine hspan.trans ?_
  rw [Ideal.span_le]
  rintro y ⟨i, rfl⟩
  rw [← hX i]
  exact Ideal.mem_map_of_mem _ <|
    HomogeneousIdeal.mem_irrelevant_of_mem _ Nat.zero_lt_one
      (isHomogeneous_X (R := K) i)

/-- The basepoint-free condition, expressed by radical containment, supplies precisely the
irrelevant-ideal hypothesis needed by the radical form of projective functoriality. -/
theorem irrelevant_le_radical_map_of_le_radical_span_range
    [CommRing K] [CommRing C] [Algebra K C]
    (ℬ : ℕ → Submodule K C) [GradedRing ℬ]
    (f : homogeneousSubmodule I K →+*ᵍ ℬ)
    (g : I → C) (hX : ∀ i, f (X i) = g i)
    (hspan : (HomogeneousIdeal.irrelevant ℬ).toIdeal ≤
      (Ideal.span (Set.range g)).radical) :
    (HomogeneousIdeal.irrelevant ℬ).toIdeal ≤
      (HomogeneousIdeal.map f
        (HomogeneousIdeal.irrelevant (homogeneousSubmodule I K))).toIdeal.radical := by
  refine hspan.trans (Ideal.radical_mono ?_)
  rw [Ideal.span_le]
  rintro y ⟨i, rfl⟩
  rw [← hX i, HomogeneousIdeal.toIdeal_map]
  exact Ideal.mem_map_of_mem _ <|
    HomogeneousIdeal.mem_irrelevant_of_mem _ Nat.zero_lt_one
      (isHomogeneous_X (R := K) i)

end MvPolynomial

namespace AlgebraicGeometry.Proj

open CategoryTheory

universe u

variable {A B σ τ : Type u}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
variable {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A family covers `Proj` as soon as its ideal contains the irrelevant ideal up to radical. -/
theorem iSup_basicOpen_eq_top_of_le_radical {ι : Type*} (f : ι → A)
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ (Ideal.span (Set.range f)).radical) :
    ⨆ i, basicOpen 𝒜 (f i) = ⊤ := by
  classical
  refine top_le_iff.mp fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ?_
  by_contra! H
  simp only [mem_basicOpen, Decidable.not_not] at H
  refine x.not_irrelevant_le (hf.trans ?_)
  exact x.isPrime.radical_le_iff.mpr <| by
    rwa [Ideal.span_le, Set.range_subset_iff]

/-- The projective morphism defined by a basepoint-free family of degree-one elements. -/
noncomputable def projectiveAeval
    {K C I : Type u} [CommRing K] [CommRing C] [Algebra K C]
    (𝒞 : ℕ → Submodule K C) [GradedRing 𝒞]
    (g : I → C) (hg : ∀ i, g i ∈ 𝒞 1)
    (hspan : (HomogeneousIdeal.irrelevant 𝒞).toIdeal ≤ Ideal.span (Set.range g)) :
    Proj 𝒞 ⟶ Proj (MvPolynomial.homogeneousSubmodule I K) :=
  let f := MvPolynomial.standardGradedAevalHom 𝒞 g hg
  map f (MvPolynomial.irrelevant_le_map_of_span_range 𝒞 f g
    (MvPolynomial.standardGradedAevalHom_apply_X 𝒞 g hg) hspan)

/-- On a standard affine chart, `Proj.map` is the spectrum map on degree-zero localizations. -/
noncomputable def mapRestrictArrowIso
    (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤
      HomogeneousIdeal.map f (HomogeneousIdeal.irrelevant 𝒜))
    {i : ℕ} (hi : 0 < i) (s : A) (hs : s ∈ 𝒜 i) :
    Arrow.mk (map f hf ∣_ basicOpen 𝒜 s) ≅
      Arrow.mk (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map f s))) := by
  let eSrc :=
    Scheme.isoOfEq (Proj ℬ) (map_preimage_basicOpen f hf s) ≪≫
      basicOpenIsoSpec ℬ (f s) (f.2 hs) hi
  refine Arrow.isoMk
    eSrc
    (basicOpenIsoSpec 𝒜 s hs hi) ?_
  apply (cancel_mono ((basicOpenIsoSpec 𝒜 s hs hi).inv ≫ (basicOpen 𝒜 s).ι)).1
  simp only [Category.assoc, basicOpenIsoSpec_inv_ι]
  change eSrc.hom ≫
      Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map f s)) ≫
        awayι 𝒜 s hs hi =
    (map f hf ∣_ basicOpen 𝒜 s) ≫
      (basicOpenIsoSpec 𝒜 s hs hi).hom ≫ awayι 𝒜 s hs hi
  rw [← awayι_comp_map f hf hi s hs]
  simp only [eSrc, Iso.trans_hom, awayι, Category.assoc, Iso.hom_inv_id_assoc]
  rw [morphismRestrict_ι]
  rw [Scheme.isoOfEq_hom_ι_assoc]

/-- A map on `Proj` is finite when all its standard degree-zero localization maps are finite. -/
theorem map_isFinite_of_away_finite
    (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤
      HomogeneousIdeal.map f (HomogeneousIdeal.irrelevant 𝒜))
    (hfin : ∀ (i : PNat) (s : 𝒜 i),
      RingHom.Finite (HomogeneousLocalization.Away.map f s)) :
    IsFinite (map f hf) := by
  let P : MorphismProperty Scheme.{u} := @IsFinite
  let _ : HasAffineProperty P (affineAnd RingHom.Finite) := by
    refine (HasAffineProperty.affineAnd_iff P RingHom.finite_respectsIso
      RingHom.finite_localizationPreserves.away RingHom.finite_ofLocalizationSpan).2 ?_
    intro X Y g
    dsimp only [P]
    exact isFinite_iff g
  let _ : IsZariskiLocalAtTarget P :=
    HasAffineProperty.instIsZariskiLocalAtTarget
  change P (map f hf)
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := P)
    (fun s : Σ i : PNat, 𝒜 i ↦ basicOpen 𝒜 s.2)
  · apply iSup_basicOpen_eq_top 𝒜
    classical
    intro z hz
    rw [← DirectSum.sum_support_decompose 𝒜 z]
    refine Ideal.sum_mem _ fun c hc ↦ if hc0 : c = 0 then ?_ else
      Ideal.subset_span ⟨⟨⟨c, Nat.pos_iff_ne_zero.mpr hc0⟩, _⟩, rfl⟩
    convert! Ideal.zero_mem _
    subst hc0
    exact hz
  · intro s
    apply (MorphismProperty.arrow_mk_iso_iff P
      (mapRestrictArrowIso f hf s.1.2 s.2 s.2.2)).mpr
    change IsFinite (Spec.map
      (CommRingCat.ofHom (HomogeneousLocalization.Away.map f (s.2 : A))))
    exact (IsFinite.SpecMap_iff _).mpr (hfin s.1 s.2)

/-- The projective morphism attached to degree-one generators is finite as soon as
all its standard affine-chart ring maps are finite. -/
theorem projectiveAeval_isFinite_of_away_finite
    {K C I : Type u} [CommRing K] [CommRing C] [Algebra K C]
    (𝒞 : ℕ → Submodule K C) [GradedRing 𝒞]
    (g : I → C) (hg : ∀ i, g i ∈ 𝒞 1)
    (hspan : (HomogeneousIdeal.irrelevant 𝒞).toIdeal ≤ Ideal.span (Set.range g))
    (hfin : ∀ (i : PNat) (s : MvPolynomial.homogeneousSubmodule I K i),
      RingHom.Finite (HomogeneousLocalization.Away.map
        (MvPolynomial.standardGradedAevalHom 𝒞 g hg) s)) :
    IsFinite (projectiveAeval 𝒞 g hg hspan) := by
  let f := MvPolynomial.standardGradedAevalHom 𝒞 g hg
  let hf := MvPolynomial.irrelevant_le_map_of_span_range 𝒞 f g
    (MvPolynomial.standardGradedAevalHom_apply_X 𝒞 g hg) hspan
  exact map_isFinite_of_away_finite f hf hfin

end AlgebraicGeometry.Proj
