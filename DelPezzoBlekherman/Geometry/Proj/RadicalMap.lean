import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import DelPezzoBlekherman.Geometry.Proj.GradedEvaluation

universe u

open HomogeneousIdeal HomogeneousLocalization TopologicalSpace CategoryTheory Graded
open AlgebraicGeometry ProjectiveSpectrum Proj

namespace AlgebraicGeometry

section universe_polymorphic

variable {A B σ τ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (f : 𝒜 →+*ᵍ ℬ)
  (hf : ℬ₊.toIdeal ≤ (𝒜₊.map f).toIdeal.radical)

namespace ProjectiveSpectrum

/-- Pullback of relevant homogeneous primes under a graded map whose irrelevant
ideal condition holds up to radical. -/
@[simps] def comapFunOfRadical (p : ProjectiveSpectrum ℬ) : ProjectiveSpectrum 𝒜 where
  asHomogeneousIdeal := p.1.comap f
  isPrime := p.2.comap f
  not_irrelevant_le le := p.3 <| toIdeal_le_toIdeal_iff.mp <|
    hf.trans <| p.isPrime.radical_le_iff.mpr <|
      toIdeal_le_toIdeal_iff.mpr <| map_le_of_le_comap f le

/-- The continuous map on projective spectra induced under a radical irrelevant-ideal condition. -/
def comapOfRadical : C(ProjectiveSpectrum ℬ, ProjectiveSpectrum 𝒜) where
  toFun := comapFunOfRadical f hf
  continuous_toFun := by
    simp_rw [continuous_iff_isClosed, isClosed_iff_zeroLocus, exists_imp,
      forall_eq_apply_imp_iff]
    exact fun s ↦ ⟨f '' s, by ext; simp [comapFunOfRadical]⟩

end ProjectiveSpectrum

namespace Proj

open StructureSheaf

variable (U : Opens (ProjectiveSpectrum 𝒜)) (V : Opens (ProjectiveSpectrum ℬ))
  (hUV : V.1 ⊆ ProjectiveSpectrum.comapOfRadical f hf ⁻¹' U.1)

/-- Pull sections back pointwise under the radical form of the projective-spectrum map. -/
noncomputable def comapStructureSheafFunOfRadical
    (s : ∀ x : U, AtPrime 𝒜 x.1.1.1) (y : V) : AtPrime ℬ y.1.1.1 :=
  localRingHom f _ y.1.1.1 rfl <|
    s ⟨ProjectiveSpectrum.comapOfRadical f hf y.1, hUV y.2⟩

set_option backward.isDefEq.respectTransparency false in
lemma isLocallyFraction_comapStructureSheafFunOfRadical
    (s : ∀ x : U, AtPrime 𝒜 x.1.1.1) (hs : (isLocallyFraction 𝒜).pred s) :
    (isLocallyFraction ℬ).pred (comapStructureSheafFunOfRadical f hf U V hUV s) := by
  rintro ⟨p, hpV⟩
  rcases hs ⟨ProjectiveSpectrum.comapOfRadical f hf p, hUV hpV⟩ with
    ⟨W, m, iWU, i, a, b, hb, h_frac⟩
  refine ⟨W.comap (ProjectiveSpectrum.comapOfRadical f hf) ⊓ V, ⟨m, hpV⟩,
    Opens.infLERight _ _, i, f.gradedAddHom i a, f.gradedAddHom i b,
    fun ⟨q, ⟨hqW, hqV⟩⟩ ↦ hb ⟨_, hqW⟩, fun ⟨q, ⟨hqW, hqV⟩⟩ ↦ ?_⟩
  ext
  specialize h_frac ⟨_, hqW⟩
  simp_all [comapStructureSheafFunOfRadical]

set_option backward.isDefEq.respectTransparency false in
/-- The structure-sheaf pullback under the radical form of the projective-spectrum map. -/
noncomputable def comapStructureSheafOfRadical :
    (Proj.structureSheaf 𝒜).1.obj (.op U) →+* (Proj.structureSheaf ℬ).1.obj (.op V) where
  toFun s := ⟨comapStructureSheafFunOfRadical _ _ _ _ hUV s.1,
    isLocallyFraction_comapStructureSheafFunOfRadical _ _ _ _ hUV _ s.2⟩
  map_one' := by ext; simp [comapStructureSheafFunOfRadical]
  map_zero' := by ext; simp [comapStructureSheafFunOfRadical]
  map_add' x y := by ext; simp [comapStructureSheafFunOfRadical]
  map_mul' x y := by ext; simp [comapStructureSheafFunOfRadical]

end Proj

end universe_polymorphic

section universe_monomorphic

namespace Proj

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (f : 𝒜 →+*ᵍ ℬ)
  (hf : ℬ₊.toIdeal ≤ (𝒜₊.map f).toIdeal.radical)

set_option backward.isDefEq.respectTransparency.types false in
/-- The sheafed-space map induced by a graded map satisfying the irrelevant condition up to
radical. -/
@[simps! (isSimp := false)] noncomputable def sheafedSpaceMapOfRadical :
    Proj.toSheafedSpace ℬ ⟶ Proj.toSheafedSpace 𝒜 where
  hom :=
    { base := TopCat.ofHom <| ProjectiveSpectrum.comapOfRadical f hf
      c := { app U := CommRingCat.ofHom <|
        comapStructureSheafOfRadical f hf _ _ Set.Subset.rfl } }

set_option backward.isDefEq.respectTransparency.types false in
lemma germ_map_sectionInBasicOpen_ofRadical {p : ProjectiveSpectrum ℬ}
    (c : NumDenSameDeg 𝒜
      (ProjectiveSpectrum.comapOfRadical f hf p).1.toIdeal.primeCompl) :
    (toSheafedSpace ℬ).presheaf.germ
      ((Opens.map (sheafedSpaceMapOfRadical f hf).hom.base).obj _) p
      (mem_basicOpen_den _ _ _)
      ((sheafedSpaceMapOfRadical f hf).hom.c.app _ (sectionInBasicOpen 𝒜 _ c)) =
    (toSheafedSpace ℬ).presheaf.germ
      (ProjectiveSpectrum.basicOpen _ (f c.den)) p c.4
      (sectionInBasicOpen ℬ p (c.map _ le_rfl)) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[elementwise] theorem localRingHom_comp_stalkIso_ofRadical (p : ProjectiveSpectrum ℬ) :
    (stalkIso 𝒜 (ProjectiveSpectrum.comapOfRadical f hf p)).hom ≫
      CommRingCat.ofHom (localRingHom f _ _ rfl) ≫
        (stalkIso ℬ p).inv =
      (sheafedSpaceMapOfRadical f hf).hom.stalkMap p := by
  rw [← Iso.eq_inv_comp, Iso.comp_inv_eq]
  ext : 1
  simp only [CommRingCat.hom_ofHom, stalkIso, RingEquiv.toCommRingCatIso_inv,
    RingEquiv.toCommRingCatIso_hom, CommRingCat.hom_comp]
  ext x : 2
  obtain ⟨c, rfl⟩ := x.mk_surjective
  simp only [val_localRingHom, val_mk, RingHom.comp_apply]
  simp only [GradedRingHom.toRingHom_eq_toRingHom, Localization.localRingHom_mk,
    GradedRingHom.coe_toRingHom]
  erw [stalkIso'_symm_mk]
  erw [PresheafedSpace.stalkMap_germ_apply]
  erw [germ_map_sectionInBasicOpen_ofRadical]
  erw [stalkIso'_germ]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Functoriality of `Proj` under the optimal irrelevant-ideal hypothesis up to radical. -/
noncomputable def mapOfRadical : Proj ℬ ⟶ Proj 𝒜 where
  __ := (sheafedSpaceMapOfRadical f hf).hom
  prop p := .mk fun x hx ↦ by
    rw [← localRingHom_comp_stalkIso_ofRadical] at hx
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
      Function.comp_apply] at hx
    have : IsLocalHom (stalkIso ℬ p).inv.hom := isLocalHom_of_isIso _
    replace hx := (isUnit_map_iff _ _).mp hx
    replace hx := IsLocalHom.map_nonunit _ hx
    have : IsLocalHom
        (stalkIso 𝒜 (ProjectiveSpectrum.comapOfRadical f hf p)).hom.hom :=
      isLocalHom_of_isIso _
    exact (isUnit_map_iff _ _).mp hx

/-- The radical construction agrees with mathlib's original `Proj.map` whenever the original
stronger irrelevant-ideal hypothesis is available. -/
theorem mapOfRadical_eq_map
    (hs : ℬ₊ ≤ 𝒜₊.map f)
    (hr : ℬ₊.toIdeal ≤ (𝒜₊.map f).toIdeal.radical) :
    mapOfRadical f hr = map f hs := by
  rfl

@[simp] theorem mapOfRadical_preimage_basicOpen (s : A) :
    mapOfRadical f hf ⁻¹ᵁ basicOpen 𝒜 s = basicOpen ℬ (f s) := rfl

set_option backward.isDefEq.respectTransparency.types false in
theorem ι_comp_mapOfRadical (s : A) :
    (basicOpen ℬ (f s)).ι ≫ mapOfRadical f hf =
      (mapOfRadical f hf).resLE _ _ le_rfl ≫ (basicOpen 𝒜 s).ι := by
  simp

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc] lemma awayToSection_comp_appLE_ofRadical {i : ℕ} {s : A} (hs : s ∈ 𝒜 i) :
    awayToSection 𝒜 s ≫
      Scheme.Hom.appLE (mapOfRadical f hf) (basicOpen 𝒜 s) (basicOpen ℬ (f s)) (by rfl) =
    CommRingCat.ofHom (Away.map f s : Away 𝒜 s →+* Away ℬ (f s)) ≫
      awayToSection ℬ (f s) := by
  ext x
  obtain ⟨n, x, hx, rfl⟩ := x.mk_surjective _ hs
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_ofHom, Away.map_mk]
  refine Subtype.ext <| funext fun p ↦ ?_
  change HomogeneousLocalization.mk _ = .mk _
  ext
  simp

set_option backward.isDefEq.respectTransparency false in
/-- On a standard affine chart, the radical version of `Proj.map` is the spectrum map on
degree-zero localizations. -/
@[reassoc] theorem awayι_comp_mapOfRadical {i : ℕ} (hi : 0 < i) (s : A)
    (hs : s ∈ 𝒜 i) :
    awayι ℬ (f s) (f.2 hs) hi ≫ mapOfRadical f hf =
    Spec.map (CommRingCat.ofHom (Away.map f s)) ≫ awayι 𝒜 s hs hi := by
  rw [awayι, awayι, Category.assoc, ι_comp_mapOfRadical, ← Category.assoc,
    ← Category.assoc]
  congr 1
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  refine ext_to_Spec <| (cancel_mono (basicOpen ℬ (f s)).topIso.hom).mp ?_
  simp [basicOpenIsoSpec_hom, basicOpenToSpec_app_top,
    awayToSection_comp_appLE_ofRadical _ _ hs]

/-- The restriction of `mapOfRadical` to a standard affine chart agrees, as an arrow, with
the spectrum map on degree-zero localizations. -/
noncomputable def mapOfRadicalRestrictArrowIso
    {i : ℕ} (hi : 0 < i) (s : A) (hs : s ∈ 𝒜 i) :
    Arrow.mk (mapOfRadical f hf ∣_ basicOpen 𝒜 s) ≅
      Arrow.mk (Spec.map (CommRingCat.ofHom (Away.map f s))) := by
  let eSrc :=
    Scheme.isoOfEq (Proj ℬ) (mapOfRadical_preimage_basicOpen f hf s) ≪≫
      basicOpenIsoSpec ℬ (f s) (f.2 hs) hi
  refine Arrow.isoMk eSrc (basicOpenIsoSpec 𝒜 s hs hi) ?_
  apply (cancel_mono ((basicOpenIsoSpec 𝒜 s hs hi).inv ≫ (basicOpen 𝒜 s).ι)).1
  simp only [Category.assoc, basicOpenIsoSpec_inv_ι]
  change eSrc.hom ≫ Spec.map (CommRingCat.ofHom (Away.map f s)) ≫ awayι 𝒜 s hs hi =
    (mapOfRadical f hf ∣_ basicOpen 𝒜 s) ≫
      (basicOpenIsoSpec 𝒜 s hs hi).hom ≫ awayι 𝒜 s hs hi
  rw [← awayι_comp_mapOfRadical f hf hi s hs]
  simp only [eSrc, Iso.trans_hom, awayι, Category.assoc, Iso.hom_inv_id_assoc]
  rw [morphismRestrict_ι]
  rw [Scheme.isoOfEq_hom_ι_assoc]

/-- A radical-condition map on `Proj` is finite when all standard degree-zero localization
maps are finite. -/
theorem mapOfRadical_isFinite_of_away_finite
    (hfin : ∀ (i : PNat) (s : 𝒜 i), RingHom.Finite (Away.map f s)) :
    IsFinite (mapOfRadical f hf) := by
  let P : MorphismProperty Scheme.{u} := @IsFinite
  let _ : HasAffineProperty P (affineAnd RingHom.Finite) := by
    refine (HasAffineProperty.affineAnd_iff P RingHom.finite_respectsIso
      RingHom.finite_localizationPreserves.away RingHom.finite_ofLocalizationSpan).2 ?_
    intro X Y g
    dsimp only [P]
    exact isFinite_iff g
  let _ : IsZariskiLocalAtTarget P := HasAffineProperty.instIsZariskiLocalAtTarget
  change P (mapOfRadical f hf)
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
      (mapOfRadicalRestrictArrowIso f hf s.1.2 s.2 s.2.2)).mpr
    change IsFinite (Spec.map (CommRingCat.ofHom (Away.map f (s.2 : A))))
    exact (IsFinite.SpecMap_iff _).mpr (hfin s.1 s.2)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The projective morphism defined by a basepoint-free degree-one family. Here
basepoint-freeness is encoded by the standard radical containment, rather than the stronger
condition that the family itself generate the irrelevant ideal. -/
noncomputable def projectiveAevalOfRadical
    {K C I : Type u} [CommRing K] [CommRing C] [Algebra K C]
    (𝒞 : ℕ → Submodule K C) [GradedRing 𝒞]
    (g : I → C) (hg : ∀ i, g i ∈ 𝒞 1)
    (hspan : (HomogeneousIdeal.irrelevant 𝒞).toIdeal ≤
      (Ideal.span (Set.range g)).radical) :
    Proj 𝒞 ⟶ Proj (MvPolynomial.homogeneousSubmodule I K) :=
  let f := MvPolynomial.standardGradedAevalHom 𝒞 g hg
  mapOfRadical f <|
    MvPolynomial.irrelevant_le_radical_map_of_le_radical_span_range 𝒞 f g
      (MvPolynomial.standardGradedAevalHom_apply_X 𝒞 g hg) hspan

/-- A basepoint-free projective evaluation morphism is finite when its degree-zero maps on
all standard affine charts are finite. -/
theorem projectiveAevalOfRadical_isFinite_of_away_finite
    {K C I : Type u} [CommRing K] [CommRing C] [Algebra K C]
    (𝒞 : ℕ → Submodule K C) [GradedRing 𝒞]
    (g : I → C) (hg : ∀ i, g i ∈ 𝒞 1)
    (hspan : (HomogeneousIdeal.irrelevant 𝒞).toIdeal ≤
      (Ideal.span (Set.range g)).radical)
    (hfin : ∀ (i : PNat) (s : MvPolynomial.homogeneousSubmodule I K i),
      RingHom.Finite (Away.map (MvPolynomial.standardGradedAevalHom 𝒞 g hg) s)) :
    IsFinite (projectiveAevalOfRadical 𝒞 g hg hspan) := by
  let f := MvPolynomial.standardGradedAevalHom 𝒞 g hg
  let hf := MvPolynomial.irrelevant_le_radical_map_of_le_radical_span_range 𝒞 f g
    (MvPolynomial.standardGradedAevalHom_apply_X 𝒞 g hg) hspan
  exact mapOfRadical_isFinite_of_away_finite f hf hfin

end Proj

end universe_monomorphic

end AlgebraicGeometry
