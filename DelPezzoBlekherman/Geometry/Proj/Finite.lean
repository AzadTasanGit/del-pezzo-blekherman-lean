import DelPezzoBlekherman.Geometry.Proj.RadicalMap
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

open HomogeneousLocalization

namespace HomogeneousLocalization.Away

universe u

variable {A B σ τ : Type u}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
variable {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

lemma map_mk_mul_mk_of_degree_one
    (f : 𝒜 →+*ᵍ ℬ) {s : A} (hs : s ∈ 𝒜 1)
    {n d : ℕ} (hd : d ≤ n) {a : A} (ha : a ∈ 𝒜 (n - d))
    {v : B} (hv : v ∈ ℬ d) :
    Away.map f s (Away.mk 𝒜 hs (n - d) a (by simpa using ha)) *
      Away.mk ℬ (f.2 hs) d v (by simpa using hv) =
        Away.mk ℬ (f.2 hs) n (f a * v) (by
          simpa [Nat.sub_add_cancel hd] using SetLike.mul_mem_graded (f.2 ha) hv) := by
  rw [HomogeneousLocalization.ext_iff_val]
  simp only [map_mk, val_mul, val_mk]
  rw [Localization.mk_mul]
  congr 1
  ext
  simp [← pow_add, Nat.sub_add_cancel hd]

lemma mk_sum {J : Type*} [Fintype J]
    {s : A} {q : ℕ} (hs : s ∈ 𝒜 q) (n : ℕ)
    (x : J → A) (hx : ∀ j, x j ∈ 𝒜 (n • q)) :
    Away.mk 𝒜 hs n (∑ j, x j) (sum_mem fun j _ ↦ hx j) =
      ∑ j, Away.mk 𝒜 hs n (x j) (hx j) := by
  rw [HomogeneousLocalization.ext_iff_val]
  change Localization.mk (∑ j, x j) _ = algebraMap _ _ (∑ j, Away.mk 𝒜 hs n (x j) (hx j))
  rw [map_sum]
  simp only [algebraMap_apply, val_mk]
  simpa using Localization.mk_sum x Finset.univ
    (⟨s ^ n, by use n⟩ : Submonoid.powers s)

/-- A finite homogeneous family spans a graded target over a graded source when every
homogeneous element has a degree-compatible expression in that family. -/
def HomogeneouslySpans (f : 𝒜 →+*ᵍ ℬ) {J : Type*} [Fintype J]
    (d : J → ℕ) (v : J → B) : Prop :=
  (∀ j, v j ∈ ℬ (d j)) ∧
    ∀ (n : ℕ) (b : B), b ∈ ℬ n →
      ∃ a : {j : J // d j ≤ n} → A,
        (∀ j, a j ∈ 𝒜 (n - d j.1)) ∧
          b = ∑ j, f (a j) * v j.1

/-- Degree-compatible finite homogeneous module generators remain module generators after
passing to degree-zero localization at a degree-one element. -/
theorem map_finite_of_homogeneouslySpans
    (f : 𝒜 →+*ᵍ ℬ) {J : Type*} [Fintype J]
    (d : J → ℕ) (v : J → B) (hgen : HomogeneouslySpans f d v)
    {s : A} (hs : s ∈ 𝒜 1) : RingHom.Finite (Away.map f s) := by
  dsimp only [HomogeneouslySpans] at hgen
  obtain ⟨hv, hspan⟩ := hgen
  let φ := Away.map f s
  let z : J → Away ℬ (f s) := fun j ↦
    Away.mk ℬ (f.2 hs) (d j) (v j) (by simpa using hv j)
  let _ : Algebra (Away 𝒜 s) (Away ℬ (f s)) := φ.toAlgebra
  rw [RingHom.Finite, Module.finite_def]
  suffices hz : Submodule.span (Away 𝒜 s) (Set.range z) = ⊤ by
    rw [← hz]
    exact Submodule.fg_span (Set.finite_range z)
  rw [eq_top_iff]
  intro x _
  obtain ⟨n, b, hb, rfl⟩ := Away.mk_surjective ℬ (f.2 hs) x
  have hb' : b ∈ ℬ n := by simpa using hb
  obtain ⟨a, ha, rfl⟩ := hspan n b hb'
  let c : {j : J // d j ≤ n} → Away 𝒜 s := fun j ↦
    Away.mk 𝒜 hs (n - d j.1) (a j) (by simpa using ha j)
  have hterm (j : {j : J // d j ≤ n}) :
      c j • z j.1 = Away.mk ℬ (f.2 hs) n (f (a j) * v j.1) (by
        simpa [Nat.sub_add_cancel j.2] using
          SetLike.mul_mem_graded (f.2 (ha j)) (hv j.1)) := by
    change φ (c j) * z j.1 = _
    exact map_mk_mul_mk_of_degree_one f hs j.2 (ha j) (hv j.1)
  have hsum :
      Away.mk ℬ (f.2 hs) n (∑ j, f (a j) * v j.1) (by
        exact sum_mem fun j _ ↦ by
          simpa [Nat.sub_add_cancel j.2] using
            SetLike.mul_mem_graded (f.2 (ha j)) (hv j.1)) =
        ∑ j, c j • z j.1 := by
    rw [mk_sum (x := fun j : {j : J // d j ≤ n} ↦ f (a j) * v j.1)
      (hx := fun j ↦ by
        simpa [Nat.sub_add_cancel j.2] using
          SetLike.mul_mem_graded (f.2 (ha j)) (hv j.1))]
    exact Finset.sum_congr rfl fun j _ ↦ (hterm j).symm
  rw [hsum]
  exact Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _ <| by
    apply Submodule.subset_span
    exact Set.mem_range_self j.1

/-- Ordinary finite module generation by homogeneous elements automatically gives the
degree-compatible expressions used by `HomogeneouslySpans`. -/
theorem homogeneouslySpans_of_span_eq_top
    (f : 𝒜 →+*ᵍ ℬ) {J : Type*} [Fintype J]
    (d : J → ℕ) (v : J → B) (hv : ∀ j, v j ∈ ℬ (d j))
    (htop : letI := f.toRingHom.toAlgebra
      Submodule.span A (Set.range v) = ⊤) : HomogeneouslySpans f d v := by
  refine ⟨hv, ?_⟩
  intro n b hb
  let _ : Algebra A B := f.toRingHom.toAlgebra
  have hmem : b ∈ Submodule.span A (Set.range v) := by
    rw [htop]
    trivial
  obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp hmem
  have hr' : ∑ j, f.toRingHom (r j) * v j = b := by
    change ∑ j, algebraMap A B (r j) * v j = b
    simpa only [Algebra.smul_def] using hr
  let a : {j : J // d j ≤ n} → A := fun j ↦
    (DirectSum.decompose 𝒜 (r j.1) (n - d j.1) : A)
  refine ⟨a, fun j ↦ (DirectSum.decompose 𝒜 (r j.1) (n - d j.1)).2, ?_⟩
  calc
    b = (DirectSum.decompose ℬ b n : B) :=
      (DirectSum.decompose_of_mem_same ℬ hb).symm
    _ = (DirectSum.decompose ℬ (∑ j, f.toRingHom (r j) * v j) n : B) := by rw [hr']
    _ = ∑ j : J, (DirectSum.decompose ℬ (f.toRingHom (r j) * v j) n : B) := by simp
    _ = ∑ j : J, if h : d j ≤ n then f.toRingHom (a ⟨j, h⟩) * v j else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      split_ifs with h
      · rw [DirectSum.coe_decompose_mul_of_right_mem_of_le ℬ (hv j) h]
        exact congrArg (fun x : B ↦ x * v j) <|
          (f.map_directSumDecompose 𝒜 ℬ).symm
      · exact DirectSum.coe_decompose_mul_of_right_mem_of_not_le ℬ (hv j) h
    _ = ∑ j : {j : J // d j ≤ n}, f.toRingHom (a j) * v j.1 := by
      simp only [a]
      change (∑ x ∈ Finset.univ, if d x ≤ n then
          f.toRingHom (DirectSum.decompose 𝒜 (r x) (n - d x) : A) * v x else 0) = _
      rw [← Finset.sum_filter]
      simpa using
        (Finset.sum_subtype_eq_sum_filter
          (s := Finset.univ)
          (p := fun j ↦ d j ≤ n)
          (f := fun j ↦ f.toRingHom
            (DirectSum.decompose 𝒜 (r j) (n - d j) : A) * v j)).symm

/-- A graded ring map whose target is generated, as a module, by finitely many homogeneous
elements induces a finite degree-zero localization map on every degree-one chart. -/
theorem map_finite_of_span_eq_top
    (f : 𝒜 →+*ᵍ ℬ) {J : Type*} [Fintype J]
    (d : J → ℕ) (v : J → B) (hv : ∀ j, v j ∈ ℬ (d j))
    (htop : letI := f.toRingHom.toAlgebra
      Submodule.span A (Set.range v) = ⊤)
    {s : A} (hs : s ∈ 𝒜 1) : RingHom.Finite (Away.map f s) :=
  map_finite_of_homogeneouslySpans f d v
    (homogeneouslySpans_of_span_eq_top f d v hv htop) hs

/-- Finiteness of the underlying graded ring homomorphism implies finiteness of every
degree-zero localization map at a degree-one element. The proof replaces arbitrary finite
module generators by their finitely many homogeneous components. -/
theorem map_finite_of_toRingHom_finite
    (f : 𝒜 →+*ᵍ ℬ) (hfinite : f.toRingHom.Finite)
    {s : A} (hs : s ∈ 𝒜 1) : RingHom.Finite (Away.map f s) := by
  classical
  let _ : Algebra A B := f.toRingHom.toAlgebra
  let _ : Module.Finite A B := hfinite
  obtain ⟨N, b, hb⟩ := Module.Finite.exists_fin (R := A) (M := B)
  let J := Σ i : Fin N, (DirectSum.decompose ℬ (b i)).support
  let d : J → ℕ := fun j ↦ j.2.1
  let v : J → B := fun j ↦ (DirectSum.decompose ℬ (b j.1) j.2.1 : B)
  have hv : ∀ j, v j ∈ ℬ (d j) := fun j ↦ (DirectSum.decompose ℬ (b j.1) j.2.1).2
  have hspan : Submodule.span A (Set.range v) = ⊤ := by
    rw [eq_top_iff, ← hb, Submodule.span_le]
    rintro x ⟨i, rfl⟩
    rw [← DirectSum.sum_support_decompose ℬ (b i)]
    exact Submodule.sum_mem _ fun n hn ↦ Submodule.subset_span <|
      ⟨⟨i, ⟨n, hn⟩⟩, rfl⟩
  exact map_finite_of_span_eq_top f d v hv hspan hs

end HomogeneousLocalization.Away

namespace AlgebraicGeometry.Proj

open CategoryTheory HomogeneousLocalization

universe u

variable {A B σ τ : Type u}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
variable {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- It suffices to check finiteness of a radical-condition projective morphism on any
degree-one family whose standard opens cover the target `Proj`. -/
theorem mapOfRadical_isFinite_of_degreeOne_cover
    (f : 𝒜 →+*ᵍ ℬ)
    (hf : (HomogeneousIdeal.irrelevant ℬ).toIdeal ≤
      (HomogeneousIdeal.map f (HomogeneousIdeal.irrelevant 𝒜)).toIdeal.radical)
    {J : Type*} (s : J → A) (hs : ∀ j, s j ∈ 𝒜 1)
    (hcover : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ Ideal.span (Set.range s))
    (hfin : ∀ j, RingHom.Finite (Away.map f (s j))) :
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
    (fun j ↦ basicOpen 𝒜 (s j))
  · exact iSup_basicOpen_eq_top 𝒜 s hcover
  · intro j
    apply (MorphismProperty.arrow_mk_iso_iff P
      (mapOfRadicalRestrictArrowIso f hf Nat.zero_lt_one (s j) (hs j))).mpr
    change IsFinite (Spec.map (CommRingCat.ofHom (Away.map f (s j))))
    exact (IsFinite.SpecMap_iff _).mpr (hfin j)

end AlgebraicGeometry.Proj

namespace MvPolynomial

universe uK uI

variable {K : Type uK} {I : Type uI} [CommRing K]

attribute [local instance] gradedAlgebra

/-- For the standard grading, the irrelevant ideal is contained in the ideal generated by
the polynomial variables. -/
theorem irrelevant_toIdeal_le_span_range_X :
    (HomogeneousIdeal.irrelevant (homogeneousSubmodule I K)).toIdeal ≤
      Ideal.span (Set.range (X : I → MvPolynomial I K)) := by
  intro p hp
  have hp0 : homogeneousComponent 0 p = 0 := by
    have h := (HomogeneousIdeal.mem_irrelevant_iff _ p).mp hp
    rw [GradedRing.proj_apply] at h
    exact (decomposition.decompose'_apply p 0).symm.trans h
  have hcoeff : coeff 0 p = 0 := by
    simpa using congrArg (coeff 0) hp0
  rw [show Set.range (X : I → MvPolynomial I K) = X '' Set.univ by simp,
    mem_ideal_span_X_image]
  intro m hm
  have hm0 : m ≠ 0 := by
    intro hmzero
    subst m
    exact (mem_support_iff.mp hm) hcoeff
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hm0
  exact ⟨i, Set.mem_univ i, hi⟩

/-- A degreewise finite standard-graded coordinate ring is finite over the polynomial ring
generated by any basepoint-free degree-one family.

Here standard grading is used in its operational form: every degree-`n` homogeneous element
belongs to the `n`th power of the irrelevant ideal.  Basepoint-freeness then puts a fixed power
of that ideal inside the parameter ideal.  Bases of the finitely many lower homogeneous pieces
generate the entire coordinate ring, by induction on degree.  Thus the statement constructs
module finiteness; it does not accept `RingHom.Finite` or a module basis as input. -/
theorem standardGradedAevalHom_toRingHom_finite_of_basepointFree
    {K C I : Type u} [Field K] [CommRing C] [Algebra K C] [Finite I]
    (𝒞 : ℕ → Submodule K C) [GradedRing 𝒞]
    (g : I → C) (hg : ∀ i, g i ∈ 𝒞 1)
    (hbasepointFree : (HomogeneousIdeal.irrelevant 𝒞).toIdeal ≤
      (Ideal.span (Set.range g)).radical)
    (hirrelevantFG : (HomogeneousIdeal.irrelevant 𝒞).toIdeal.FG)
    (hcomponentFinite : ∀ n, Module.Finite K (𝒞 n))
    (hstandard : ∀ n (x : C), x ∈ 𝒞 n →
      x ∈ (HomogeneousIdeal.irrelevant 𝒞).toIdeal ^ n) :
    (standardGradedAevalHom 𝒞 g hg).toRingHom.Finite := by
  classical
  letI : Fintype I := Fintype.ofFinite I
  let f := standardGradedAevalHom 𝒞 g hg
  let _ : Algebra (MvPolynomial I K) C := f.toRingHom.toAlgebra
  letI componentFinite (n : ℕ) : Module.Finite K (𝒞 n) := hcomponentFinite n
  let J := (HomogeneousIdeal.irrelevant 𝒞).toIdeal
  let Q := Ideal.span (Set.range g)
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg
    hbasepointFree hirrelevantFG
  let q := N + 1
  have hqpos : 0 < q := by simp [q]
  have hq : J ^ q ≤ Q := by
    exact (Ideal.pow_le_pow_right (show N ≤ q by simp [q])).trans hN
  let E := Σ d : Fin q, Fin (Module.finrank K (𝒞 d.1))
  let v : E → C := fun e ↦ (Module.finBasis K (𝒞 e.1.1) e.2 : 𝒞 e.1.1)
  rw [RingHom.Finite, Module.finite_def]
  suffices hspan : Submodule.span (MvPolynomial I K) (Set.range v) = ⊤ by
    rw [← hspan]
    exact Submodule.fg_span (Set.finite_range v)
  let S := Submodule.span (MvPolynomial I K) (Set.range v)
  have hhomogeneous : ∀ n (x : C), x ∈ 𝒞 n → x ∈ S := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hx
      by_cases hn : n < q
      · let b := Module.finBasis K (𝒞 n)
        have hxspan : (⟨x, hx⟩ : 𝒞 n) ∈ Submodule.span K (Set.range b) := by
          rw [b.span_eq]
          trivial
        obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hxspan
        have haC : ∑ i, algebraMap K C (a i) * (b i : C) = x := by
          simpa only [Algebra.smul_def, Submodule.coe_sum, Submodule.coe_smul,
            Submodule.coe_mk] using congrArg Subtype.val ha
        rw [← haC]
        apply Submodule.sum_mem
        intro i hi
        have hbmem : (b i : C) ∈ S := by
          apply Submodule.subset_span
          exact ⟨⟨⟨n, hn⟩, i⟩, rfl⟩
        have hsmul := S.smul_mem (MvPolynomial.C (a i)) hbmem
        change algebraMap (MvPolynomial I K) C (MvPolynomial.C (a i)) * (b i : C) ∈ S at hsmul
        have hC : algebraMap (MvPolynomial I K) C (MvPolynomial.C (a i)) =
            algebraMap K C (a i) := by
          change f.toRingHom (MvPolynomial.C (a i)) = algebraMap K C (a i)
          change eval₂Hom (algebraMap K C) g (MvPolynomial.C (a i)) = _
          simp
        rw [hC] at hsmul
        simpa only using hsmul
      · have hnq : q ≤ n := Nat.le_of_not_gt hn
        have hnpos : 1 ≤ n := hqpos.trans_le hnq
        have hxQ : x ∈ Q := hq ((Ideal.pow_le_pow_right hnq) (hstandard n x hx))
        obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun C).mp hxQ
        have haC : ∑ i, a i * g i = x := by
          simpa [Algebra.smul_def] using ha
        have hxdecomp : x = ∑ i, (DirectSum.decompose 𝒞 (a i) (n - 1) : C) * g i := by
          calc
            x = (DirectSum.decompose 𝒞 x n : C) :=
              (DirectSum.decompose_of_mem_same 𝒞 hx).symm
            _ = (DirectSum.decompose 𝒞 (∑ i, a i * g i) n : C) := by rw [haC]
            _ = ∑ i, (DirectSum.decompose 𝒞 (a i * g i) n : C) := by simp
            _ = ∑ i, (DirectSum.decompose 𝒞 (a i) (n - 1) : C) * g i := by
              apply Finset.sum_congr rfl
              intro i hi
              exact DirectSum.coe_decompose_mul_of_right_mem_of_le 𝒞 (hg i) hnpos
        rw [hxdecomp]
        apply Submodule.sum_mem
        intro i hi
        have hcoeff : (DirectSum.decompose 𝒞 (a i) (n - 1) : C) ∈ S :=
          ih (n - 1) (Nat.sub_lt hnpos Nat.zero_lt_one)
            _ (DirectSum.decompose 𝒞 (a i) (n - 1)).2
        have hsmul := S.smul_mem (X i) hcoeff
        change algebraMap (MvPolynomial I K) C (X i) *
          (DirectSum.decompose 𝒞 (a i) (n - 1) : C) ∈ S at hsmul
        have hX : algebraMap (MvPolynomial I K) C (X i) = g i := by
          change f.toRingHom (X i) = g i
          exact standardGradedAevalHom_apply_X 𝒞 g hg i
        rw [hX] at hsmul
        simpa only [mul_comm] using hsmul
  change S = ⊤
  rw [_root_.eq_top_iff]
  intro x hx
  rw [← DirectSum.sum_support_decompose 𝒞 x]
  exact Submodule.sum_mem S fun n hn ↦
    hhomogeneous n _ (DirectSum.decompose 𝒞 x n).2

end MvPolynomial

namespace AlgebraicGeometry.Proj

open HomogeneousLocalization

universe u


attribute [local instance] MvPolynomial.gradedAlgebra

/-- A basepoint-free degree-one family defines a finite projective morphism as soon as the
target graded coordinate ring is generated by finitely many homogeneous elements as a module
over the corresponding polynomial ring. -/
theorem projectiveAevalOfRadical_isFinite_of_homogeneous_module_generators
    {K C I J : Type u} [CommRing K] [CommRing C] [Algebra K C] [Fintype J]
    (𝒞 : ℕ → Submodule K C) [GradedRing 𝒞]
    (g : I → C) (hg : ∀ i, g i ∈ 𝒞 1)
    (hbasepointFree : (HomogeneousIdeal.irrelevant 𝒞).toIdeal ≤
      (Ideal.span (Set.range g)).radical)
    (d : J → ℕ) (v : J → C) (hv : ∀ j, v j ∈ 𝒞 (d j))
    (hmodule : let f := MvPolynomial.standardGradedAevalHom 𝒞 g hg
      letI := f.toRingHom.toAlgebra
      Submodule.span (MvPolynomial I K) (Set.range v) = ⊤) :
    IsFinite (projectiveAevalOfRadical 𝒞 g hg hbasepointFree) := by
  let f := MvPolynomial.standardGradedAevalHom 𝒞 g hg
  let hf := MvPolynomial.irrelevant_le_radical_map_of_le_radical_span_range 𝒞 f g
    (MvPolynomial.standardGradedAevalHom_apply_X 𝒞 g hg) hbasepointFree
  change IsFinite (mapOfRadical f hf)
  apply mapOfRadical_isFinite_of_degreeOne_cover f hf MvPolynomial.X
    (fun i ↦ MvPolynomial.isHomogeneous_X (R := K) i)
    MvPolynomial.irrelevant_toIdeal_le_span_range_X
  intro i
  exact HomogeneousLocalization.Away.map_finite_of_span_eq_top f d v hv hmodule
    (MvPolynomial.isHomogeneous_X (R := K) i)

/-- A basepoint-free degree-one evaluation map is a finite projective morphism whenever the
resulting map from the polynomial ring to the graded coordinate ring is finite. -/
theorem projectiveAevalOfRadical_isFinite_of_toRingHom_finite
    {K C I : Type u} [CommRing K] [CommRing C] [Algebra K C]
    (𝒞 : ℕ → Submodule K C) [GradedRing 𝒞]
    (g : I → C) (hg : ∀ i, g i ∈ 𝒞 1)
    (hbasepointFree : (HomogeneousIdeal.irrelevant 𝒞).toIdeal ≤
      (Ideal.span (Set.range g)).radical)
    (hfinite : (MvPolynomial.standardGradedAevalHom 𝒞 g hg).toRingHom.Finite) :
    IsFinite (projectiveAevalOfRadical 𝒞 g hg hbasepointFree) := by
  let f := MvPolynomial.standardGradedAevalHom 𝒞 g hg
  let hf := MvPolynomial.irrelevant_le_radical_map_of_le_radical_span_range 𝒞 f g
    (MvPolynomial.standardGradedAevalHom_apply_X 𝒞 g hg) hbasepointFree
  change IsFinite (mapOfRadical f hf)
  apply mapOfRadical_isFinite_of_degreeOne_cover f hf MvPolynomial.X
    (fun i ↦ MvPolynomial.isHomogeneous_X (R := K) i)
    MvPolynomial.irrelevant_toIdeal_le_span_range_X
  intro i
  exact HomogeneousLocalization.Away.map_finite_of_toRingHom_finite f hfinite
    (MvPolynomial.isHomogeneous_X (R := K) i)

/-- Certificate-free finite-Proj endpoint for a finite-type standard-graded coordinate ring.
The hypotheses are degreewise finite homogeneous pieces, finite generation of the irrelevant
ideal, and the defining degree-power property of a standard grading. -/
theorem projectiveAevalOfRadical_isFinite_of_standardGraded_basepointFree
    {K C I : Type u} [Field K] [CommRing C] [Algebra K C] [Finite I]
    (𝒞 : ℕ → Submodule K C) [GradedRing 𝒞]
    (g : I → C) (hg : ∀ i, g i ∈ 𝒞 1)
    (hbasepointFree : (HomogeneousIdeal.irrelevant 𝒞).toIdeal ≤
      (Ideal.span (Set.range g)).radical)
    (hirrelevantFG : (HomogeneousIdeal.irrelevant 𝒞).toIdeal.FG)
    (hcomponentFinite : ∀ n, Module.Finite K (𝒞 n))
    (hstandard : ∀ n (x : C), x ∈ 𝒞 n →
      x ∈ (HomogeneousIdeal.irrelevant 𝒞).toIdeal ^ n) :
    IsFinite (projectiveAevalOfRadical 𝒞 g hg hbasepointFree) := by
  apply projectiveAevalOfRadical_isFinite_of_toRingHom_finite 𝒞 g hg hbasepointFree
  exact MvPolynomial.standardGradedAevalHom_toRingHom_finite_of_basepointFree
    𝒞 g hg hbasepointFree hirrelevantFG hcomponentFinite hstandard

/-- A free-module basis of cardinality `c + 2` simultaneously certifies finiteness of the
basepoint-free projective evaluation morphism and its algebraic rank `c + 2`. This is the direct
interface expected from the Hilbert numerator `1 + c t + t²`. -/
theorem projectiveAevalOfRadical_isFinite_and_finrank_eq_add_two_of_basis
    {K C I : Type u} [Field K] [CommRing C] [Algebra K C]
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
       Module.finrank (MvPolynomial I K) C = c + 2) := by
  let f := MvPolynomial.standardGradedAevalHom 𝒞 g hg
  let _ : Algebra (MvPolynomial I K) C := f.toRingHom.toAlgebra
  let _ : Module.Free (MvPolynomial I K) C := Module.Free.of_basis b
  let _ : Module.Finite (MvPolynomial I K) C := Module.Finite.of_basis b
  constructor
  · apply projectiveAevalOfRadical_isFinite_of_toRingHom_finite 𝒞 g hg hbasepointFree
    exact (RingHom.finite_algebraMap.mpr inferInstance : f.toRingHom.Finite)
  · simpa using Module.finrank_eq_card_basis b

end AlgebraicGeometry.Proj
