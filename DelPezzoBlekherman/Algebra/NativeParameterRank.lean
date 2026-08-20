/-
Copyright (c) 2026 Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import DelPezzoBlekherman.Algebra.NativeGorenstein
import DelPezzoBlekherman.Geometry.Proj.GradedEvaluation
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.Regular.Free
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Generic rank from the native parameter reduction

This file identifies the generic rank of a coordinate ring over its polynomial parameter
subring with the dimension of the actual parameter quotient. Combined with the native
Hilbert-series calculation in NativeGorenstein, this gives rank c + 2 without a global
module basis or an HVectorOneCOneFreeCertificate.

The strongest endpoint derives freeness after localization at the parameter-space origin from
the actual regular parameter sequence. Global flatness and explicitly supplied local freeness
remain only as convenient wrappers, not assumptions of the native rank theorem.
-/

noncomputable section

open PowerSeries
open TensorProduct

namespace DelPezzoBlekherman

universe u v

variable {K : Type u} {C : Type v}

/-- A finitely presented module over a local ring is free if a regular sequence on it generates
the maximal ideal.  The proof lifts freeness backwards through one regular element at a time;
at the end of the sequence the base is a field. -/
theorem Module.free_of_isRegular_of_span_eq_maximalIdeal
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.FinitePresentation R M]
    {rs : List R} (hregular : RingTheory.Sequence.IsRegular M rs)
    (hspan : Ideal.ofList rs = IsLocalRing.maximalIdeal R) :
    Module.Free R M := by
  apply hregular.recIterModByRegularWithRing
    (motive := fun R _ M _ _ rs _ ↦
      ∀ [IsLocalRing R] [Module.FinitePresentation R M],
        Ideal.ofList rs = IsLocalRing.maximalIdeal R → Module.Free R M)
  · intro R _ M _ _ _ _ _ hspan
    have hfield : IsField R :=
      IsLocalRing.isField_iff_maximalIdeal_eq.mpr (by simpa using hspan.symm)
    letI : Field R := hfield.toField
    exact Module.Free.of_divisionRing R M
  · intro R _ M _ _ r rs hreg htail ih _ _ hspan
    letI : Nontrivial (QuotSMulTop r M) :=
      (Submodule.nontrivial_iff (R ⧸ Ideal.span {r})).mp <|
        nontrivial_iff.mpr ⟨⊤, Ideal.ofList
          (rs.map (Ideal.Quotient.mk (Ideal.span {r}))) • ⊤, htail.top_ne_smul⟩
    letI : Nontrivial (R ⧸ Ideal.span {r}) :=
      Module.nontrivial (R ⧸ Ideal.span {r}) (QuotSMulTop r M)
    letI : IsLocalRing (R ⧸ Ideal.span {r}) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    letI : Module.FinitePresentation (R ⧸ Ideal.span {r})
        ((R ⧸ Ideal.span {r}) ⊗[R] M) := inferInstance
    letI : Module.FinitePresentation (R ⧸ Ideal.span {r}) (QuotSMulTop r M) :=
      Module.FinitePresentation.of_equiv
        ((QuotSMulTop.equivQuotTensor r M).extendScalarsOfSurjective
          Ideal.Quotient.mk_surjective).symm
    apply (Module.free_quotSMulTop_iff_free R M ?_ hreg).mp
    · apply ih
      rw [← Ideal.map_ofList]
      rw [← IsLocalRing.map_maximalIdeal_of_surjective
        (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective]
      rw [← hspan]
      rw [Ideal.ofList_cons, Ideal.map_sup]
      have hr : Ideal.map (Ideal.Quotient.mk (Ideal.span {r}))
          (Ideal.span {r}) = ⊥ := by
        rw [Ideal.map_eq_bot_iff_le_ker]
        exact Ideal.span_le.mpr (by simp)
      rw [hr, Ideal.map_ofList]
      simp
    · rw [Ideal.jacobson_bot, IsLocalRing.ringJacobson_eq_maximalIdeal]
      rw [← hspan]
      exact Ideal.subset_span (by simp)
  exact hspan

/-- A finite module has the same generic rank as its fiber dimension at a prime whenever it is
free at that prime.  Unlike `Ideal.finrank_fiber_eq_finrank`, this only asks for freeness at the
one stalk being used, rather than global flatness. -/
theorem finrank_fiber_eq_finrank_of_free_atPrime
    {R : Type u} {M : Type v} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (p : Ideal R) [p.IsPrime]
    (hfree : Module.Free (Localization.AtPrime p)
      (LocalizedModule.AtPrime p M)) :
    Module.finrank p.ResidueField (p.Fiber M) = Module.finrank R M := by
  let F := FractionRing R
  let Rp := Localization.AtPrime p
  let Mp := LocalizedModule.AtPrime p M
  letI : Module.Free Rp Mp := hfree
  let k := p.ResidueField
  letI : Module.Free Rp (Rp ⊗[R] M) :=
    Module.Free.of_equiv (LocalizedModule.equivTensorProduct p.primeCompl M)
  let e : k ⊗[Rp] (Rp ⊗[R] M) ≃ₗ[k] k ⊗[R] M :=
    AlgebraTensorModule.cancelBaseChange R Rp k k M
  have hfiberStalk : Module.finrank k (p.Fiber M) = Module.finrank Rp Mp := by
    rw [← e.finrank_eq, Module.finrank_baseChange,
      ← (LocalizedModule.equivTensorProduct p.primeCompl M).finrank_eq]
  have hgeneric : Module.finrank F (F ⊗[R] M) = Module.finrank R M := by
    rw [IsLocalization.finrank_eq F (nonZeroDivisors R) le_rfl]
    exact IsLocalizedModule.finrank_eq (nonZeroDivisors R)
      (TensorProduct.mk R F M 1) le_rfl
  calc
    Module.finrank p.ResidueField (p.Fiber M) = Module.finrank Rp Mp := hfiberStalk
    _ = Module.finrank F (F ⊗[Rp] Mp) := Module.finrank_baseChange.symm
    _ = Module.finrank F (F ⊗[Rp] (Rp ⊗[R] M)) :=
      ((LocalizedModule.equivTensorProduct p.primeCompl M).baseChange Rp F Mp _).finrank_eq
    _ = Module.finrank F (F ⊗[R] M) :=
      (AlgebraTensorModule.cancelBaseChange R Rp F F M).finrank_eq
    _ = Module.finrank R M := hgeneric

/-- The kernel of polynomial evaluation at the origin is the irrelevant ideal. -/
theorem ker_constantCoeff_eq_idealOfVars
    {I : Type*} [Field K] :
    RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial I K →+* K) =
      MvPolynomial.idealOfVars I K := by
  ext p
  rw [RingHom.mem_ker]
  rw [← pow_one (MvPolynomial.idealOfVars I K)]
  rw [MvPolynomial.mem_pow_idealOfVars_iff']
  simp only [Nat.lt_one_iff, MvPolynomial.constantCoeff_eq]
  constructor
  · intro hp x hx
    rwa [(Finsupp.degree_eq_zero_iff x).mp hx]
  · intro hp
    exact hp 0 rfl

/-- Over a field, the ideal generated by all variables is the maximal ideal of the origin. -/
instance instIsPrimeIdealOfVars
    {I : Type*} [Field K] : (MvPolynomial.idealOfVars I K).IsPrime := by
  rw [← ker_constantCoeff_eq_idealOfVars]
  apply Ideal.IsMaximal.isPrime
  apply RingHom.ker_isMaximal_of_surjective
  intro x
  exact ⟨MvPolynomial.C x, by simp⟩

/-- The graded evaluation homomorphism determined by degree-one parameters. -/
def degreeOneParameterAevalHom
    [Field K] [CommRing C] [Algebra K C]
    (𝒞 : ℕ → Submodule K C) [SetLike.GradedMonoid 𝒞]
    {n : ℕ} (parameters : Fin n → 𝒞 1) :=
  MvPolynomial.standardGradedAevalHom 𝒞
    (fun i ↦ (parameters i : C)) (fun i ↦ (parameters i).2)

/-- The irrelevant ideal maps to the ideal generated by the chosen parameters. -/
theorem map_idealOfVars_degreeOneParameterAevalHom
    [Field K] [CommRing C] [Algebra K C]
    (𝒞 : ℕ → Submodule K C) [SetLike.GradedMonoid 𝒞]
    {n : ℕ} (parameters : Fin n → 𝒞 1) :
    (MvPolynomial.idealOfVars (Fin n) K).map
        (degreeOneParameterAevalHom 𝒞 parameters).toRingHom =
      degreeOneParameterIdeal 𝒞 parameters := by
  unfold MvPolynomial.idealOfVars degreeOneParameterIdeal
  rw [Ideal.map_span]
  congr 1
  ext x
  simp [degreeOneParameterAevalHom,
    MvPolynomial.standardGradedAevalHom_apply_X]

/-- A regular sequence of degree-one parameters makes the coordinate ring free at the origin
of parameter space.  This is the local commutative-algebra bridge needed for the native degree
calculation; it uses no global basis, projectivity, flatness, or Cohen--Macaulay certificate. -/
theorem degreeOneParameter_free_at_origin_of_isRegular
    [Field K] [CommRing C] [Algebra K C]
    (𝒞 : ℕ → Submodule K C) [SetLike.GradedMonoid 𝒞]
    {n : ℕ} (parameters : Fin n → 𝒞 1)
    (hregular : RingTheory.Sequence.IsRegular C
      (List.ofFn fun i ↦ (parameters i : C)))
    (hfinite : let f := degreeOneParameterAevalHom 𝒞 parameters
      letI := f.toRingHom.toAlgebra
      Module.Finite (MvPolynomial (Fin n) K) C) :
    let f := degreeOneParameterAevalHom 𝒞 parameters
    letI := f.toRingHom.toAlgebra
    let p := MvPolynomial.idealOfVars (Fin n) K
    Module.Free (Localization.AtPrime p) (LocalizedModule.AtPrime p C) := by
  classical
  let P := MvPolynomial (Fin n) K
  let f := degreeOneParameterAevalHom 𝒞 parameters
  letI : Algebra P C := f.toRingHom.toAlgebra
  let p := MvPolynomial.idealOfVars (Fin n) K
  let Rp := Localization.AtPrime p
  let Mp := LocalizedModule.AtPrime p C
  let vars : List P := List.ofFn fun i : Fin n ↦ MvPolynomial.X i
  letI : Module.Finite P C := hfinite
  letI : Module.FinitePresentation P C := Module.finitePresentation_of_finite P C
  letI : Module.Finite Rp Mp := inferInstance
  letI : Module.FinitePresentation Rp Mp :=
    Module.finitePresentation_of_finite Rp Mp
  have hparams : vars.map (algebraMap P C) =
      List.ofFn (fun i ↦ (parameters i : C)) := by
    rw [List.map_ofFn]
    congr 1
    funext i
    change f.toRingHom (MvPolynomial.X i) = (parameters i : C)
    simp [f, degreeOneParameterAevalHom,
      MvPolynomial.standardGradedAevalHom_apply_X]
  have hweak : RingTheory.Sequence.IsWeaklyRegular C vars :=
    (RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff C C vars).mp <| by
      rw [hparams]
      exact hregular.toIsWeaklyRegular
  have hspan : Ideal.ofList vars = p := by
    unfold vars p MvPolynomial.idealOfVars Ideal.ofList
    congr 1
    ext x
    simp
  have hmem : ∀ r ∈ vars, r ∈ p := by
    intro r hr
    rw [← hspan]
    exact Ideal.subset_span hr
  rcases subsingleton_or_nontrivial Mp with hMp | hMp
  · letI : Subsingleton Mp := hMp
    exact Module.Free.of_subsingleton Rp Mp
  · letI : Nontrivial Mp := hMp
    have hregularLocal : RingTheory.Sequence.IsRegular Mp
        (vars.map (algebraMap P Rp)) :=
      hweak.isRegular_of_isLocalizedModule_of_mem Rp p
        (LocalizedModule.mkLinearMap p.primeCompl C) hmem
    have hspanLocal : Ideal.ofList (vars.map (algebraMap P Rp)) =
        IsLocalRing.maximalIdeal Rp := by
      rw [← Ideal.map_ofList, hspan,
        IsLocalization.AtPrime.map_eq_maximalIdeal]
    exact Module.free_of_isRegular_of_span_eq_maximalIdeal
      hregularLocal hspanLocal

/-- For a finite coordinate ring that is free at the parameter origin, generic rank equals the
dimension of the actual Artinian parameter reduction. This is basis-free and only uses freeness
at the one stalk whose fiber is the parameter quotient. -/
theorem genericRank_eq_degreeOneParameterIdeal_quotient_of_free_at_origin
    [Field K] [CommRing C] [Algebra K C]
    (𝒞 : ℕ → Submodule K C) [SetLike.GradedMonoid 𝒞]
    {n : ℕ} (parameters : Fin n → 𝒞 1)
    (hfree : let f := degreeOneParameterAevalHom 𝒞 parameters
      letI := f.toRingHom.toAlgebra
      let p := MvPolynomial.idealOfVars (Fin n) K
      Module.Free (Localization.AtPrime p) (LocalizedModule.AtPrime p C))
    (hfinite : let f := degreeOneParameterAevalHom 𝒞 parameters
      letI := f.toRingHom.toAlgebra
      Module.Finite (MvPolynomial (Fin n) K) C) :
    let f := degreeOneParameterAevalHom 𝒞 parameters
    letI := f.toRingHom.toAlgebra
    Module.finrank (MvPolynomial (Fin n) K) C =
      Module.finrank K
        (C ⧸ (degreeOneParameterIdeal 𝒞 parameters).restrictScalars K) := by
  classical
  let P := MvPolynomial (Fin n) K
  let f := degreeOneParameterAevalHom 𝒞 parameters
  letI : Algebra P C := f.toRingHom.toAlgebra
  let p := MvPolynomial.idealOfVars (Fin n) K
  have hconstSurj : Function.Surjective
      (MvPolynomial.constantCoeff : P →+* K) := by
    intro x
    exact ⟨MvPolynomial.C x, by simp⟩
  have hpker : p = RingHom.ker MvPolynomial.constantCoeff := by
    exact ker_constantCoeff_eq_idealOfVars.symm
  letI : p.IsMaximal := hpker.symm ▸
    RingHom.ker_isMaximal_of_surjective _ hconstSurj
  letI : p.IsPrime := inferInstance
  let hQuotIsField : IsField (P ⧸ p) :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient p).mp inferInstance
  letI : Field (P ⧸ p) := hQuotIsField.toField
  letI : Module.Finite P C := hfinite
  letI : Module.Free (Localization.AtPrime p) (LocalizedModule.AtPrime p C) := hfree
  let Q := C ⧸ p.map (algebraMap P C)
  let eBase : (P ⧸ p) ≃+* K :=
    (Ideal.quotEquivOfEq hpker).trans
      (RingHom.quotientKerEquivOfSurjective hconstSurj)
  let eQuot : Q ≃ₐ[P ⧸ p] TensorProduct P (P ⧸ p) C :=
    Algebra.TensorProduct.quotIdealMapEquivQuotTensor C p
  let eCancel : TensorProduct (P ⧸ p) p.ResidueField
      (TensorProduct P (P ⧸ p) C) ≃ₐ[p.ResidueField]
      p.Fiber C :=
    Algebra.TensorProduct.cancelBaseChange P (P ⧸ p) p.ResidueField p.ResidueField C
  have hbaseFinrank : Module.finrank (P ⧸ p) Q = Module.finrank K Q := by
    apply Algebra.finrank_eq_of_equiv_equiv eBase (RingEquiv.refl Q)
    apply RingHom.ext
    intro a
    induction a using Quotient.inductionOn' with
    | _ a =>
      apply Ideal.Quotient.eq.mpr
      have ha : MvPolynomial.C (MvPolynomial.constantCoeff a) - a ∈ p := by
        rw [hpker]
        change MvPolynomial.constantCoeff
          (MvPolynomial.C (MvPolynomial.constantCoeff a) - a) = 0
        simp
      have hmap := Ideal.mem_map_of_mem (algebraMap P C) ha
      have heBase : eBase (Ideal.Quotient.mk p a) =
          MvPolynomial.constantCoeff a := by
        simp [eBase, Ideal.quotEquivOfEq_mk,
          RingHom.quotientKerEquivOfSurjective_apply_mk]
      change algebraMap K C (eBase (Ideal.Quotient.mk p a)) -
          algebraMap P C a ∈ p.map (algebraMap P C)
      rw [heBase]
      have hC : algebraMap P C
          (MvPolynomial.C (MvPolynomial.constantCoeff a)) =
          algebraMap K C (MvPolynomial.constantCoeff a) := by
        change f.toRingHom (MvPolynomial.C (MvPolynomial.constantCoeff a)) = _
        simp [f, degreeOneParameterAevalHom,
          MvPolynomial.standardGradedAevalHom, MvPolynomial.gradedAevalHom,
          MvPolynomial.gradedEval₂Hom]
      rw [← hC]
      simpa using hmap
  have hfiberQuot :
      Module.finrank p.ResidueField (p.Fiber C) = Module.finrank (P ⧸ p) Q := by
    letI : Module.Finite (P ⧸ p) (TensorProduct P (P ⧸ p) C) :=
      Module.Finite.base_change P (P ⧸ p) C
    letI : Module.Free (P ⧸ p) (TensorProduct P (P ⧸ p) C) :=
      Module.Free.of_divisionRing _ _
    rw [← eCancel.toLinearEquiv.finrank_eq, Module.finrank_baseChange,
      ← eQuot.toLinearEquiv.finrank_eq]
  have hmap : p.map (algebraMap P C) = degreeOneParameterIdeal 𝒞 parameters := by
    change (MvPolynomial.idealOfVars (Fin n) K).map f.toRingHom = _
    exact map_idealOfVars_degreeOneParameterAevalHom 𝒞 parameters
  calc
    Module.finrank P C = Module.finrank p.ResidueField (p.Fiber C) :=
      (finrank_fiber_eq_finrank_of_free_atPrime p hfree).symm
    _ = Module.finrank (P ⧸ p) Q := hfiberQuot
    _ = Module.finrank K Q := hbaseFinrank
    _ = Module.finrank K
        (C ⧸ (degreeOneParameterIdeal 𝒞 parameters).restrictScalars K) := by
      change Module.finrank K (C ⧸ p.map (algebraMap P C)) =
        Module.finrank K
          (C ⧸ (degreeOneParameterIdeal 𝒞 parameters).restrictScalars K)
      rw [hmap]
      exact (Submodule.Quotient.restrictScalarsEquiv K
        (degreeOneParameterIdeal 𝒞 parameters : Submodule C C)).finrank_eq.symm

/-- A finite coordinate ring with a regular degree-one parameter sequence has generic rank equal
to the dimension of its actual Artinian parameter reduction.  The local freeness needed by the
fiber calculation is derived internally from the regular sequence. -/
theorem genericRank_eq_degreeOneParameterIdeal_quotient_of_isRegular
    [Field K] [CommRing C] [Algebra K C]
    (𝒞 : ℕ → Submodule K C) [SetLike.GradedMonoid 𝒞]
    {n : ℕ} (parameters : Fin n → 𝒞 1)
    (hregular : RingTheory.Sequence.IsRegular C
      (List.ofFn fun i ↦ (parameters i : C)))
    (hfinite : let f := degreeOneParameterAevalHom 𝒞 parameters
      letI := f.toRingHom.toAlgebra
      Module.Finite (MvPolynomial (Fin n) K) C) :
    let f := degreeOneParameterAevalHom 𝒞 parameters
    letI := f.toRingHom.toAlgebra
    Module.finrank (MvPolynomial (Fin n) K) C =
      Module.finrank K
        (C ⧸ (degreeOneParameterIdeal 𝒞 parameters).restrictScalars K) := by
  exact genericRank_eq_degreeOneParameterIdeal_quotient_of_free_at_origin
    𝒞 parameters
      (degreeOneParameter_free_at_origin_of_isRegular
        𝒞 parameters hregular hfinite)
      hfinite

/-- The flat version of the origin-fiber theorem. Flatness is used only to make the single
localized module at the parameter origin free. -/
theorem genericRank_eq_degreeOneParameterIdeal_quotient_of_flat
    [Field K] [CommRing C] [Algebra K C]
    (𝒞 : ℕ → Submodule K C) [SetLike.GradedMonoid 𝒞]
    {n : ℕ} (parameters : Fin n → 𝒞 1)
    (hflat : let f := degreeOneParameterAevalHom 𝒞 parameters
      letI := f.toRingHom.toAlgebra
      Module.Flat (MvPolynomial (Fin n) K) C)
    (hfinite : let f := degreeOneParameterAevalHom 𝒞 parameters
      letI := f.toRingHom.toAlgebra
      Module.Finite (MvPolynomial (Fin n) K) C) :
    let f := degreeOneParameterAevalHom 𝒞 parameters
    letI := f.toRingHom.toAlgebra
    Module.finrank (MvPolynomial (Fin n) K) C =
      Module.finrank K
        (C ⧸ (degreeOneParameterIdeal 𝒞 parameters).restrictScalars K) := by
  let P := MvPolynomial (Fin n) K
  let f := degreeOneParameterAevalHom 𝒞 parameters
  letI : Algebra P C := f.toRingHom.toAlgebra
  let p := MvPolynomial.idealOfVars (Fin n) K
  letI : Module.Flat P C := hflat
  letI : Module.Finite P C := hfinite
  letI : Module.Flat (Localization.AtPrime p) (LocalizedModule.AtPrime p C) :=
    Module.Flat.localizedModule p.primeCompl
  have hfree : Module.Free (Localization.AtPrime p) (LocalizedModule.AtPrime p C) :=
    Module.free_of_flat_of_isLocalRing
  exact genericRank_eq_degreeOneParameterIdeal_quotient_of_free_at_origin
    𝒞 parameters hfree hfinite

/-- Native rank `c + 2` from freeness at the parameter origin, regularity, degreewise finiteness,
and the literal Hilbert-series formula. -/
theorem genericRank_eq_add_two_of_free_at_origin
    [Field K] [CommRing C] [Algebra K C]
    (𝒞 : ℕ → Submodule K C) [GradedRing 𝒞]
    {m c : ℕ} (parameters : Fin (m + 1) → 𝒞 1)
    (hregular : RingTheory.Sequence.IsRegular C
      (List.ofFn fun i ↦ (parameters i : C)))
    (hcomponentFinite : ∀ d, Module.Finite K (𝒞 d))
    (hHilbert : ∀ d,
      (Module.finrank K (𝒞 d) : ℤ) = coeff d (delPezzoHilbertSeries m c))
    (hfree : let f := degreeOneParameterAevalHom 𝒞 parameters
      letI := f.toRingHom.toAlgebra
      let p := MvPolynomial.idealOfVars (Fin (m + 1)) K
      Module.Free (Localization.AtPrime p) (LocalizedModule.AtPrime p C))
    (hfinite : let f := degreeOneParameterAevalHom 𝒞 parameters
      letI := f.toRingHom.toAlgebra
      Module.Finite (MvPolynomial (Fin (m + 1)) K) C) :
    let f := degreeOneParameterAevalHom 𝒞 parameters
    letI := f.toRingHom.toAlgebra
    Module.finrank (MvPolynomial (Fin (m + 1)) K) C = c + 2 := by
  let f := degreeOneParameterAevalHom 𝒞 parameters
  letI := f.toRingHom.toAlgebra
  change Module.finrank (MvPolynomial (Fin (m + 1)) K) C = c + 2
  rw [genericRank_eq_degreeOneParameterIdeal_quotient_of_free_at_origin
    𝒞 parameters hfree hfinite]
  exact degreeOneParameterIdeal_quotient_finrank
    𝒞 parameters hregular hcomponentFinite hHilbert

/-- Native rank `c + 2` from a regular degree-one parameter sequence, degreewise finiteness,
the literal Hilbert-series formula, and module finiteness over the parameter polynomial ring.
Local freeness is proved internally; no chosen basis, flatness assumption, or project-specific
algebra certificate appears in the statement. -/
theorem genericRank_eq_add_two
    [Field K] [CommRing C] [Algebra K C]
    (𝒞 : ℕ → Submodule K C) [GradedRing 𝒞]
    {m c : ℕ} (parameters : Fin (m + 1) → 𝒞 1)
    (hregular : RingTheory.Sequence.IsRegular C
      (List.ofFn fun i ↦ (parameters i : C)))
    (hcomponentFinite : ∀ d, Module.Finite K (𝒞 d))
    (hHilbert : ∀ d,
      (Module.finrank K (𝒞 d) : ℤ) = coeff d (delPezzoHilbertSeries m c))
    (hfinite : let f := degreeOneParameterAevalHom 𝒞 parameters
      letI := f.toRingHom.toAlgebra
      Module.Finite (MvPolynomial (Fin (m + 1)) K) C) :
    let f := degreeOneParameterAevalHom 𝒞 parameters
    letI := f.toRingHom.toAlgebra
    Module.finrank (MvPolynomial (Fin (m + 1)) K) C = c + 2 := by
  let f := degreeOneParameterAevalHom 𝒞 parameters
  letI := f.toRingHom.toAlgebra
  change Module.finrank (MvPolynomial (Fin (m + 1)) K) C = c + 2
  rw [genericRank_eq_degreeOneParameterIdeal_quotient_of_isRegular
    𝒞 parameters hregular hfinite]
  exact degreeOneParameterIdeal_quotient_finrank
    𝒞 parameters hregular hcomponentFinite hHilbert

/-- Native rank c + 2 over the parameter polynomial ring. The rank follows from flatness,
regularity, degreewise finiteness, and the literal Hilbert-series formula; no chosen module basis
or project-specific Hilbert-vector certificate appears in the statement. -/
theorem genericRank_eq_add_two_of_flat
    [Field K] [CommRing C] [Algebra K C]
    (𝒞 : ℕ → Submodule K C) [GradedRing 𝒞]
    {m c : ℕ} (parameters : Fin (m + 1) → 𝒞 1)
    (hregular : RingTheory.Sequence.IsRegular C
      (List.ofFn fun i ↦ (parameters i : C)))
    (hcomponentFinite : ∀ d, Module.Finite K (𝒞 d))
    (hHilbert : ∀ d,
      (Module.finrank K (𝒞 d) : ℤ) = coeff d (delPezzoHilbertSeries m c))
    (hflat : let f := degreeOneParameterAevalHom 𝒞 parameters
      letI := f.toRingHom.toAlgebra
      Module.Flat (MvPolynomial (Fin (m + 1)) K) C)
    (hfinite : let f := degreeOneParameterAevalHom 𝒞 parameters
      letI := f.toRingHom.toAlgebra
      Module.Finite (MvPolynomial (Fin (m + 1)) K) C) :
    let f := degreeOneParameterAevalHom 𝒞 parameters
    letI := f.toRingHom.toAlgebra
    Module.finrank (MvPolynomial (Fin (m + 1)) K) C = c + 2 := by
  let f := degreeOneParameterAevalHom 𝒞 parameters
  letI := f.toRingHom.toAlgebra
  change Module.finrank (MvPolynomial (Fin (m + 1)) K) C = c + 2
  rw [genericRank_eq_degreeOneParameterIdeal_quotient_of_flat
    𝒞 parameters hflat hfinite]
  exact degreeOneParameterIdeal_quotient_finrank
    𝒞 parameters hregular hcomponentFinite hHilbert

end DelPezzoBlekherman
