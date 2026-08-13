import Mathlib.RingTheory.Artinian.Module
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

noncomputable section

universe u v w

variable (K A : Type u) [Field K] [IsAlgClosed K]
variable [CommRing A] [Algebra K A] [Module.Finite K A] [IsReduced A]

namespace IsArtinianRing

/-- A finite-dimensional reduced commutative algebra over an algebraically closed field is a
finite product of copies of the base field, indexed by its maximal ideals. -/
noncomputable def reducedFiniteAlgEquivPi :
    A ≃ₐ[K] (MaximalSpectrum A → K) := by
  letI : IsArtinianRing A := IsArtinianRing.of_finite K A
  let e₁ : A ≃ₐ[K] (∀ I : MaximalSpectrum A, A ⧸ I.asIdeal) :=
    (equivPi A).restrictScalars K
  let e₂ : (∀ I : MaximalSpectrum A, A ⧸ I.asIdeal) ≃ₐ[K]
      (MaximalSpectrum A → K) :=
    AlgEquiv.piCongrRight fun I ↦
      (AlgEquiv.ofBijective (Algebra.ofId K (A ⧸ I.asIdeal))
        IsAlgClosed.algebraMap_bijective_of_isIntegral).symm
  exact e₁.trans e₂

/-- The length of a reduced finite scheme over an algebraically closed field equals its number
of geometric points. -/
theorem card_maximalSpectrum_eq_finrank :
    Nat.card (MaximalSpectrum A) = Module.finrank K A := by
  let _ : IsArtinianRing A := IsArtinianRing.of_finite K A
  let _ : Fintype (MaximalSpectrum A) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  rw [(reducedFiniteAlgEquivPi K A).toLinearEquiv.finrank_eq]
  simp

/-- Equivalently, a reduced finite-dimensional algebra over an algebraically closed field has
exactly `finrank` prime-spectrum points. -/
theorem card_primeSpectrum_eq_finrank :
    Nat.card (PrimeSpectrum A) = Module.finrank K A := by
  let _ : IsArtinianRing A := IsArtinianRing.of_finite K A
  rw [Nat.card_congr (primeSpectrumEquivMaximalSpectrum (R := A))]
  exact card_maximalSpectrum_eq_finrank K A

end IsArtinianRing

namespace Ideal

variable {R S : Type u} [CommRing R] [CommRing S] [IsDomain R] [Algebra R S]
variable [Module.Finite R S] [Module.Flat R S]

/-- A reduced fiber of a finite flat algebra over an algebraically closed residue field has
as many geometric points as the rank of the finite algebra. -/
theorem natCard_primeSpectrum_fiber_eq_finrank
    (p : Ideal R) [p.IsPrime] [IsAlgClosed p.ResidueField]
    [IsReduced (p.Fiber S)] :
    Nat.card (PrimeSpectrum (p.Fiber S)) = Module.finrank R S := by
  rw [IsArtinianRing.card_primeSpectrum_eq_finrank p.ResidueField (p.Fiber S)]
  exact p.finrank_fiber_eq_finrank

/-- In particular, rank `c + 2` gives reduced fibers consisting of exactly `c + 2`
geometric points. -/
theorem natCard_primeSpectrum_fiber_eq_add_two
    (p : Ideal R) [p.IsPrime] [IsAlgClosed p.ResidueField]
    [IsReduced (p.Fiber S)] {c : ℕ} (hrank : Module.finrank R S = c + 2) :
    Nat.card (PrimeSpectrum (p.Fiber S)) = c + 2 :=
  (natCard_primeSpectrum_fiber_eq_finrank p).trans hrank

end Ideal

namespace Algebra

open Module

variable {F : Type u} {E : Type v} [Field F] [CommRing E] [Algebra F E]

/-- A finite-dimensional commutative algebra over a field is reduced whenever its trace
pairing is nondegenerate. -/
theorem isReduced_of_traceForm_nondegenerate
    (htrace : (traceForm F E).Nondegenerate) : IsReduced E := by
  constructor
  intro x hx
  apply htrace.1 x
  intro y
  rw [traceForm_apply]
  exact (isNilpotent_trace_of_isNilpotent
    ((Commute.all x y).isNilpotent_mul_right hx)).eq_zero

/-- A nonzero trace discriminant is therefore a concrete certificate that a finite
commutative algebra over a field is reduced. -/
theorem isReduced_of_det_traceForm_ne_zero
    {ι : Type w} [Fintype ι] [DecidableEq ι] (b : Basis ι F E)
    (hdet : ((traceForm F E).toMatrix b).det ≠ 0) : IsReduced E :=
  isReduced_of_traceForm_nondegenerate <|
    LinearMap.BilinForm.nondegenerate_of_det_ne_zero (traceForm F E) b hdet

end Algebra

namespace MaximalSpectrum

variable {F : Type u} {F' : Type v} {A : Type w}
variable [Field F] [Field F'] [Algebra F F'] [IsAlgClosed F']
variable [CommRing A] [Algebra F A] [Module.Finite F A]

/-- If an algebraic closure of `F` has degree two, every closed point of a finite
`F`-algebra has residue degree one or two. Over `ℝ`, these are the real points and the
nonreal conjugate pairs. -/
theorem finrank_quotient_eq_one_or_two
    (hclosure : Module.finrank F F' = 2) (p : MaximalSpectrum A) :
    Module.finrank F (A ⧸ p.asIdeal) = 1 ∨
      Module.finrank F (A ⧸ p.asIdeal) = 2 := by
  let _ : IsArtinianRing A := IsArtinianRing.of_finite F A
  let _ : Field (A ⧸ p.asIdeal) :=
    IsArtinianRing.fieldOfSubtypeIsMaximal (R := A) p
  rcases IsAlgClosed.nonempty_algEquiv_or_of_finrank_eq_two
      (F := F) (F' := F') (A ⧸ p.asIdeal) hclosure with h | h
  · obtain ⟨e⟩ := h
    left
    exact e.toLinearEquiv.finrank_eq.trans (Module.finrank_self F)
  · obtain ⟨e⟩ := h
    right
    exact e.toLinearEquiv.finrank_eq.trans hclosure

end MaximalSpectrum

/-- Closed points whose residue field is quadratic over the base field. Over `ℝ`, each such
point represents one nonreal complex-conjugate pair. -/
abbrev QuadraticClosedPoint (F : Type u) (A : Type v)
    [Field F] [CommRing A] [Algebra F A] :=
  {p : MaximalSpectrum A // Module.finrank F (A ⧸ p.asIdeal) = 2}

/-- Closed points whose residue field has degree one over the base field.  Over `ℝ` these are
exactly the real/rational closed points. -/
abbrev RationalClosedPoint (F : Type u) (A : Type v)
    [Field F] [CommRing A] [Algebra F A] :=
  {p : MaximalSpectrum A // Module.finrank F (A ⧸ p.asIdeal) = 1}

namespace QuadraticClosedPoint

variable {F : Type u} {F' : Type v} {A : Type w}
variable [Field F] [Field F'] [Algebra F F'] [IsAlgClosed F']
variable [CommRing A] [Algebra F A] [Module.Finite F A]

/-- A quadratic closed point really has residue field isomorphic to the chosen quadratic
algebraic closure. For `F = ℝ` and `F' = ℂ`, this identifies it with one conjugate pair. -/
theorem nonempty_residueAlgEquiv_algebraicClosure
    (hclosure : Module.finrank F F' = 2) (p : QuadraticClosedPoint F A) :
    Nonempty ((A ⧸ p.1.asIdeal) ≃ₐ[F] F') := by
  let _ : IsArtinianRing A := IsArtinianRing.of_finite F A
  let _ : Field (A ⧸ p.1.asIdeal) :=
    IsArtinianRing.fieldOfSubtypeIsMaximal (R := A) p.1
  rcases IsAlgClosed.nonempty_algEquiv_or_of_finrank_eq_two
      (F := F) (F' := F') (A ⧸ p.1.asIdeal) hclosure with h | h
  · obtain ⟨e⟩ := h
    have he : Module.finrank F (A ⧸ p.1.asIdeal) = 1 := by
      exact e.toLinearEquiv.finrank_eq.trans (Module.finrank_self F)
    omega
  · exact h

/-- Real quadratic closed points have complex residue field. -/
theorem nonempty_residueAlgEquiv_complex
    {A : Type u} [CommRing A] [Algebra ℝ A] [Module.Finite ℝ A]
    (p : QuadraticClosedPoint ℝ A) :
    Nonempty ((A ⧸ p.1.asIdeal) ≃ₐ[ℝ] ℂ) :=
  nonempty_residueAlgEquiv_algebraicClosure Complex.finrank_real_complex p

end QuadraticClosedPoint

namespace MaximalSpectrum

variable {F : Type u} {F' : Type v} {A : Type w}
variable [Field F] [Field F'] [Algebra F F'] [IsAlgClosed F']
variable [CommRing A] [Algebra F A] [Module.Finite F A]

/-- Over a field with quadratic algebraic closure, every closed point is uniquely either
rational or quadratic. -/
noncomputable def equivRationalClosedPointSumQuadraticClosedPoint
    (hclosure : Module.finrank F F' = 2) :
    MaximalSpectrum A ≃ RationalClosedPoint F A ⊕ QuadraticClosedPoint F A := by
  let ecomp :
      {p : MaximalSpectrum A // ¬ Module.finrank F (A ⧸ p.asIdeal) = 1} ≃
        QuadraticClosedPoint F A :=
  {
    toFun p := ⟨p.1, (finrank_quotient_eq_one_or_two hclosure p.1).resolve_left p.2⟩
    invFun p := ⟨p.1, by omega⟩
    left_inv p := by ext; rfl
    right_inv p := by ext; rfl
  }
  exact (Equiv.sumCompl
    (fun p : MaximalSpectrum A ↦ Module.finrank F (A ⧸ p.asIdeal) = 1)).symm.trans
      (Equiv.sumCongr (Equiv.refl _) ecomp)

/-- The closed points are partitioned into rational points and quadratic points. -/
theorem natCard_eq_natCard_rationalClosedPoint_add_quadraticClosedPoint
    (hclosure : Module.finrank F F' = 2) :
    Nat.card (MaximalSpectrum A) =
      Nat.card (RationalClosedPoint F A) + Nat.card (QuadraticClosedPoint F A) := by
  let _ : IsArtinianRing A := IsArtinianRing.of_finite F A
  let _ : Finite (RationalClosedPoint F A) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  let _ : Finite (QuadraticClosedPoint F A) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  rw [Nat.card_congr (equivRationalClosedPointSumQuadraticClosedPoint hclosure)]
  exact Nat.card_sum

end MaximalSpectrum

namespace IsArtinianRing

variable {F : Type u} {F' : Type v} {A : Type w}
variable [Field F] [Field F'] [Algebra F F'] [IsAlgClosed F']
variable [CommRing A] [Algebra F A] [Module.Finite F A] [IsReduced A]

/-- For a reduced finite algebra over a field with quadratic algebraic closure, its vector-space
dimension is the number of closed points plus the number of quadratic closed points. Thus a real
point contributes one and a nonreal conjugate pair contributes two. -/
theorem finrank_eq_natCard_add_natCard_quadraticClosedPoint
    (hclosure : Module.finrank F F' = 2) :
    Module.finrank F A =
      Nat.card (MaximalSpectrum A) + Nat.card (QuadraticClosedPoint F A) := by
  classical
  let _ : IsArtinianRing A := IsArtinianRing.of_finite F A
  let _ : Fintype (MaximalSpectrum A) := Fintype.ofFinite _
  let _ : Fintype (QuadraticClosedPoint F A) := Fintype.ofFinite _
  have hsum : Module.finrank F A =
      ∑ p : MaximalSpectrum A, Module.finrank F (A ⧸ p.asIdeal) := by
    rw [((equivPi A).restrictScalars F).toLinearEquiv.finrank_eq]
    exact Module.finrank_pi_fintype F
  rw [hsum, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  calc
    (∑ p : MaximalSpectrum A, Module.finrank F (A ⧸ p.asIdeal)) =
        ∑ p : MaximalSpectrum A,
          (1 + if Module.finrank F (A ⧸ p.asIdeal) = 2 then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro p _
      obtain hp | hp := MaximalSpectrum.finrank_quotient_eq_one_or_two hclosure p
      · simp [hp]
      · simp [hp]
    _ = Fintype.card (MaximalSpectrum A) +
        Fintype.card (QuadraticClosedPoint F A) := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.sum_ite]
      simp only [Nat.mul_one, Nat.mul_zero, Nat.add_zero]
      exact congrArg (Fintype.card (MaximalSpectrum A) + ·) <|
        (Fintype.card_subtype
          (fun p : MaximalSpectrum A ↦ Module.finrank F (A ⧸ p.asIdeal) = 2)).symm

/-- Real specialization: the length of a reduced finite real algebra is the number of real
closed points plus the number of nonreal conjugate pairs. -/
theorem real_finrank_eq_natCard_add_natCard_quadraticClosedPoint
    {A : Type u} [CommRing A] [Algebra ℝ A] [Module.Finite ℝ A] [IsReduced A] :
    Module.finrank ℝ A =
      Nat.card (MaximalSpectrum A) + Nat.card (QuadraticClosedPoint ℝ A) :=
  finrank_eq_natCard_add_natCard_quadraticClosedPoint
    (F := ℝ) (F' := ℂ) (A := A) Complex.finrank_real_complex

/-- If a reduced real fiber of length `c + 2` contains at most one quadratic closed point,
then it is either fully real with `c + 2` closed points, or it has one conjugate pair and
`c + 1` real-scheme closed points. -/
theorem real_reduced_fiber_count_dichotomy
    {A : Type u} [CommRing A] [Algebra ℝ A] [Module.Finite ℝ A] [IsReduced A]
    {c : ℕ} (hrank : Module.finrank ℝ A = c + 2)
    (hpairs : Nat.card (QuadraticClosedPoint ℝ A) ≤ 1) :
    (Nat.card (QuadraticClosedPoint ℝ A) = 0 ∧
        Nat.card (MaximalSpectrum A) = c + 2) ∨
      (Nat.card (QuadraticClosedPoint ℝ A) = 1 ∧
        Nat.card (MaximalSpectrum A) = c + 1) := by
  have hlength := real_finrank_eq_natCard_add_natCard_quadraticClosedPoint (A := A)
  omega

/-- Geometric real-point formulation of the preceding dichotomy: a reduced real fiber of
length `c + 2` with at most one quadratic closed point has either `c + 2` real points, or `c`
real points and one nonreal conjugate pair. -/
theorem real_reduced_fiber_rational_point_dichotomy
    {A : Type u} [CommRing A] [Algebra ℝ A] [Module.Finite ℝ A] [IsReduced A]
    {c : ℕ} (hrank : Module.finrank ℝ A = c + 2)
    (hpairs : Nat.card (QuadraticClosedPoint ℝ A) ≤ 1) :
    (Nat.card (QuadraticClosedPoint ℝ A) = 0 ∧
        Nat.card (RationalClosedPoint ℝ A) = c + 2) ∨
      (Nat.card (QuadraticClosedPoint ℝ A) = 1 ∧
        Nat.card (RationalClosedPoint ℝ A) = c) := by
  have hclosed := MaximalSpectrum.natCard_eq_natCard_rationalClosedPoint_add_quadraticClosedPoint
    (F := ℝ) (F' := ℂ) (A := A) Complex.finrank_real_complex
  rcases real_reduced_fiber_count_dichotomy hrank hpairs with h | h
  · left
    omega
  · right
    omega

/-- A nonzero trace discriminant supplies the reducedness hypothesis in the preceding real-fiber
dichotomy. -/
theorem real_fiber_count_dichotomy_of_det_traceForm_ne_zero
    {A : Type u} [CommRing A] [Algebra ℝ A] [Module.Finite ℝ A]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ A)
    (hdet : ((Algebra.traceForm ℝ A).toMatrix b).det ≠ 0)
    {c : ℕ} (hrank : Module.finrank ℝ A = c + 2)
    (hpairs : Nat.card (QuadraticClosedPoint ℝ A) ≤ 1) :
    (Nat.card (QuadraticClosedPoint ℝ A) = 0 ∧
        Nat.card (MaximalSpectrum A) = c + 2) ∨
      (Nat.card (QuadraticClosedPoint ℝ A) = 1 ∧
        Nat.card (MaximalSpectrum A) = c + 1) := by
  let _ : IsReduced A := Algebra.isReduced_of_det_traceForm_ne_zero b hdet
  exact real_reduced_fiber_count_dichotomy hrank hpairs

end IsArtinianRing
