/-
Copyright (c) 2026 Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import DelPezzoBlekherman.Convexity.ClosedConeImage
import DelPezzoBlekherman.Convexity.SumSquaresDual
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Gram-matrix realization of a sums-of-squares cone

This module supplies the finite-dimensional Gram-cone part of Proposition 3.1.
For a square map represented by a continuous linear map on real symmetric Gram
matrices, finite sums of squares are exactly the image of the positive
semidefinite matrix cone.  If no nonzero positive semidefinite Gram matrix maps
to zero, the general closed-cone image theorem proves closedness.
-/

open Set
open scoped MatrixOrder BigOperators

namespace DelPezzoBlekherman

noncomputable section

local instance {m n : Type*} [Fintype m] [Fintype n] :
    NormedAddCommGroup (Matrix m n ℝ) := Matrix.normedAddCommGroup

local instance {m n : Type*} [Fintype m] [Fintype n] :
    NormedSpace ℝ (Matrix m n ℝ) := Matrix.normedSpace

def realGramCone (n : Type*) [Fintype n] : Set (Matrix n n ℝ) :=
  {A | A.PosSemidef}

def rankOneGram {n : Type*} (q : n → ℝ) : Matrix n n ℝ :=
  Matrix.vecMulVec q q

def gramOfFamily {ι n : Type*} [Fintype ι]
    (q : ι → (n → ℝ)) : Matrix n n ℝ :=
  ∑ i, rankOneGram (q i)

theorem rankOneGram_smul
    {n : Type*} (r : ℝ) (q : n → ℝ) :
    rankOneGram (r • q) = r ^ 2 • rankOneGram q := by
  ext i j
  simp [rankOneGram, Matrix.vecMulVec_apply]
  ring

theorem realGramCone_isClosed
    (n : Type*) [Fintype n] :
    IsClosed (realGramCone n) := by
  classical
  rw [show realGramCone n =
      {A | A.IsHermitian} ∩ ⋂ x, {A | 0 ≤ dotProduct (star x) (Matrix.mulVec A x)} by
    ext A
    simp [realGramCone, Matrix.posSemidef_iff_dotProduct_mulVec]]
  apply IsClosed.inter
  · change IsClosed {A : Matrix n n ℝ | star A = A}
    exact isClosed_eq continuous_star continuous_id
  · apply isClosed_iInter
    intro x
    apply isClosed_le continuous_const
    simp only [dotProduct, Matrix.mulVec, star_trivial]
    fun_prop

theorem realGramCone_smul
    {n : Type*} [Fintype n]
    {a : ℝ} (ha : 0 ≤ a) {A : Matrix n n ℝ} (hA : A ∈ realGramCone n) :
    a • A ∈ realGramCone n := by
  exact Matrix.LE.le.posSemidef (smul_nonneg ha hA.nonneg)

theorem rankOneGram_posSemidef
    {n : Type*} [Fintype n] (q : n → ℝ) :
    rankOneGram q ∈ realGramCone n := by
  change (rankOneGram q).PosSemidef
  simpa [rankOneGram] using Matrix.posSemidef_vecMulVec_self_star q

/-- Spectral expansion of a real PSD matrix as rank-one Gram matrices, first
indexed by all eigenvalues. -/
theorem posSemidef_eq_sum_rankOneGram_eigenvectors
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.PosSemidef) :
    A = ∑ k : n, rankOneGram
      (Real.sqrt (hA.isHermitian.eigenvalues k) •
        (hA.isHermitian.eigenvectorBasis k : n → ℝ)) := by
  let U : Matrix n n ℝ := hA.isHermitian.eigenvectorUnitary
  let d : n → ℝ := hA.isHermitian.eigenvalues
  let UD : Matrix n n ℝ := fun i j => U i j * d j
  have hspectral := hA.isHermitian.spectral_theorem
  have hmuldiag : U * Matrix.diagonal d = UD := by
    ext i j
    exact Matrix.mul_diagonal d U i j
  calc
    A = ((Unitary.conjStarAlgAut ℝ (Matrix n n ℝ))
        hA.isHermitian.eigenvectorUnitary)
        (Matrix.diagonal (RCLike.ofReal ∘ hA.isHermitian.eigenvalues)) := hspectral
    _ = _ := by
      rw [Unitary.conjStarAlgAut_apply]
      change U * Matrix.diagonal d * star U = _
      rw [hmuldiag]
      ext i j
      rw [Matrix.mul_apply]
      have hsum_apply :
          ((∑ k : n, rankOneGram
            (Real.sqrt (d k) • (hA.isHermitian.eigenvectorBasis k : n → ℝ))) :
            Matrix n n ℝ) i j =
          ∑ k : n, rankOneGram
            (Real.sqrt (d k) • (hA.isHermitian.eigenvectorBasis k : n → ℝ)) i j := by
        rw [Matrix.sum_apply]
      rw [hsum_apply]
      simp only [Matrix.star_apply, star_trivial, rankOneGram,
        Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
      dsimp [UD, U, d]
      apply Finset.sum_congr rfl
      intro k hk
      calc
        _ = hA.isHermitian.eigenvalues k *
            (hA.isHermitian.eigenvectorBasis k : n → ℝ) i *
            (hA.isHermitian.eigenvectorBasis k : n → ℝ) j := by ring
        _ = (Real.sqrt (hA.isHermitian.eigenvalues k) *
              Real.sqrt (hA.isHermitian.eigenvalues k)) *
            (hA.isHermitian.eigenvectorBasis k : n → ℝ) i *
            (hA.isHermitian.eigenvectorBasis k : n → ℝ) j := by
              rw [Real.mul_self_sqrt (hA.eigenvalues_nonneg k)]
        _ = _ := by ring

/-- Removing the zero-eigenvalue terms gives a rank-one decomposition indexed
by a type whose cardinality is exactly the matrix rank. -/
theorem posSemidef_eq_sum_rankOneGram_nonzero_eigenvectors
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.PosSemidef) :
    A = ∑ k : {i // hA.isHermitian.eigenvalues i ≠ 0}, rankOneGram
      (Real.sqrt (hA.isHermitian.eigenvalues k) •
        (hA.isHermitian.eigenvectorBasis k : n → ℝ)) := by
  let f : n → Matrix n n ℝ := fun k => rankOneGram
    (Real.sqrt (hA.isHermitian.eigenvalues k) •
      (hA.isHermitian.eigenvectorBasis k : n → ℝ))
  calc
    A = ∑ k : n, f k := posSemidef_eq_sum_rankOneGram_eigenvectors A hA
    _ = (Finset.univ.filter
        (fun k => hA.isHermitian.eigenvalues k ≠ 0)).sum f := by
      symm
      apply Finset.sum_subset (by simp)
      intro k hk hkn
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hkn
      simp [hkn, rankOneGram]
    _ = ∑ k : {i // hA.isHermitian.eigenvalues i ≠ 0}, f k := by
      apply Finset.sum_subtype
      intro k
      simp
    _ = _ := rfl

theorem finrank_range_toLin'_eq_card_nonzero_eigenvalues
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.PosSemidef) :
    Module.finrank ℝ (LinearMap.range (Matrix.toLin' A)) =
      Fintype.card {i // hA.isHermitian.eigenvalues i ≠ 0} := by
  calc
    Module.finrank ℝ (LinearMap.range (Matrix.toLin' A)) = A.rank := by
      rw [Matrix.rank_eq_finrank_range_toLin A (Pi.basisFun ℝ n) (Pi.basisFun ℝ n),
        Matrix.toLin_eq_toLin']
    _ = Fintype.card {i // hA.isHermitian.eigenvalues i ≠ 0} :=
      hA.isHermitian.rank_eq_card_non_zero_eigs

/-- A PSD Gram matrix has a rank-one decomposition with exactly as many terms
as its rank. -/
theorem exists_gramFamily_card_eq_finrank_of_posSemidef
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.PosSemidef) :
    ∃ q : {i // hA.isHermitian.eigenvalues i ≠ 0} → (n → ℝ),
      A = gramOfFamily q ∧
      Fintype.card {i // hA.isHermitian.eigenvalues i ≠ 0} =
        Module.finrank ℝ (LinearMap.range (Matrix.toLin' A)) := by
  let q : {i // hA.isHermitian.eigenvalues i ≠ 0} → (n → ℝ) := fun k =>
    Real.sqrt (hA.isHermitian.eigenvalues k) •
      (hA.isHermitian.eigenvectorBasis k : n → ℝ)
  refine ⟨q, ?_, ?_⟩
  · exact posSemidef_eq_sum_rankOneGram_nonzero_eigenvectors A hA
  · exact (finrank_range_toLin'_eq_card_nonzero_eigenvalues A hA).symm

theorem star_mul_self_eq_sum_rankOneGram
    {n : Type*} [Fintype n] (B : Matrix n n ℝ) :
    star B * B = ∑ k : n, rankOneGram (fun i : n => B k i) := by
  classical
  ext i j
  simp only [Matrix.mul_apply, Matrix.star_apply, star_trivial]
  have hsum_apply :
      ((∑ k : n, rankOneGram (fun i : n => B k i)) : Matrix n n ℝ) i j =
        ∑ k : n, rankOneGram (fun i : n => B k i) i j := by
    rw [Matrix.sum_apply]
  rw [hsum_apply]
  simp [rankOneGram, Matrix.vecMulVec_apply]

/-- If all rows of `B` lie in a subspace `K`, the Gram operator `BᴴB` has
range contained in `K`, hence rank at most `dim K`. -/
theorem finrank_range_star_mul_self_le
    {n : Type*} [Fintype n] [DecidableEq n]
    (K : Submodule ℝ (n → ℝ)) (B : Matrix n n ℝ)
    (hrow : ∀ k, (fun i : n => B k i) ∈ K) :
    Module.finrank ℝ (LinearMap.range (Matrix.toLin' (star B * B))) ≤
      Module.finrank ℝ K := by
  apply Submodule.finrank_mono
  rintro y ⟨x, rfl⟩
  rw [Matrix.toLin'_apply, star_mul_self_eq_sum_rankOneGram,
    Matrix.sum_mulVec]
  apply K.sum_mem
  intro k hk
  rw [rankOneGram, Matrix.vecMulVec_mulVec]
  simpa using K.smul_mem ((fun i : n => B k i) ⬝ᵥ x) (hrow k)

theorem gramOfFamily_posSemidef
    {ι n : Type*} [Fintype ι] [Finite n]
    (q : ι → (n → ℝ)) :
    (gramOfFamily q).PosSemidef := by
  let _ := Fintype.ofFinite n
  apply Matrix.LE.le.posSemidef
  unfold gramOfFamily
  apply Finset.sum_nonneg
  intro i hi
  exact (rankOneGram_posSemidef (q i)).nonneg

theorem finrank_range_gramOfFamily_le_finrank_span
    {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
    (q : ι → (n → ℝ)) :
    Module.finrank ℝ (LinearMap.range (Matrix.toLin' (gramOfFamily q))) ≤
      Module.finrank ℝ (Submodule.span ℝ (Set.range q)) := by
  apply Submodule.finrank_mono
  rintro y ⟨x, rfl⟩
  rw [Matrix.toLin'_apply]
  unfold gramOfFamily
  rw [Matrix.sum_mulVec]
  apply Submodule.sum_mem
  intro i hi
  rw [rankOneGram, Matrix.vecMulVec_mulVec]
  simpa using (Submodule.span ℝ (Set.range q)).smul_mem
    ((q i) ⬝ᵥ x) (Submodule.subset_span ⟨i, rfl⟩)

/-- A Gram matrix coming from `r` square summands has rank at most `r`.  This
is one direction of the Gram-rank/SOS-length equivalence used in Theorem 8.3. -/
theorem finrank_range_gramOfFamily_le_card
    {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
    (q : ι → (n → ℝ)) :
    Module.finrank ℝ (LinearMap.range (Matrix.toLin' (gramOfFamily q))) ≤
      Fintype.card ι := by
  calc
    Module.finrank ℝ (LinearMap.range (Matrix.toLin' (gramOfFamily q))) ≤
        Module.finrank ℝ (Submodule.span ℝ (Set.range q)) :=
      finrank_range_gramOfFamily_le_finrank_span q
    _ ≤ Fintype.card ι := finrank_range_le_card q

theorem map_gramOfFamily
    {ι n W : Type*} [Fintype ι]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (sq : (n → ℝ) → W) (T : Matrix n n ℝ →L[ℝ] W)
    (hgram : ∀ q, T (rankOneGram q) = sq q)
    (q : ι → (n → ℝ)) :
    T (gramOfFamily q) = ∑ i, sq (q i) := by
  unfold gramOfFamily
  rw [map_sum]
  simp only [hgram]

/-- Every finite square representation yields a representing PSD Gram matrix
whose rank is no larger than the number of squares. -/
theorem exists_posSemidef_gram_of_squareRepresentation
    {ι n W : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (sq : (n → ℝ) → W) (T : Matrix n n ℝ →L[ℝ] W)
    (hgram : ∀ q, T (rankOneGram q) = sq q)
    (q : ι → (n → ℝ)) {p : W} (hp : p = ∑ i, sq (q i)) :
    ∃ A : Matrix n n ℝ, A.PosSemidef ∧ T A = p ∧
      Module.finrank ℝ (LinearMap.range (Matrix.toLin' A)) ≤ Fintype.card ι := by
  refine ⟨gramOfFamily q, gramOfFamily_posSemidef q, ?_,
    finrank_range_gramOfFamily_le_card q⟩
  rw [map_gramOfFamily sq T hgram q, ← hp]

/-- Conversely, a representing PSD Gram matrix gives a square representation
with exactly `rank A` summands. -/
theorem exists_squareRepresentation_card_eq_finrank_of_posSemidef_gram
    {n W : Type*} [Fintype n] [DecidableEq n]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (sq : (n → ℝ) → W) (T : Matrix n n ℝ →L[ℝ] W)
    (hgram : ∀ q, T (rankOneGram q) = sq q)
    {A : Matrix n n ℝ} (hA : A.PosSemidef) {p : W} (hTA : T A = p) :
    ∃ q : {i // hA.isHermitian.eigenvalues i ≠ 0} → (n → ℝ),
      p = ∑ i, sq (q i) ∧
      Fintype.card {i // hA.isHermitian.eigenvalues i ≠ 0} =
        Module.finrank ℝ (LinearMap.range (Matrix.toLin' A)) := by
  obtain ⟨q, hAq, hcard⟩ :=
    exists_gramFamily_card_eq_finrank_of_posSemidef A hA
  refine ⟨q, ?_, hcard⟩
  calc
    p = T A := hTA.symm
    _ = T (gramOfFamily q) := congrArg T hAq
    _ = ∑ i, sq (q i) := map_gramOfFamily sq T hgram q

/-- A Gram-compatible square map has its finite-sum cone equal to the linear
image of the positive semidefinite matrix cone. -/
theorem finiteSumCone_eq_image_realGramCone
    {n W : Type*} [Fintype n]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (sq : (n → ℝ) → W) (T : Matrix n n ℝ →L[ℝ] W)
    (hgram : ∀ q, T (rankOneGram q) = sq q) :
    finiteSumCone sq = T '' realGramCone n := by
  classical
  ext w
  constructor
  · rintro ⟨qs, rfl⟩
    let A : Matrix n n ℝ := (qs.map rankOneGram).sum
    refine ⟨A, ?_, ?_⟩
    · apply Matrix.LE.le.posSemidef
      dsimp [A]
      apply List.sum_nonneg
      intro M hM
      rw [List.mem_map] at hM
      obtain ⟨q, hq, rfl⟩ := hM
      exact (rankOneGram_posSemidef q).nonneg
    · dsimp [A]
      induction qs with
      | nil => simp
      | cons q qs ih => simp [hgram, ih]
  · rintro ⟨A, hA, rfl⟩
    obtain ⟨B, hfactor⟩ :=
      CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
    rw [hfactor, star_mul_self_eq_sum_rankOneGram, map_sum]
    simpa only [hgram] using
      finiteSumCone_finset_sum sq Finset.univ (fun k : n => fun i : n => B k i)

/-- A positive semidefinite matrix which annihilates a spanning collection of
vectors is zero. -/
theorem posSemidef_eq_zero_of_mulVec_eq_zero_on_spanning
    {ι n : Type*} [Fintype n]
    (e : ι → (n → ℝ))
    (hspan : Submodule.span ℝ (Set.range e) = ⊤)
    {A : Matrix n n ℝ} (hA : A.PosSemidef)
    (hzero : ∀ i, dotProduct (e i) (Matrix.mulVec A (e i)) = 0) :
    A = 0 := by
  classical
  have hrange : Set.range e ⊆ LinearMap.ker (Matrix.toLin' A) := by
    rintro x ⟨i, rfl⟩
    apply LinearMap.mem_ker.mpr
    rw [Matrix.toLin'_apply]
    exact hA.dotProduct_mulVec_zero_iff (e i) |>.mp (by simpa using hzero i)
  have hker_top : LinearMap.ker (Matrix.toLin' A) = ⊤ := by
    apply top_unique
    rw [← hspan]
    exact Submodule.span_le.mpr hrange
  have hmap_zero : Matrix.toLin' A = 0 := LinearMap.ker_eq_top.mp hker_top
  apply Matrix.toLin'.injective
  simpa using hmap_zero

/-- If no nonzero linear functional vanishes on all evaluation vectors, those
vectors span the whole degree-one coordinate space.  This is the precise
finite-dimensional consequence of Zariski density used in Proposition 3.1. -/
theorem span_evaluations_eq_top_of_functionals_separate
    {ι n : Type*}
    (e : ι → (n → ℝ))
    (hseparate : ∀ f : (n → ℝ) →ₗ[ℝ] ℝ,
      (∀ i, f (e i) = 0) → f = 0) :
    Submodule.span ℝ (Set.range e) = ⊤ := by
  by_contra htop
  have hlt : Submodule.span ℝ (Set.range e) < ⊤ := lt_top_iff_ne_top.mpr htop
  obtain ⟨f, hf0, hfker⟩ :=
    (Submodule.span ℝ (Set.range e)).exists_le_ker_of_lt_top hlt
  apply hf0
  apply hseparate f
  intro i
  exact LinearMap.mem_ker.mp (hfker (Submodule.subset_span ⟨i, rfl⟩))

/-- Spanning real evaluation vectors turn vanishing of the represented
quadratic section into the kernel condition required for Gram-cone
closedness. -/
theorem gram_ker_eq_zero_of_spanning_evaluations
    {ι n W : Type*} [Fintype n]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (e : ι → (n → ℝ))
    (hspan : Submodule.span ℝ (Set.range e) = ⊤)
    (T : Matrix n n ℝ →L[ℝ] W)
    (hvanish : ∀ A, T A = 0 →
      ∀ i, dotProduct (e i) (Matrix.mulVec A (e i)) = 0) :
    ∀ A ∈ realGramCone n, T A = 0 → A = 0 := by
  classical
  intro A hA hTA
  exact posSemidef_eq_zero_of_mulVec_eq_zero_on_spanning e hspan hA (hvanish A hTA)

/-- A PSD Gram matrix representing a section annihilated by a nonnegative
functional has range inside the functional's null subspace.  Consequently its
rank is at most the dimension of that subspace.  This is the Gram-rank upper
bound used in Theorem 8.3. -/
theorem supported_psd_gram_finrank_le
    {n W : Type*} [Fintype n] [DecidableEq n]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (sq : (n → ℝ) → W) (T : Matrix n n ℝ →L[ℝ] W)
    (hgram : ∀ q, T (rankOneGram q) = sq q)
    (ell : W →ₗ[ℝ] ℝ) (K : Submodule ℝ (n → ℝ))
    (hnonneg : ∀ q, 0 ≤ ell (sq q))
    (hnull : ∀ q, ell (sq q) = 0 ↔ q ∈ K)
    {A : Matrix n n ℝ} {p : W}
    (hA : A.PosSemidef) (hTA : T A = p) (hellp : ell p = 0) :
    Module.finrank ℝ (LinearMap.range (Matrix.toLin' A)) ≤ Module.finrank ℝ K := by
  obtain ⟨B, hfactor⟩ :=
    CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  have hsumzero :
      (∑ k : n, ell (sq (fun i : n => B k i))) = 0 := by
    have hellTA : ell (T A) = 0 := by rw [hTA, hellp]
    rw [hfactor, star_mul_self_eq_sum_rankOneGram, map_sum] at hellTA
    simpa only [hgram, map_sum] using hellTA
  have hrow : ∀ k, (fun i : n => B k i) ∈ K := by
    intro k
    apply (hnull _).mp
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun i hi => hnonneg (fun j : n => B i j))).mp hsumzero k (Finset.mem_univ k)
  rw [hfactor]
  exact finrank_range_star_mul_self_le K B hrow

/-- A supported sum of squares has an actual square representation whose
number of summands is at most the dimension of the support nullspace.  With
`finrank K = m+1`, this is the upper-bound half of Theorem 8.3. -/
theorem exists_squareRepresentation_card_le_of_supported
    {n W : Type*} [Fintype n] [DecidableEq n]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (sq : (n → ℝ) → W) (T : Matrix n n ℝ →L[ℝ] W)
    (hgram : ∀ q, T (rankOneGram q) = sq q)
    (ell : W →ₗ[ℝ] ℝ) (K : Submodule ℝ (n → ℝ))
    (hnonneg : ∀ q, 0 ≤ ell (sq q))
    (hnull : ∀ q, ell (sq q) = 0 ↔ q ∈ K)
    {p : W} (hp : p ∈ finiteSumCone sq) (hellp : ell p = 0) :
    ∃ (A : Matrix n n ℝ) (hA : A.PosSemidef)
      (q : {i // hA.isHermitian.eigenvalues i ≠ 0} → (n → ℝ)),
      p = ∑ i, sq (q i) ∧
      Fintype.card {i // hA.isHermitian.eigenvalues i ≠ 0} ≤
        Module.finrank ℝ K := by
  have hpImage : p ∈ T '' realGramCone n := by
    rw [← finiteSumCone_eq_image_realGramCone sq T hgram]
    exact hp
  obtain ⟨A, hA, hTA⟩ := hpImage
  obtain ⟨q, hpq, hcard⟩ :=
    exists_squareRepresentation_card_eq_finrank_of_posSemidef_gram
      sq T hgram hA hTA
  refine ⟨A, hA, q, hpq, ?_⟩
  rw [hcard]
  exact supported_psd_gram_finrank_le sq T hgram ell K hnonneg hnull hA hTA hellp

/-- Closedness of a Gram-represented sums-of-squares cone.  The kernel
hypothesis is precisely the absence of a nonzero positive semidefinite Gram
relation. -/
theorem finiteSumCone_isClosed_of_gram
    {n W : Type*} [Fintype n]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (sq : (n → ℝ) → W) (T : Matrix n n ℝ →L[ℝ] W)
    (hgram : ∀ q, T (rankOneGram q) = sq q)
    (hker : ∀ A ∈ realGramCone n, T A = 0 → A = 0) :
    IsClosed (finiteSumCone sq) := by
  classical
  rw [finiteSumCone_eq_image_realGramCone sq T hgram]
  exact isClosed_image_of_closed_cone_ker_eq_zero T (realGramCone n)
    (realGramCone_isClosed n) (fun ha _ hA => realGramCone_smul ha hA) hker

/-- Evaluation-spanning version of Gram-cone closedness, matching the use of
Zariski-dense real points in Proposition 3.1. -/
theorem finiteSumCone_isClosed_of_gram_of_spanning_evaluations
    {ι n W : Type*} [Fintype n]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (sq : (n → ℝ) → W) (T : Matrix n n ℝ →L[ℝ] W)
    (hgram : ∀ q, T (rankOneGram q) = sq q)
    (e : ι → (n → ℝ))
    (hspan : Submodule.span ℝ (Set.range e) = ⊤)
    (hvanish : ∀ A, T A = 0 →
      ∀ i, dotProduct (e i) (Matrix.mulVec A (e i)) = 0) :
    IsClosed (finiteSumCone sq) := by
  classical
  apply finiteSumCone_isClosed_of_gram sq T hgram
  exact gram_ker_eq_zero_of_spanning_evaluations e hspan T hvanish

/-- The closedness, full-dimensionality, convexity, and dual description of a
finite-dimensional sums-of-squares cone, under the explicit Gram and spanning
evaluation hypotheses used in Proposition 3.1. -/
theorem finiteSumCone_closed_fullDimensional_dual
    {ι n W : Type*} [Fintype n]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (sq : (n → ℝ) → W) (T : Matrix n n ℝ →L[ℝ] W)
    (hsq : ∀ (a : ℝ), 0 ≤ a → ∀ q, ∃ r, sq r = a • sq q)
    (hsq_span : Submodule.span ℝ (Set.range sq) = ⊤)
    (hgram : ∀ q, T (rankOneGram q) = sq q)
    (e : ι → (n → ℝ))
    (he_span : Submodule.span ℝ (Set.range e) = ⊤)
    (hvanish : ∀ A, T A = 0 →
      ∀ i, dotProduct (e i) (Matrix.mulVec A (e i)) = 0) :
    IsClosed (finiteSumCone sq) ∧
      Convex ℝ (finiteSumCone sq) ∧
      (interior (finiteSumCone sq)).Nonempty ∧
      ∀ ell : W →ₗ[ℝ] ℝ,
        (∀ w ∈ finiteSumCone sq, 0 ≤ ell w) ↔ ∀ q, 0 ≤ ell (sq q) := by
  classical
  refine ⟨finiteSumCone_isClosed_of_gram_of_spanning_evaluations
      sq T hgram e he_span hvanish,
    finiteSumCone_convex sq hsq,
    finiteSumCone_interior_nonempty_of_span_eq_top sq hsq hsq_span, ?_⟩
  exact fun ell => nonnegative_on_finiteSumCone_iff sq ell

/-- Gram compatibility itself supplies the square-root scaling hypothesis, so
the combined Proposition 3.1 theorem can be stated without a separate conic
assumption on `sq`. -/
theorem finiteSumCone_closed_fullDimensional_dual_of_gram
    {ι n W : Type*} [Fintype n]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (sq : (n → ℝ) → W) (T : Matrix n n ℝ →L[ℝ] W)
    (hsq_span : Submodule.span ℝ (Set.range sq) = ⊤)
    (hgram : ∀ q, T (rankOneGram q) = sq q)
    (e : ι → (n → ℝ))
    (he_span : Submodule.span ℝ (Set.range e) = ⊤)
    (hvanish : ∀ A, T A = 0 →
      ∀ i, dotProduct (e i) (Matrix.mulVec A (e i)) = 0) :
    IsClosed (finiteSumCone sq) ∧
      Convex ℝ (finiteSumCone sq) ∧
      (interior (finiteSumCone sq)).Nonempty ∧
      ∀ ell : W →ₗ[ℝ] ℝ,
        (∀ w ∈ finiteSumCone sq, 0 ≤ ell w) ↔ ∀ q, 0 ≤ ell (sq q) := by
  classical
  apply finiteSumCone_closed_fullDimensional_dual sq T _ hsq_span hgram e he_span hvanish
  intro a ha q
  refine ⟨Real.sqrt a • q, ?_⟩
  rw [← hgram, rankOneGram_smul, map_smul, Real.sq_sqrt ha, hgram]

/-- Zariski-density-interface version of the full Proposition 3.1 package: it
is enough to know that real evaluations separate linear functionals. -/
theorem finiteSumCone_closed_fullDimensional_dual_of_separating_evaluations
    {ι n W : Type*} [Fintype n]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (sq : (n → ℝ) → W) (T : Matrix n n ℝ →L[ℝ] W)
    (hsq_span : Submodule.span ℝ (Set.range sq) = ⊤)
    (hgram : ∀ q, T (rankOneGram q) = sq q)
    (e : ι → (n → ℝ))
    (hseparate : ∀ f : (n → ℝ) →ₗ[ℝ] ℝ,
      (∀ i, f (e i) = 0) → f = 0)
    (hvanish : ∀ A, T A = 0 →
      ∀ i, dotProduct (e i) (Matrix.mulVec A (e i)) = 0) :
    IsClosed (finiteSumCone sq) ∧
      Convex ℝ (finiteSumCone sq) ∧
      (interior (finiteSumCone sq)).Nonempty ∧
      ∀ ell : W →ₗ[ℝ] ℝ,
        (∀ w ∈ finiteSumCone sq, 0 ≤ ell w) ↔ ∀ q, 0 ≤ ell (sq q) := by
  classical
  exact finiteSumCone_closed_fullDimensional_dual_of_gram sq T hsq_span hgram e
    (span_evaluations_eq_top_of_functionals_separate e hseparate) hvanish

end

end DelPezzoBlekherman
