/-
Copyright (c) 2026 Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import DelPezzoBlekherman.Convexity.GramCone
import DelPezzoBlekherman.Fiber.GeometricObstruction
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Sums-of-squares length

Finite-dimensional Gram arguments used in the lower-bound half of Theorem 8.3.
-/

open Set
open scoped BigOperators

namespace DelPezzoBlekherman

/-- A square family is shortest if its cardinality is no larger than that of
any other finite family representing the same element. -/
def IsMinimalSquareRepresentation
    {n W : Type*} [AddCommMonoid W]
    (sq : (n → ℝ) → W) (p : W) {r : ℕ} (q : Fin r → (n → ℝ)) : Prop :=
  p = ∑ i, sq (q i) ∧
    ∀ (r' : ℕ) (q' : Fin r' → (n → ℝ)), p = ∑ i, sq (q' i) → r ≤ r'

/-- The assertion that `p` has a square representation with exactly `r`
indexed summands. -/
def HasSquareRepresentationLength
    {n W : Type*} [AddCommMonoid W]
    (sq : (n → ℝ) → W) (p : W) (r : ℕ) : Prop :=
  ∃ q : Fin r → (n → ℝ), p = ∑ i, sq (q i)

/-- The SOS length as a natural number.  It is the least represented length
when a representation exists, and is defined to be zero off the finite-sum
cone. -/
noncomputable def sosLength
    {n W : Type*} [AddCommMonoid W]
    (sq : (n → ℝ) → W) (p : W) : ℕ := by
  classical
  exact if h : ∃ r, HasSquareRepresentationLength sq p r then Nat.find h else 0

/-- Every element of a finite-sum cone admits a shortest square
representation, by well-ordering the possible natural-number lengths. -/
theorem exists_isMinimalSquareRepresentation_of_mem_finiteSumCone
    {n W : Type*} [AddCommMonoid W]
    (sq : (n → ℝ) → W) {p : W} (hp : p ∈ finiteSumCone sq) :
    ∃ (r : ℕ) (q : Fin r → (n → ℝ)), IsMinimalSquareRepresentation sq p q := by
  classical
  let P : ℕ → Prop := fun r ↦ ∃ q : Fin r → (n → ℝ), p = ∑ i, sq (q i)
  have hP : ∃ r, P r := by
    obtain ⟨qs, hpqs⟩ := hp
    refine ⟨qs.length, (fun i ↦ qs.get i), ?_⟩
    rw [hpqs]
    simp
  let r := Nat.find hP
  obtain ⟨q, hq⟩ := Nat.find_spec hP
  refine ⟨r, q, hq, ?_⟩
  intro r' q' hq'
  exact Nat.find_min' hP ⟨q', hq'⟩

/-- On the finite-sum cone, the numerical SOS length is represented by an
actual family of that length. -/
theorem exists_squareRepresentation_sosLength_of_mem_finiteSumCone
    {n W : Type*} [AddCommMonoid W]
    (sq : (n → ℝ) → W) {p : W} (hp : p ∈ finiteSumCone sq) :
    ∃ q : Fin (sosLength sq p) → (n → ℝ), p = ∑ i, sq (q i) := by
  classical
  have hex : ∃ r, HasSquareRepresentationLength sq p r := by
    obtain ⟨r, q, hmin⟩ :=
      exists_isMinimalSquareRepresentation_of_mem_finiteSumCone sq hp
    exact ⟨r, q, hmin.1⟩
  rw [sosLength, dif_pos hex]
  exact Nat.find_spec hex

/-- Every shortest representation has cardinality equal to the numerical SOS
length. -/
theorem sosLength_eq_of_isMinimalSquareRepresentation
    {n W : Type*} [AddCommMonoid W]
    (sq : (n → ℝ) → W) {p : W} {r : ℕ} {q : Fin r → (n → ℝ)}
    (hmin : IsMinimalSquareRepresentation sq p q) :
    sosLength sq p = r := by
  classical
  have hex : ∃ r', HasSquareRepresentationLength sq p r' := ⟨r, q, hmin.1⟩
  have hspec : HasSquareRepresentationLength sq p (Nat.find hex) := Nat.find_spec hex
  obtain ⟨q', hq'⟩ := hspec
  have hrle : r ≤ Nat.find hex := hmin.2 (Nat.find hex) q' hq'
  have hler : Nat.find hex ≤ r := Nat.find_min' hex ⟨q, hmin.1⟩
  rw [sosLength, dif_pos hex]
  omega

/-- The summands in a shortest SOS representation are linearly independent.
Otherwise their Gram matrix has rank strictly below the number of summands,
and spectral decomposition produces a shorter representation. -/
theorem linearIndependent_of_isMinimalSquareRepresentation
    {n W : Type*} {r : ℕ} [Finite n]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (sq : (n → ℝ) → W) (T : Matrix n n ℝ →L[ℝ] W)
    (hgram : ∀ q, T (rankOneGram q) = sq q)
    {p : W} {q : Fin r → (n → ℝ)}
    (hmin : IsMinimalSquareRepresentation sq p q) :
    LinearIndependent ℝ q := by
  classical
  let _ := Fintype.ofFinite n
  by_contra hdep
  have hspan_lt :
      Module.finrank ℝ (Submodule.span ℝ (Set.range q)) < r := by
    have hle : Module.finrank ℝ (Submodule.span ℝ (Set.range q)) ≤ r := by
      simpa [Set.finrank] using finrank_range_le_card q
    have hne : Module.finrank ℝ (Submodule.span ℝ (Set.range q)) ≠ r := by
      intro heq
      apply hdep
      apply linearIndependent_iff_card_eq_finrank_span.mpr
      simpa [Set.finrank] using heq.symm
    exact lt_of_le_of_ne hle hne
  let A : Matrix n n ℝ := gramOfFamily q
  have hA : A.PosSemidef := gramOfFamily_posSemidef q
  have hTA : T A = p := by
    dsimp [A]
    rw [map_gramOfFamily sq T hgram q, ← hmin.1]
  have hrank_lt :
      Module.finrank ℝ (LinearMap.range (Matrix.toLin' A)) < r :=
    lt_of_le_of_lt (finrank_range_gramOfFamily_le_finrank_span q) hspan_lt
  obtain ⟨q', hpq', hcard⟩ :=
    exists_squareRepresentation_card_eq_finrank_of_posSemidef_gram
      sq T hgram hA hTA
  let J := {i // hA.isHermitian.eigenvalues i ≠ 0}
  let e : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  let qFin : Fin (Fintype.card J) → (n → ℝ) := q' ∘ e.symm
  have hpqFin : p = ∑ i, sq (qFin i) := by
    rw [hpq']
    exact Fintype.sum_equiv e _ _ (fun i ↦ by simp [qFin, e])
  have hshort : Fintype.card J < r := by
    rw [hcard]
    exact hrank_lt
  have hminimal := hmin.2 (Fintype.card J) qFin hpqFin
  omega

/-- A supported sum of squares has a shortest representation lying in the
support nullspace, and its shortest length is at most the dimension of that
nullspace. -/
theorem exists_minimalSquareRepresentation_card_le_of_supported
    {n W : Type*} [Finite n]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (sq : (n → ℝ) → W) (T : Matrix n n ℝ →L[ℝ] W)
    (hgram : ∀ q, T (rankOneGram q) = sq q)
    (ell : W →ₗ[ℝ] ℝ) (K : Submodule ℝ (n → ℝ))
    (hnonneg : ∀ q, 0 ≤ ell (sq q))
    (hnull : ∀ q, ell (sq q) = 0 ↔ q ∈ K)
    {p : W} (hp : p ∈ finiteSumCone sq) (hellp : ell p = 0) :
    ∃ (r : ℕ) (q : Fin r → (n → ℝ)),
      IsMinimalSquareRepresentation sq p q ∧
      r ≤ Module.finrank ℝ K ∧ ∀ i, q i ∈ K := by
  classical
  let _ := Fintype.ofFinite n
  obtain ⟨r, q, hmin⟩ :=
    exists_isMinimalSquareRepresentation_of_mem_finiteSumCone sq hp
  have hqK : ∀ i, q i ∈ K := by
    intro i
    apply (hnull (q i)).mp
    exact support_vanishes_on_each_square sq ell hnonneg q hmin.1 hellp i
  obtain ⟨A, hA, q', hpq', hcard⟩ :=
    exists_squareRepresentation_card_le_of_supported
      sq T hgram ell K hnonneg hnull hp hellp
  let J := {i // hA.isHermitian.eigenvalues i ≠ 0}
  let e : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  let qFin : Fin (Fintype.card J) → (n → ℝ) := q' ∘ e.symm
  have hpqFin : p = ∑ i, sq (qFin i) := by
    rw [hpq']
    exact Fintype.sum_equiv e _ _ (fun i ↦ by simp [qFin, e])
  refine ⟨r, q, hmin, (hmin.2 (Fintype.card J) qFin hpqFin).trans ?_, hqK⟩
  exact hcard

/-- A linearly independent family of at most `m` vectors in an
`(m + 1)`-dimensional real vector space is contained in an `m`-dimensional
subspace.  This is the basis-extension step used for a shortest SOS family in
the proof of Theorem 8.3. -/
theorem exists_finrank_eq_containing_of_linearIndependent
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    {r m : ℕ} (q : Fin r → V) (hq : LinearIndependent ℝ q)
    (hrm : r ≤ m) (hdim : Module.finrank ℝ V = m + 1) :
    ∃ U : Submodule ℝ V,
      Submodule.span ℝ (Set.range q) ≤ U ∧ Module.finrank ℝ U = m := by
  let S : Submodule ℝ V := Submodule.span ℝ (Set.range q)
  have hSdim : Module.finrank ℝ S = r := by
    simpa [S] using finrank_span_eq_card hq
  have hSlt : Module.finrank ℝ S < Module.finrank ℝ V := by
    rw [hSdim, hdim]
    omega
  obtain ⟨f, hf, hSf⟩ :=
    S.exists_le_ker_of_lt_top (Submodule.lt_top_of_finrank_lt_finrank hSlt)
  refine ⟨LinearMap.ker f, hSf, ?_⟩
  have hk := Module.Dual.finrank_ker_add_one_of_ne_zero hf
  rw [hdim] at hk
  omega

/-- Ambient-space version of `exists_finrank_eq_containing_of_linearIndependent`:
the desired `m`-plane lies inside a prescribed `(m + 1)`-plane `K`. -/
theorem exists_submodule_finrank_eq_containing_of_linearIndependent
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    {r m : ℕ} (K : Submodule ℝ V) (q : Fin r → V)
    (hq : LinearIndependent ℝ q) (hqK : ∀ i, q i ∈ K)
    (hrm : r ≤ m) (hdim : Module.finrank ℝ K = m + 1) :
    ∃ U : Submodule ℝ V,
      Submodule.span ℝ (Set.range q) ≤ U ∧ U ≤ K ∧ Module.finrank ℝ U = m := by
  let qK : Fin r → K := fun i ↦ ⟨q i, hqK i⟩
  have hqKli : LinearIndependent ℝ qK := by
    apply LinearIndependent.of_comp K.subtype
    simpa [qK, Function.comp_def] using hq
  obtain ⟨UK, hspan, hUKdim⟩ :=
    exists_finrank_eq_containing_of_linearIndependent qK hqKli hrm hdim
  let U : Submodule ℝ V := UK.map K.subtype
  refine ⟨U, ?_, ?_, ?_⟩
  · apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    refine ⟨qK i, hspan (Submodule.subset_span ⟨i, rfl⟩), ?_⟩
    rfl
  · rintro x ⟨y, hy, rfl⟩
    exact y.property
  · simpa [U] using (Submodule.finrank_map_subtype_eq K UK).trans hUKdim

/-- The two shortest-SOS linear-algebra steps in one statement: minimality
forces independence, and a shortest family contained in an `(m + 1)`-plane
and having length at most `m` lies in an `m`-plane inside it. -/
theorem exists_submodule_finrank_eq_containing_of_isMinimalSquareRepresentation
    {n W : Type*} {r m : ℕ} [Finite n]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (sq : (n → ℝ) → W) (T : Matrix n n ℝ →L[ℝ] W)
    (hgram : ∀ q, T (rankOneGram q) = sq q)
    (K : Submodule ℝ (n → ℝ)) {p : W} {q : Fin r → (n → ℝ)}
    (hmin : IsMinimalSquareRepresentation sq p q) (hqK : ∀ i, q i ∈ K)
    (hrm : r ≤ m) (hdim : Module.finrank ℝ K = m + 1) :
    ∃ U : Submodule ℝ (n → ℝ),
      Submodule.span ℝ (Set.range q) ≤ U ∧ U ≤ K ∧ Module.finrank ℝ U = m := by
  exact exists_submodule_finrank_eq_containing_of_linearIndependent K q
    (linearIndependent_of_isMinimalSquareRepresentation sq T hgram hmin)
    hqK hrm hdim

/-- Conditional final length assembly for Theorem 8.3.  All convex, Gram,
minimality, and positivity steps are internal.  The sole geometric interface
`hgeometric` says that an `m`-plane inside the supporting nullspace cannot be
basepoint-free; Proposition 5.1 plus Proposition 6.2 supply exactly this
obstruction in the paper. -/
theorem exists_minimalSquareRepresentation_length_eq_of_geometric_obstruction
    {n W X : Type*} [Finite n]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (sq : (n → ℝ) → W) (T : Matrix n n ℝ →L[ℝ] W)
    (hgram : ∀ q, T (rankOneGram q) = sq q)
    (ell : W →ₗ[ℝ] ℝ) (K : Submodule ℝ (n → ℝ))
    (hnonneg : ∀ q, 0 ≤ ell (sq q))
    (hnull : ∀ q, ell (sq q) = 0 ↔ q ∈ K)
    (evOne : X → (n → ℝ) →ₗ[ℝ] ℝ) (evTwo : X → W →ₗ[ℝ] ℝ)
    (hsqeval : ∀ x q, evTwo x (sq q) = (evOne x q) ^ 2)
    {m : ℕ} (hKdim : Module.finrank ℝ K = m + 1)
    {p : W} (hp : p ∈ finiteSumCone sq) (hellp : ell p = 0)
    (hpositive : ∀ x, 0 < evTwo x p)
    (hgeometric : ∀ U : Submodule ℝ (n → ℝ),
      U ≤ K → Module.finrank ℝ U = m →
      IsBasepointFreeForEvaluation evOne U → False) :
    ∃ (r : ℕ) (q : Fin r → (n → ℝ)),
      IsMinimalSquareRepresentation sq p q ∧
      r = m + 1 ∧ sosLength sq p = m + 1 := by
  obtain ⟨r, q, hmin, hrK, hqK⟩ :=
    exists_minimalSquareRepresentation_card_le_of_supported
      sq T hgram ell K hnonneg hnull hp hellp
  have hrUpper : r ≤ m + 1 := by
    rw [← hKdim]
    exact hrK
  have hrNotLe : ¬r ≤ m := by
    intro hrm
    obtain ⟨U, hspan, hUK, hUdim⟩ :=
      exists_submodule_finrank_eq_containing_of_isMinimalSquareRepresentation
        sq T hgram K hmin hqK hrm hKdim
    apply hgeometric U hUK hUdim
    intro x
    by_contra hcommon
    have hqzero : ∀ i, evOne x (q i) = 0 := by
      intro i
      by_contra hi
      apply hcommon
      exact ⟨q i, hspan (Submodule.subset_span ⟨i, rfl⟩), hi⟩
    have hpzero : evTwo x p = 0 := by
      rw [hmin.1, map_sum]
      simp [hsqeval, hqzero]
    linarith [hpositive x]
  have hr : r = m + 1 := by omega
  refine ⟨r, q, hmin, hr, ?_⟩
  rw [sosLength_eq_of_isMinimalSquareRepresentation sq hmin, hr]

/-- Theorem 8.3 length assembly with the geometric obstruction expanded into
the finite-fiber data used to prove it.  The remaining hypotheses now mirror
the scheme-theoretic bridge: a compact continuous real map, dense good-fiber
locus, an omitted point for a basepoint-free plane, and the two fiber pair
bounds. -/
theorem exists_minimalSquareRepresentation_length_eq_of_fiber_pair_data
    {n W X Y : Type*} [Finite n]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [T2Space Y]
    (sq : (n → ℝ) → W) (T : Matrix n n ℝ →L[ℝ] W)
    (hgram : ∀ q, T (rankOneGram q) = sq q)
    (ell : W →ₗ[ℝ] ℝ) (K : Submodule ℝ (n → ℝ))
    (hnonneg : ∀ q, 0 ≤ ell (sq q))
    (hnull : ∀ q, ell (sq q) = 0 ↔ q ∈ K)
    (evOne : X → (n → ℝ) →ₗ[ℝ] ℝ) (evTwo : X → W →ₗ[ℝ] ℝ)
    (hsqeval : ∀ x q, evTwo x (sq q) = (evOne x q) ^ 2)
    {m : ℕ} (hKdim : Module.finrank ℝ K = m + 1)
    {p : W} (hp : p ∈ finiteSumCone sq) (hellp : ell p = 0)
    (hpositive : ∀ x, 0 < evTwo x p)
    (phi : X → Y) (hphi : Continuous phi)
    (Omega : Set Y) (hOmega : Dense Omega) (pairCount : Y → ℕ)
    (hcard : ∀ y ∈ Omega, y ∉ Set.range phi → 3 ≤ 2 * pairCount y)
    (hatMostOne : ∀ y ∈ Omega, pairCount y ≤ 1)
    (pointOfPlane : Submodule ℝ (n → ℝ) → Y)
    (homitted : ∀ U, U ≤ K → Module.finrank ℝ U = m →
      IsBasepointFreeForEvaluation evOne U →
      pointOfPlane U ∉ Set.range phi) :
    ∃ (r : ℕ) (q : Fin r → (n → ℝ)),
      IsMinimalSquareRepresentation sq p q ∧
      r = m + 1 ∧ sosLength sq p = m + 1 := by
  apply exists_minimalSquareRepresentation_length_eq_of_geometric_obstruction
    sq T hgram ell K hnonneg hnull evOne evTwo hsqeval hKdim hp hellp hpositive
  exact no_basepointFree_submodule_of_dense_fiber_pair_bounds
    evOne K m phi hphi Omega hOmega pairCount hcard hatMostOne pointOfPlane homitted

end DelPezzoBlekherman
