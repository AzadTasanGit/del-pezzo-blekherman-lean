import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

noncomputable section

universe u v w

open scoped BigOperators
open Finset

namespace SOSCompression

variable {V : Type u} {Q : Type v}
  [AddCommGroup V] [Module ℝ V]
  [AddCommGroup Q] [Module ℝ Q]

def sumSquares {ι : Type w} [Fintype ι]
    (B : LinearMap.BilinMap ℝ V Q) (f : ι → V) : Q :=
  ∑ i, B (f i) (f i)

/-- The explicit scalar used to take the square root of `I + b bᵀ`. -/
def updateScalar (S : ℝ) : ℝ := (Real.sqrt (1 + S) - 1) / S

theorem updateScalar_identity {S : ℝ} (hS : 0 < S) :
    2 * updateScalar S + (updateScalar S) ^ 2 * S = 1 := by
  have hnonneg : 0 ≤ 1 + S := by positivity
  have hsqrt : (Real.sqrt (1 + S)) ^ 2 = 1 + S := Real.sq_sqrt hnonneg
  rw [updateScalar]
  field_simp [hS.ne']
  nlinarith

/-- A nonzero real coefficient vector has positive squared norm. -/
theorem sum_sq_pos {ι : Type w} [Fintype ι] (b : ι → ℝ) (hb : b ≠ 0) :
    0 < ∑ i, (b i) ^ 2 := by
  have hex : ∃ i, b i ≠ 0 := by
    by_contra h
    apply hb
    funext i
    exact not_ne_iff.mp (not_exists.mp h i)
  obtain ⟨i, hi⟩ := hex
  apply Finset.sum_pos'
  · intro j hj
    exact sq_nonneg (b j)
  · exact ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩

/-- Rank-one update formula.  If `F = ∑ bᵢ fᵢ`, the updated family has square-sum equal to the
old square-sum plus the square of `F`. -/
theorem rankOne_update
    {ι : Type w} [Fintype ι]
    (B : LinearMap.BilinMap ℝ V Q) (f : ι → V) (b : ι → ℝ)
    (F : V) (hF : F = ∑ i, b i • f i) (hb : b ≠ 0) :
    let lambda := updateScalar (∑ i, (b i) ^ 2)
    let g : ι → V := fun i ↦ f i + (lambda * b i) • F
    sumSquares B g = sumSquares B f + B F F := by
  let S : ℝ := ∑ i, (b i) ^ 2
  let lambda : ℝ := updateScalar S
  let g : ι → V := fun i ↦ f i + (lambda * b i) • F
  have hS : 0 < S := sum_sq_pos b hb
  have hlambda : 2 * lambda + lambda ^ 2 * S = 1 :=
    updateScalar_identity hS
  have hleft : ∑ i, (lambda * b i) • B (f i) F = lambda • B F F := by
    calc
      (∑ i, (lambda * b i) • B (f i) F) =
          lambda • ∑ i, b i • B (f i) F := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        simp only [smul_smul]
      _ = lambda • B (∑ i, b i • f i) F := by simp
      _ = lambda • B F F := by rw [← hF]
  have hright : ∑ i, (lambda * b i) • B F (f i) = lambda • B F F := by
    calc
      (∑ i, (lambda * b i) • B F (f i)) =
          lambda • ∑ i, b i • B F (f i) := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        simp only [smul_smul]
      _ = lambda • B F (∑ i, b i • f i) := by simp
      _ = lambda • B F F := by rw [← hF]
  have hquad : ∑ i, ((lambda * b i) * (lambda * b i)) • B F F =
      (lambda ^ 2 * S) • B F F := by
    rw [← Finset.sum_smul]
    congr 1
    change (∑ i, (lambda * b i) * (lambda * b i)) =
      lambda ^ 2 * ∑ i, (b i) ^ 2
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  change sumSquares B g = sumSquares B f + B F F
  have hexpand (i : ι) : B (g i) (g i) =
      B (f i) (f i) + ((lambda * b i) • B F (f i) +
        ((lambda * b i) • B (f i) F +
          ((lambda * b i) * (lambda * b i)) • B F F)) := by
    simp only [g, map_add, LinearMap.add_apply, LinearMap.map_smul,
      LinearMap.smul_apply, smul_smul]
    rw [add_assoc]
  simp only [sumSquares]
  rw [Finset.sum_congr rfl (fun i hi ↦ hexpand i)]
  simp only [Finset.sum_add_distrib]
  rw [hleft, hright, hquad]
  abel_nf
  simp only [two_smul, ← add_smul]
  have hcoeff : lambda + lambda + lambda ^ 2 * S = 1 := by linarith
  rw [hcoeff, one_smul]

/-- One redundant square can be eliminated whenever its vector is supplied as an explicit linear
combination of the others.  The zero combination is handled without a positivity hypothesis. -/
theorem compress_one_extra_explicit
    {ι : Type w} [Fintype ι]
    (B : LinearMap.BilinMap ℝ V Q) (f : ι → V) (b : ι → ℝ)
    (F : V) (hF : F = ∑ i, b i • f i) :
    ∃ g : ι → V, sumSquares B g = sumSquares B f + B F F := by
  by_cases hb : b = 0
  · subst b
    simp at hF
    subst F
    exact ⟨f, by simp⟩
  · let lambda := updateScalar (∑ i, (b i) ^ 2)
    let g : ι → V := fun i ↦ f i + (lambda * b i) • F
    exact ⟨g, rankOne_update B f b F hF hb⟩

/-- The rank-one compression update preserves the span of the original family. -/
theorem rankOne_update_span_eq
    {ι : Type w} [Fintype ι]
    (f : ι → V) (b : ι → ℝ) (F : V)
    (hF : F = ∑ i, b i • f i) (hb : b ≠ 0) :
    let S := ∑ i, (b i) ^ 2
    let lambda := updateScalar S
    let g : ι → V := fun i ↦ f i + (lambda * b i) • F
    Submodule.span ℝ (Set.range g) = Submodule.span ℝ (Set.range f) := by
  let S : ℝ := ∑ i, (b i) ^ 2
  let lambda : ℝ := updateScalar S
  let g : ι → V := fun i ↦ f i + (lambda * b i) • F
  have hS : 0 < S := sum_sq_pos b hb
  have hsqrt : 0 < Real.sqrt (1 + S) := Real.sqrt_pos.2 (by positivity)
  have hfactor : 1 + lambda * S = Real.sqrt (1 + S) := by
    dsimp only [lambda, updateScalar]
    field_simp [hS.ne']
    ring
  have hfactor_ne : 1 + lambda * S ≠ 0 := by
    rw [hfactor]
    exact hsqrt.ne'
  have hFmem : F ∈ Submodule.span ℝ (Set.range f) :=
    (Submodule.mem_span_range_iff_exists_fun ℝ).2 ⟨b, hF.symm⟩
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    exact Submodule.add_mem _ (Submodule.subset_span ⟨i, rfl⟩)
      (Submodule.smul_mem _ _ hFmem)
  · have hweighted : ∑ i, b i • g i = (1 + lambda * S) • F := by
      have hcoeffsum : (∑ i, b i * (lambda * b i)) = lambda * S := by
        change (∑ i, b i * (lambda * b i)) = lambda * ∑ i, (b i) ^ 2
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      calc
        (∑ i, b i • g i) =
            (∑ i, b i • f i) + ∑ i, (b i * (lambda * b i)) • F := by
          simp only [g, smul_add, Finset.sum_add_distrib, smul_smul]
        _ = F + (lambda * S) • F := by
          rw [← hF, ← Finset.sum_smul]
          rw [hcoeffsum]
        _ = (1 + lambda * S) • F := by
          rw [add_smul, one_smul]
    have hscaled : (1 + lambda * S) • F ∈
        Submodule.span ℝ (Set.range g) := by
      rw [← hweighted]
      exact (Submodule.mem_span_range_iff_exists_fun ℝ).2 ⟨b, rfl⟩
    have hFmemg : F ∈ Submodule.span ℝ (Set.range g) := by
      have hinv := Submodule.smul_mem (Submodule.span ℝ (Set.range g))
        (1 + lambda * S)⁻¹ hscaled
      simpa [smul_smul, hfactor_ne] using hinv
    rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    have hgmem : g i ∈ Submodule.span ℝ (Set.range g) :=
      Submodule.subset_span ⟨i, rfl⟩
    have hsub := Submodule.sub_mem _ hgmem
      (Submodule.smul_mem _ (lambda * b i) hFmemg)
    simpa [g] using hsub

/-- One-step compression, simultaneously preserving the represented datum and the linear span. -/
theorem compress_one_extra_explicit_span
    {ι : Type w} [Fintype ι]
    (B : LinearMap.BilinMap ℝ V Q) (f : ι → V) (b : ι → ℝ)
    (F : V) (hF : F = ∑ i, b i • f i) :
    ∃ g : ι → V,
      sumSquares B g = sumSquares B f + B F F ∧
      Submodule.span ℝ (Set.range g) = Submodule.span ℝ (Set.range f) := by
  by_cases hb : b = 0
  · subst b
    simp at hF
    subst F
    exact ⟨f, by simp⟩
  · let lambda := updateScalar (∑ i, (b i) ^ 2)
    let g : ι → V := fun i ↦ f i + (lambda * b i) • F
    exact ⟨g, rankOne_update B f b F hF hb,
      rankOne_update_span_eq f b F hF hb⟩

/-- Sum of the diagonal bilinear values of a list. -/
def listSumSquares (B : LinearMap.BilinMap ℝ V Q) : List V → Q
  | [] => 0
  | F :: rest => B F F + listSumSquares B rest

/-- Any finite list of squares whose vectors lie in the span of a fixed finite family can be
absorbed into that family.  Both its cardinality and its span stay fixed. -/
theorem compress_list_into_family
    {ι : Type w} [Fintype ι]
    (B : LinearMap.BilinMap ℝ V Q) (f : ι → V) (extras : List V)
    (hspan : ∀ F ∈ extras, F ∈ Submodule.span ℝ (Set.range f)) :
    ∃ g : ι → V,
      Submodule.span ℝ (Set.range g) = Submodule.span ℝ (Set.range f) ∧
      sumSquares B g = sumSquares B f + listSumSquares B extras := by
  induction extras generalizing f with
  | nil =>
      exact ⟨f, rfl, by simp [listSumSquares]⟩
  | cons F rest ih =>
      have hFmem : F ∈ Submodule.span ℝ (Set.range f) := hspan F (by simp)
      obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hFmem
      obtain ⟨g, hsumg, hspang⟩ :=
        compress_one_extra_explicit_span B f b F hb.symm
      have hrest : ∀ x ∈ rest, x ∈ Submodule.span ℝ (Set.range g) := by
        intro x hx
        rw [hspang]
        exact hspan x (by simp [hx])
      obtain ⟨g', hspang', hsumg'⟩ := ih g hrest
      refine ⟨g', hspang'.trans hspang, ?_⟩
      rw [hsumg', hsumg]
      simp only [listSumSquares]
      abel

/-- Finset-indexed version of finite absorption, convenient for splitting an original family into
a spanning subfamily and its complement. -/
theorem compress_finset_into_family
    {ι : Type w} [Fintype ι] {κ : Type*} [DecidableEq κ]
    (B : LinearMap.BilinMap ℝ V Q) (f : ι → V) (F : κ → V) (extras : Finset κ)
    (hspan : ∀ k ∈ extras, F k ∈ Submodule.span ℝ (Set.range f)) :
    ∃ g : ι → V,
      Submodule.span ℝ (Set.range g) = Submodule.span ℝ (Set.range f) ∧
      sumSquares B g = sumSquares B f + ∑ k ∈ extras, B (F k) (F k) := by
  induction extras using Finset.induction_on generalizing f with
  | empty =>
      exact ⟨f, rfl, by simp⟩
  | @insert k extras hk ih =>
      have hkspan : F k ∈ Submodule.span ℝ (Set.range f) := hspan k (by simp)
      obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hkspan
      obtain ⟨g, hsumg, hspang⟩ :=
        compress_one_extra_explicit_span B f b (F k) hb.symm
      have hrest : ∀ j ∈ extras, F j ∈ Submodule.span ℝ (Set.range g) := by
        intro j hj
        rw [hspang]
        exact hspan j (by simp [hj])
      obtain ⟨g', hspang', hsumg'⟩ := ih g hrest
      refine ⟨g', hspang'.trans hspang, ?_⟩
      rw [hsumg', hsumg]
      simp only [Finset.sum_insert hk]
      abel

/-- If a subfamily spans every vector in a finite family, all remaining squares can be absorbed
into that subfamily.  Thus the represented quadratic datum needs no more squares than the size of
any supplied spanning subfamily. -/
theorem compress_to_spanning_subfamily
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {ι : Type w} [Fintype ι]
    (B : LinearMap.BilinMap ℝ V Q) (f : κ → V) (e : ι ↪ κ)
    (hspan : ∀ k, f k ∈ Submodule.span ℝ (Set.range fun i ↦ f (e i))) :
    ∃ g : ι → V, sumSquares B g = sumSquares B f := by
  let selected : Finset κ := Finset.univ.map e
  let extras : Finset κ := Finset.univ \ selected
  obtain ⟨g, hgspan, hgsum⟩ := compress_finset_into_family B
    (fun i ↦ f (e i)) f extras (by
      intro k hk
      exact hspan k)
  refine ⟨g, ?_⟩
  rw [hgsum]
  have hselected : (∑ k ∈ selected, B (f k) (f k)) =
      sumSquares B (fun i ↦ f (e i)) := by
    simp only [selected, sumSquares, Finset.sum_map]
  have hpartition : (∑ k ∈ extras, B (f k) (f k)) +
      ∑ k ∈ selected, B (f k) (f k) = ∑ k, B (f k) (f k) := by
    exact Finset.sum_sdiff (Finset.subset_univ selected)
  rw [hselected] at hpartition
  simpa only [sumSquares, add_comm] using hpartition

/-- A finite family over `ℝ` contains a subfamily which is a basis of its span.  This packages the
choice of original indices, rather than merely choosing an unrelated basis of the ambient space. -/
theorem exists_basis_subfamily
    {κ : Type*} [Fintype κ] [DecidableEq κ] (f : κ → V) :
    ∃ s : Finset κ,
      (∀ k, f k ∈ Submodule.span ℝ (Set.range fun i : s ↦ f i.1)) ∧
      s.card = Module.finrank ℝ (Submodule.span ℝ (Set.range f)) := by
  let P : Submodule ℝ V := Submodule.span ℝ (Set.range f)
  let vf : κ → P := fun k ↦ ⟨f k, Submodule.subset_span ⟨k, rfl⟩⟩
  have htop : Submodule.span ℝ (Set.range vf) = ⊤ :=
    (Submodule.span_range_subtype_eq_top_iff P
      (fun k ↦ Submodule.subset_span ⟨k, rfl⟩)).2 rfl
  let bas := Module.Basis.ofSpan htop.ge
  let I : Set P := (linearIndepOn_empty ℝ (id : P → P)).extend
    (Set.empty_subset (Set.range vf))
  have hrange (i : I) : ∃ k : κ, vf k = bas i := by
    have hi : bas i ∈ Set.range vf :=
      Module.Basis.ofSpan_subset htop.ge ⟨i, rfl⟩
    simpa only [Set.mem_range] using hi
  let pick : I → κ := fun i ↦ Classical.choose (hrange i)
  have hpick (i : I) : vf (pick i) = bas i := Classical.choose_spec (hrange i)
  have hpick_injective : Function.Injective pick := by
    intro i j hij
    apply bas.injective
    rw [← hpick i, ← hpick j, hij]
  letI : Finite I := Finite.of_injective pick hpick_injective
  letI : Fintype I := Fintype.ofFinite I
  let e : I ↪ κ := ⟨pick, hpick_injective⟩
  let s : Finset κ := Finset.univ.map e
  let es : I → s := fun i ↦ ⟨pick i, by
    simp only [s, Finset.mem_map, Finset.mem_univ, true_and]
    exact ⟨i, rfl⟩⟩
  have es_bijective : Function.Bijective es := by
    constructor
    · intro i j hij
      exact hpick_injective (Subtype.ext_iff.mp hij)
    · intro j
      have hj : j.1 ∈ Finset.univ.map e := j.2
      obtain ⟨i, hi⟩ : ∃ i, pick i = j.1 := by
        simp only [Finset.mem_map, Finset.mem_univ, true_and] at hj
        obtain ⟨i, hi⟩ := hj
        change pick i = j.1 at hi
        exact ⟨i, hi⟩
      exact ⟨i, Subtype.ext hi⟩
  let esEquiv : I ≃ s := Equiv.ofBijective es es_bijective
  refine ⟨s, ?_, ?_⟩
  · intro k
    let x : P := ⟨f k, Submodule.subset_span ⟨k, rfl⟩⟩
    let coeff : I → ℝ := fun i ↦ bas.repr x i
    have hsumP : ∑ i, coeff i • bas i = x := Module.Basis.sum_repr bas x
    have hsumpick : ∑ i, coeff i • f (pick i) = f k := by
      simp_rw [← hpick] at hsumP
      have hmapped := congrArg P.subtype hsumP
      simpa only [map_sum, map_smul, vf, x, Submodule.coe_subtype] using hmapped
    apply (Submodule.mem_span_range_iff_exists_fun ℝ).2
    let c : s → ℝ := fun j ↦ coeff (esEquiv.symm j)
    refine ⟨c, ?_⟩
    rw [← hsumpick]
    exact (Fintype.sum_equiv esEquiv
      (fun i ↦ coeff i • f (pick i))
      (fun j ↦ c j • f j.1) (by
        intro i
        change coeff i • f (pick i) =
          coeff (esEquiv.symm (esEquiv i)) • f (esEquiv i).1
        rw [esEquiv.symm_apply_apply]
        rfl)).symm
  · change (Finset.univ.map e).card = Module.finrank ℝ P
    rw [Finset.card_map, Finset.card_univ, Module.finrank_eq_card_basis bas]

/-- Every finite sum of squares can be compressed to exactly the dimension of the span of its
summand vectors.  This is the finite Gram-rank upper bound needed by the SOS-length argument. -/
theorem exists_compression_to_finrank_span
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (B : LinearMap.BilinMap ℝ V Q) (f : κ → V) :
    ∃ (s : Finset κ) (g : s → V),
      s.card = Module.finrank ℝ (Submodule.span ℝ (Set.range f)) ∧
      sumSquares B g = sumSquares B f := by
  obtain ⟨s, hspan, hcard⟩ := exists_basis_subfamily f
  obtain ⟨g, hsum⟩ := compress_to_spanning_subfamily B f
    (Function.Embedding.subtype fun k : κ ↦ k ∈ s) hspan
  exact ⟨s, g, hcard, hsum⟩

end SOSCompression
