import ProjectiveBasepointScratch
import SOSLengthExactScratch
import Mathlib.Topology.Separation.Hausdorff

noncomputable section

universe u v w z t

open scoped BigOperators
open Finset

namespace SOSKernelLength

/-- A dense subset meets the complement of a compact image whenever that complement is nonempty.
This is the topological perturbation step in the proof of Theorem 8.3. -/
theorem exists_mem_dense_outside_compact_range
    {X : Type z} {Y : Type t} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [T2Space Y]
    (phi : X → Y) (hphi : Continuous phi) (Omega : Set Y) (hOmega : Dense Omega)
    (y₀ : Y) (hy₀ : y₀ ∉ Set.range phi) :
    ∃ y, y ∈ Omega ∧ y ∉ Set.range phi := by
  have hcompact : IsCompact (Set.range phi) := by
    rw [← Set.image_univ]
    exact isCompact_univ.image hphi
  have hopen : IsOpen ((Set.range phi)ᶜ) := hcompact.isClosed.isOpen_compl
  obtain ⟨y, hyOmega, hycompl⟩ := hOmega.exists_mem_open hopen ⟨y₀, hy₀⟩
  exact ⟨y, hyOmega, hycompl⟩

/-- A reduced conjugation-stable fiber of size at least three, with at most one conjugate pair,
must contain a real point. -/
theorem real_count_pos_of_total_eq_add_two_and_pair_le_one
    {c realCount pairCount : ℕ} (hc : 1 ≤ c)
    (hcount : c + 2 = realCount + 2 * pairCount) (hpairs : pairCount ≤ 1) :
    0 < realCount := by
  omega

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [Module.Finite ℝ V]
variable {Q : Type w} [AddCommGroup Q] [Module ℝ Q]

/-- The exact perturbation lower bound from the PDF.  A hypothetical representation by at most
`m` squares determines a projective target direction missing from the real image.  Compactness
gives an open neighborhood outside the image; density of the reduced-fiber locus produces a
reduced real fiber there.  Its count formula and the at-most-one-pair theorem force a real point,
a contradiction. -/
theorem boundary_sos_length_ge_add_one_of_reduced_fiber_perturbation
    {X : Type z} {Y : Type t}
    [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y] [T2Space Y]
    (evalV : X → Module.Dual ℝ V) (evalQ : X → Q →ₗ[ℝ] ℝ)
    (mul : LinearMap.BilinMap ℝ V Q)
    (hevalMul : ∀ x f, evalQ x (mul f f) = (evalV x f) ^ 2)
    (ell : Q →ₗ[ℝ] ℝ) (B : LinearMap.BilinForm ℝ V)
    (hPSD : B.IsPosSemidef) (hB : ∀ x y, B x y = ell (mul x y))
    (p : Q) (hpositive : ∀ x, 0 < evalQ x p) (hsupport : ell p = 0)
    (phi : X → Y) (hphi : Continuous phi)
    (pointOf : { psi : Module.Dual ℝ (LinearMap.ker B) // psi ≠ 0 } → Y)
    (hpoint : ∀ x psi, phi x = pointOf psi ↔
      ∃ a : ℝ, a ≠ 0 ∧
        ProjectiveBasepoint.restrictedEval evalV (LinearMap.ker B) x = a • psi.1)
    (Omega : Set Y) (hOmega : Dense Omega)
    (realCount pairCount : Y → ℕ) {c : ℕ} (hc : 1 ≤ c)
    (hcount : ∀ y ∈ Omega, c + 2 = realCount y + 2 * pairCount y)
    (hpairs : ∀ y ∈ Omega, pairCount y ≤ 1)
    (hrealCountZero : ∀ y ∈ Omega, y ∉ Set.range phi → realCount y = 0)
    {m : ℕ} (hker : Module.finrank ℝ (LinearMap.ker B) = m + 1)
    {ι : Type v} [Fintype ι] (f : ι → V)
    (hrep : p = ∑ i, mul (f i) (f i)) :
    m + 1 ≤ Fintype.card ι := by
  by_contra hnot
  have hcard : Fintype.card ι ≤ m := by omega
  have hsupport' : ell (∑ i, mul (f i) (f i)) = 0 := by
    rw [← hrep]
    exact hsupport
  have hsum : ∑ i, B (f i) (f i) = 0 :=
    hankel_sum_eq_zero (fun x y ↦ mul x y) ell B hB f hsupport'
  have hfker : ∀ i, f i ∈ LinearMap.ker B :=
    each_mem_ker_of_sum_apply_self_eq_zero B hPSD f hsum
  let fW : ι → LinearMap.ker B := fun i ↦ ⟨f i, hfker i⟩
  let S : Submodule ℝ (LinearMap.ker B) := Submodule.span ℝ (Set.range fW)
  have hfinrankS : Module.finrank ℝ S ≤ Fintype.card ι := by
    exact finrank_range_le_card fW
  have hS : S < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro htop
    have hfinrankTop : Module.finrank ℝ (LinearMap.ker B) = Module.finrank ℝ S := by
      exact (LinearEquiv.ofTop S htop).finrank_eq.symm
    omega
  obtain ⟨psi, hpsi, hpsiS⟩ :=
    ProjectiveBasepoint.exists_nonzero_annihilator S hS
  let psi₀ : { psi : Module.Dual ℝ (LinearMap.ker B) // psi ≠ 0 } := ⟨psi, hpsi⟩
  have hnoCommonZero : ∀ x : X, ∃ i, evalV x (f i) ≠ 0 :=
    no_common_zero_of_strictlyPositive_sos evalV evalQ (fun x y ↦ mul x y)
      hevalMul p hpositive f hrep
  have hy₀ : pointOf psi₀ ∉ Set.range phi := by
    rintro ⟨x, hx⟩
    obtain ⟨a, ha, heval⟩ := (hpoint x psi₀).mp hx
    obtain ⟨i, hi⟩ := hnoCommonZero x
    have hfiS : fW i ∈ S := Submodule.subset_span ⟨i, rfl⟩
    have hzero : psi (fW i) = 0 := hpsiS (fW i) hfiS
    have happ := LinearMap.congr_fun heval (fW i)
    apply hi
    change evalV x (f i) = a * psi (fW i) at happ
    rw [hzero, mul_zero] at happ
    exact happ
  obtain ⟨y, hyOmega, hyoutside⟩ :=
    exists_mem_dense_outside_compact_range phi hphi Omega hOmega (pointOf psi₀) hy₀
  have hrealPos : 0 < realCount y :=
    real_count_pos_of_total_eq_add_two_and_pair_le_one hc
      (hcount y hyOmega) (hpairs y hyOmega)
  rw [hrealCountZero y hyOmega hyoutside] at hrealPos
  omega

/-- Full abstract version of Theorem 8.3: finite Gram compression gives the upper bound, while
the reduced-fiber perturbation theorem gives the lower bound for every representation. -/
theorem boundary_sos_has_exact_minimal_length_of_reduced_fiber_perturbation
    {X : Type z} {Y : Type t}
    [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y] [T2Space Y]
    (evalV : X → Module.Dual ℝ V) (evalQ : X → Q →ₗ[ℝ] ℝ)
    (mul : LinearMap.BilinMap ℝ V Q)
    (hevalMul : ∀ x f, evalQ x (mul f f) = (evalV x f) ^ 2)
    (ell : Q →ₗ[ℝ] ℝ) (B : LinearMap.BilinForm ℝ V)
    (hPSD : B.IsPosSemidef) (hB : ∀ x y, B x y = ell (mul x y))
    (p : Q) (hpositive : ∀ x, 0 < evalQ x p) (hsupport : ell p = 0)
    (phi : X → Y) (hphi : Continuous phi)
    (pointOf : { psi : Module.Dual ℝ (LinearMap.ker B) // psi ≠ 0 } → Y)
    (hpoint : ∀ x psi, phi x = pointOf psi ↔
      ∃ a : ℝ, a ≠ 0 ∧
        ProjectiveBasepoint.restrictedEval evalV (LinearMap.ker B) x = a • psi.1)
    (Omega : Set Y) (hOmega : Dense Omega)
    (realCount pairCount : Y → ℕ) {c : ℕ} (hc : 1 ≤ c)
    (hcount : ∀ y ∈ Omega, c + 2 = realCount y + 2 * pairCount y)
    (hpairs : ∀ y ∈ Omega, pairCount y ≤ 1)
    (hrealCountZero : ∀ y ∈ Omega, y ∉ Set.range phi → realCount y = 0)
    {m : ℕ} (hker : Module.finrank ℝ (LinearMap.ker B) = m + 1)
    {κ : Type v} [Fintype κ] [DecidableEq κ] (f : κ → V)
    (hrep : p = ∑ i, mul (f i) (f i)) :
    ∃ (s : Finset κ) (g : s → V),
      s.card = m + 1 ∧
      p = ∑ i, mul (g i) (g i) ∧
      ∀ {ι : Type v} [Fintype ι] (h : ι → V),
        p = ∑ i, mul (h i) (h i) → m + 1 ≤ Fintype.card ι := by
  have hsupport' : ell (∑ i, mul (f i) (f i)) = 0 := by
    rw [← hrep]
    exact hsupport
  have hsum : ∑ i, B (f i) (f i) = 0 :=
    hankel_sum_eq_zero (fun x y ↦ mul x y) ell B hB f hsupport'
  have hfker : ∀ i, f i ∈ LinearMap.ker B :=
    each_mem_ker_of_sum_apply_self_eq_zero B hPSD f hsum
  have hspanle : Submodule.span ℝ (Set.range f) ≤ LinearMap.ker B := by
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact hfker i
  obtain ⟨s, g, hcard, hcompress⟩ :=
    SOSCompression.exists_compression_to_finrank_span mul f
  have hrep' : p = ∑ i, mul (g i) (g i) := by
    rw [hrep]
    exact hcompress.symm
  have hlower : m + 1 ≤ s.card :=
    by
      simpa only [Fintype.card_coe] using
        boundary_sos_length_ge_add_one_of_reduced_fiber_perturbation
          evalV evalQ mul hevalMul ell B hPSD hB p hpositive hsupport phi hphi
          pointOf hpoint Omega hOmega realCount pairCount hc hcount hpairs hrealCountZero
          hker g hrep'
  have hupper : s.card ≤ m + 1 := by
    rw [hcard, ← hker]
    exact Submodule.finrank_mono hspanle
  have hcard' : s.card = m + 1 := by omega
  refine ⟨s, g, hcard', hrep', ?_⟩
  intro ι inst h hrepr
  exact boundary_sos_length_ge_add_one_of_reduced_fiber_perturbation
    evalV evalQ mul hevalMul ell B hPSD hB p hpositive hsupport phi hphi
    pointOf hpoint Omega hOmega realCount pairCount hc hcount hpairs hrealCountZero
    hker h hrepr

end SOSKernelLength
