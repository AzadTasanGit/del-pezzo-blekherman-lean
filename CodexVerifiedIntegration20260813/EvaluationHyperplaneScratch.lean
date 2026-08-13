import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import ReciprocalHyperplaneScratch

noncomputable section

universe u v w

open scoped BigOperators
open Finset

namespace EvaluationHyperplane

variable {K : Type u} [Field K]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]

/-- The unique degree-one evaluation relation with coefficient vector `u`. -/
def relation (u : ι → K) : Module.Dual K (ι → K) where
  toFun x := ∑ i, u i * x i
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' r x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    conv_rhs => rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring

@[simp]
theorem relation_apply (u x : ι → K) : relation u x = ∑ i, u i * x i := rfl

@[simp]
theorem relation_single (u : ι → K) (i : ι) (a : K) :
    relation u (Pi.single i a) = u i * a := by
  rw [relation_apply, Finset.sum_eq_single i]
  · simp [Pi.single_apply]
  · intro j hj hji
    simp [Pi.single_apply, hji]
  · simp

theorem relation_ne_zero_of_coeff_ne_zero (u : ι → K) {i : ι} (hi : u i ≠ 0) :
    relation u ≠ 0 := by
  intro hzero
  have hi' := LinearMap.congr_fun hzero (Pi.single i 1)
  apply hi
  simpa only [relation_single, mul_one, LinearMap.zero_apply] using hi'

theorem coeff_ne_zero_iff_single_not_mem_ker (u : ι → K) (i : ι) :
    u i ≠ 0 ↔ Pi.single i 1 ∉ LinearMap.ker (relation u) := by
  rw [LinearMap.mem_ker, relation_single]
  simp

/-- A two-coordinate vector in the relation hyperplane. -/
def pairVector (u : ι → K) (i j : ι) : ι → K :=
  Pi.single i (u j) - Pi.single j (u i)

theorem relation_pairVector (u : ι → K) {i j : ι} (hij : i ≠ j) :
    relation u (pairVector u i j) = 0 := by
  rw [pairVector, map_sub, relation_single, relation_single]
  ring

/-- Products of two pair vectors sharing only coordinate `i` isolate that coordinate. -/
theorem pairVector_mul_pairVector (u : ι → K) {i j k : ι}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    pairVector u i j * pairVector u i k = Pi.single i (u j * u k) := by
  funext q
  by_cases hqi : q = i
  · subst q
    simp [pairVector, Pi.single_apply, hij, hik]
  · by_cases hqj : q = j
    · subst q
      simp [pairVector, Pi.single_apply, hij, hij.symm, hjk]
    · by_cases hqk : q = k
      · subst q
        simp [pairVector, Pi.single_apply, hik, hik.symm, hjk.symm]
      · simp [pairVector, Pi.single_apply, hqi, hqj, hqk]

/-- A finite index set of cardinality at least three supplies the two partners used in the
coordinate-isolation argument. -/
theorem partners_of_three_le_card (hcard : 3 ≤ Fintype.card ι) :
    ∀ i : ι, ∃ j k, i ≠ j ∧ i ≠ k ∧ j ≠ k := by
  classical
  intro i
  obtain ⟨j, hji⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card ι) i
  have hij : i ≠ j := hji.symm
  have hk : ∃ k, i ≠ k ∧ j ≠ k := by
    by_contra h
    have hsub : (Finset.univ : Finset ι) ⊆ {i, j} := by
      intro k hkU
      by_cases hik : i = k
      · simp [← hik]
      · have hjk : j = k := by
          by_contra hjk
          exact h ⟨k, hik, hjk⟩
        simp [← hjk]
    have hle := Finset.card_le_card hsub
    simp [hij] at hle
    omega
  obtain ⟨k, hik, hjk⟩ := hk
  exact ⟨j, k, hij, hik, hjk⟩

/-- Pure linear-algebraic core of Proposition 5.2: when all coefficients of a hyperplane
relation are nonzero and every coordinate has two distinct partners, coordinatewise products of
vectors in the hyperplane span the full function space. -/
theorem coordinateSingles_mem_span_products
    (u : ι → K) (hu : ∀ i, u i ≠ 0)
    (hpartners : ∀ i : ι, ∃ j k : ι, i ≠ j ∧ i ≠ k ∧ j ≠ k) (i : ι) :
    Pi.single i 1 ∈ Submodule.span K
      {z : ι → K | ∃ x y, relation u x = 0 ∧ relation u y = 0 ∧ z = x * y} := by
  obtain ⟨j, k, hij, hik, hjk⟩ := hpartners i
  let x := pairVector u i j
  let y := pairVector u i k
  have hx : relation u x = 0 := relation_pairVector u hij
  have hy : relation u y = 0 := relation_pairVector u hik
  have hxy : x * y = Pi.single i (u j * u k) :=
    pairVector_mul_pairVector u hij hik hjk
  have hmem : x * y ∈ Submodule.span K
      {z : ι → K | ∃ x y, relation u x = 0 ∧ relation u y = 0 ∧ z = x * y} :=
    Submodule.subset_span ⟨x, y, hx, hy, rfl⟩
  have hscalar : u j * u k ≠ 0 := mul_ne_zero (hu j) (hu k)
  have hscaled := (Submodule.span K
      {z : ι → K | ∃ x y, relation u x = 0 ∧ relation u y = 0 ∧ z = x * y}).smul_mem
        ((u j * u k)⁻¹) hmem
  rw [hxy] at hscaled
  have hscaleeq : (u j * u k)⁻¹ • Pi.single i (u j * u k) = Pi.single i 1 := by
    funext q
    by_cases hqi : q = i
    · subst q
      simp [Pi.single_apply, hscalar]
      field_simp [hu j, hu k]
    · simp [Pi.single_apply, hqi]
  rw [hscaleeq] at hscaled
  exact hscaled

theorem span_products_eq_top
    (u : ι → K) (hu : ∀ i, u i ≠ 0)
    (hpartners : ∀ i : ι, ∃ j k : ι, i ≠ j ∧ i ≠ k ∧ j ≠ k) :
    Submodule.span K
      {z : ι → K | ∃ x y, relation u x = 0 ∧ relation u y = 0 ∧ z = x * y} = ⊤ := by
  apply top_unique
  intro z hz
  rw [show z = ∑ i, z i • Pi.single i 1 by
    funext q
    simp [Pi.single_apply]]
  apply Submodule.sum_mem
  intro i hi
  exact Submodule.smul_mem _ _ (coordinateSingles_mem_span_products u hu hpartners i)

theorem span_products_eq_top_of_three_le_card
    (u : ι → K) (hu : ∀ i, u i ≠ 0) (hcard : 3 ≤ Fintype.card ι) :
    Submodule.span K
      {z : ι → K | ∃ x y, relation u x = 0 ∧ relation u y = 0 ∧ z = x * y} = ⊤ :=
  span_products_eq_top u hu (partners_of_three_le_card hcard)

section EvaluationMaps

variable {V₁ : Type w} [AddCommGroup V₁] [Module K V₁]
variable {V₂ : Type*} [AddCommGroup V₂] [Module K V₂]

/-- A relation coefficient is nonzero exactly when the corresponding coordinate delta vector
does not occur as a degree-one evaluation vector. -/
theorem coeff_ne_zero_iff_single_not_mem_range
    (u : ι → K) (eval₁ : V₁ →ₗ[K] (ι → K))
    (hrange : LinearMap.range eval₁ = LinearMap.ker (relation u)) (i : ι) :
    u i ≠ 0 ↔ Pi.single i 1 ∉ LinearMap.range eval₁ := by
  rw [hrange]
  exact coeff_ne_zero_iff_single_not_mem_ker u i

/-- The relation cutting out the degree-one evaluation image is unique up to scalar. -/
theorem unique_relation
    (u μ : ι → K) (eval₁ : V₁ →ₗ[K] (ι → K))
    (hrange : LinearMap.range eval₁ = LinearMap.ker (relation u))
    (hμ : ∀ x, x ∈ LinearMap.range eval₁ → relation μ x = 0) :
    ∃ t : K, relation μ = t • relation u := by
  have hker : LinearMap.ker (relation u) ≤ LinearMap.ker (relation μ) := by
    intro x hx
    apply LinearMap.mem_ker.mpr
    apply hμ x
    rw [hrange]
    exact hx
  obtain ⟨t, ht⟩ := LinearMap.exists_smul_of_ker_le_ker
    (relation u) (relation μ) hker
  exact ⟨t, ht.symm⟩

/-- Coordinate form of uniqueness: every relation coefficient vector is a common scalar
multiple of the distinguished coefficient vector. -/
theorem unique_relation_coefficients
    (u μ : ι → K) (eval₁ : V₁ →ₗ[K] (ι → K))
    (hrange : LinearMap.range eval₁ = LinearMap.ker (relation u))
    (hμ : ∀ x, x ∈ LinearMap.range eval₁ → relation μ x = 0) :
    ∃ t : K, μ = t • u := by
  obtain ⟨t, ht⟩ := unique_relation u μ eval₁ hrange hμ
  refine ⟨t, ?_⟩
  funext i
  have hi := LinearMap.congr_fun ht (Pi.single i 1)
  simpa only [relation_single, LinearMap.smul_apply, smul_eq_mul, mul_one,
    Pi.smul_apply] using hi

/-- If degree-one evaluation identifies its image with the relation hyperplane and degree-two
evaluation respects multiplication, then degree-two evaluation is surjective. -/
theorem eval₂_surjective
    (u : ι → K) (hu : ∀ i, u i ≠ 0)
    (hpartners : ∀ i : ι, ∃ j k : ι, i ≠ j ∧ i ≠ k ∧ j ≠ k)
    (eval₁ : V₁ →ₗ[K] (ι → K)) (eval₂ : V₂ →ₗ[K] (ι → K))
    (mul : V₁ → V₁ → V₂)
    (hrange : LinearMap.range eval₁ = LinearMap.ker (relation u))
    (hmul : ∀ x y, eval₂ (mul x y) = eval₁ x * eval₁ y) :
    Function.Surjective eval₂ := by
  rw [← LinearMap.range_eq_top]
  apply top_unique
  rw [← span_products_eq_top u hu hpartners]
  apply Submodule.span_le.mpr
  rintro z ⟨x, y, hx, hy, rfl⟩
  have hx' : x ∈ LinearMap.range eval₁ := by
    rw [hrange]
    exact LinearMap.mem_ker.mpr hx
  have hy' : y ∈ LinearMap.range eval₁ := by
    rw [hrange]
    exact LinearMap.mem_ker.mpr hy
  obtain ⟨x', rfl⟩ := hx'
  obtain ⟨y', rfl⟩ := hy'
  exact ⟨mul x' y', hmul x' y'⟩

theorem eval₂_surjective_of_three_le_card
    (u : ι → K) (hu : ∀ i, u i ≠ 0) (hcard : 3 ≤ Fintype.card ι)
    (eval₁ : V₁ →ₗ[K] (ι → K)) (eval₂ : V₂ →ₗ[K] (ι → K))
    (mul : V₁ → V₁ → V₂)
    (hrange : LinearMap.range eval₁ = LinearMap.ker (relation u))
    (hmul : ∀ x y, eval₂ (mul x y) = eval₁ x * eval₁ y) :
    Function.Surjective eval₂ :=
  eval₂_surjective u hu (partners_of_three_le_card hcard) eval₁ eval₂ mul hrange hmul

/-- Equal dimensions upgrade the preceding surjectivity to a linear equivalence. -/
noncomputable def eval₂LinearEquiv
    [FiniteDimensional K V₂]
    (u : ι → K) (hu : ∀ i, u i ≠ 0)
    (hpartners : ∀ i : ι, ∃ j k : ι, i ≠ j ∧ i ≠ k ∧ j ≠ k)
    (eval₁ : V₁ →ₗ[K] (ι → K)) (eval₂ : V₂ →ₗ[K] (ι → K))
    (mul : V₁ → V₁ → V₂)
    (hrange : LinearMap.range eval₁ = LinearMap.ker (relation u))
    (hmul : ∀ x y, eval₂ (mul x y) = eval₁ x * eval₁ y)
    (hdim : Module.finrank K V₂ = Fintype.card ι) : V₂ ≃ₗ[K] (ι → K) := by
  have hsurj := eval₂_surjective u hu hpartners eval₁ eval₂ mul hrange hmul
  have hdim' : Module.finrank K V₂ = Module.finrank K (ι → K) := by
    simpa [Module.finrank_pi] using hdim
  exact LinearEquiv.ofBijective eval₂
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim').mpr hsurj, hsurj⟩

noncomputable def eval₂LinearEquivOfThreeLeCard
    [FiniteDimensional K V₂]
    (u : ι → K) (hu : ∀ i, u i ≠ 0) (hcard : 3 ≤ Fintype.card ι)
    (eval₁ : V₁ →ₗ[K] (ι → K)) (eval₂ : V₂ →ₗ[K] (ι → K))
    (mul : V₁ → V₁ → V₂)
    (hrange : LinearMap.range eval₁ = LinearMap.ker (relation u))
    (hmul : ∀ x y, eval₂ (mul x y) = eval₁ x * eval₁ y)
    (hdim : Module.finrank K V₂ = Fintype.card ι) : V₂ ≃ₗ[K] (ι → K) :=
  eval₂LinearEquiv u hu (partners_of_three_le_card hcard) eval₁ eval₂ mul hrange hmul hdim

end EvaluationMaps

end EvaluationHyperplane
