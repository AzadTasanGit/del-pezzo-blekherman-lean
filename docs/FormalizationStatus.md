# Formalization status

Source: *A Del Pezzo--Blekherman Separation Theorem for Arithmetically
Gorenstein Varieties of Quadratic Deficiency One* (corrected note, August 2026).

The project uses Lean `v4.33.0-rc2` and mathlib `v4.33.0-rc2`
(`51e6992efd06126df61a496bebf8f49482a4e129`).

## Representation decision

Two encodings were compared before implementation:

1. A literal scheme-theoretic model using `Proj`, finite morphisms, graded canonical
   modules, and real/complex base change.
2. A layered model: prove the finite-dimensional bilinear-form and evaluation-fiber
   arguments over explicit finite-dimensional vector spaces first; represent the
   graded Gorenstein mechanism algebraically; connect these to schemes only in a
   separately audited geometric bridge.

The second is used. It preserves the distinctions among quadratic sections,
degree-two functionals, associated Hankel bilinear forms, radicals, and abstract
evaluation data, while avoiding making the already independent linear-algebra
theorems wait on the geometric bridge.

## Statement correspondence

| PDF result | Lean declaration/module | Status | Gaps or extra assumptions | Placeholders |
|---|---|---|---|---|
| Proposition 2.1 (Hilbert-series consequences) | `hilbertDegreeOne`, `hilbertDegreeTwo`, `quadratic_deficiency_one_twice`, `hilbert_numerator_at_one`, `gorenstein_a_invariant_arithmetic` in `Algebra.HilbertArithmetic` | coefficient arithmetic proved | connecting a graded ring's Hilbert series to dimensions, multiplicity, and canonical modules remains; mathlib lacks packaged Hilbert-series/canonical-module APIs | none |
| Proposition 2.2 (regular reductions) | `Algebra.PerfectPairing` (linear-algebra conclusion) | compiling with dependency | perfect-pairing kernel/rank conclusion proved; derivation from regular reduction and Gorenstein hypotheses remains because mathlib has no Cohen--Macaulay/Gorenstein API | none; explicit interface hypotheses only |
| Proposition 3.1 (closed SOS cone and dual) | `finiteSumCone_closed_fullDimensional_dual_of_separating_evaluations` and supporting Gram results | closedness, convexity, nonempty interior, and exact dual identity proved from Gram compatibility, degree-two spanning, and separation by real evaluations | instantiating those interfaces from the homogeneous coordinate ring and Zariski-dense real locus remains | none; interface hypotheses are explicit |
| Lemma 3.2 (kernel-face criterion) | `kernel_face_criterion` and supporting declarations in `LinearAlgebra.KernelFace` / `LinearAlgebra.DiagonalDomination` | proved | stated for a finite-dimensional normed real space and a subspace consisting of symmetric forms, equivalent to the paper's finite-dimensional setting | none |
| Corollary 3.3 / Lemma 4.1 (evaluation rays and dichotomy) | `rankOne_spansExtremeRay`, `extreme_psd_evaluation_xor_basepointFree` | abstract evaluation extremality and the exclusive “positive evaluation ray xor basepoint-free radical” dichotomy proved | identifying the geometric Hankel subspace and its point-evaluation family remains | none |
| Lemmas 4.1--4.2 and Theorem 4.3 | `extreme_psd_evaluation_or_basepointFree`, `kernel_dimension_and_rank_from_perfect_quotient`, `hankelKernel_eq_parameterSpan_and_rank_of_submoduleProductMultiplication` | compiling with dependency | for a commutative coordinate algebra and degree-one submodule `U`, Lean constructs the canonical multiplication into `U * U`, proves symmetry and symmetric-square surjectivity internally, and combines these with pointwise kernel membership of an independent `(m+1)`-parameter tuple. The remaining quotient input is the intrinsic one-dimensional perfect multiplication pairing in `ParameterProductPerfectPairingCertificate`, matching Proposition 2.2; identifying the concrete `R₂` with `R₁ * R₁` and producing the parameters/certificate from the PDF's AG/CM hypotheses remain | none; additional hypotheses are explicit |
| Proposition 5.1 | `vanishes_on_ker_iff_eq_smul`, `exists_projective_evaluation_omitting_hyperplane`, `interior_mvPolynomial_zeroSet_eq_empty`, `dense_compl_of_subset_mvPolynomial_zeroSet`, `surjective_of_dense_fiber_pair_bounds` plus planned geometric bridge | common-zero/projective-fiber linear algebra, construction of the omitted algebraic projective point, density of real principal opens/proper algebraic complements, continuous compact-image reduction, and the dense-reduced-locus perturbation logic proved | construction of the scheme morphism, its finiteness and degree, topological realization/continuity of the real projectivized evaluation map, and production of a nonzero equation cutting out the nonreduced-fiber locus remain | none |
| Proposition 5.2 (reduced-section evaluation) | `injective_finrank_eq_sub_one_has_hyperplane_range`, `evaluationLinearEquivOfInjective`, `relation_coefficients_ne_zero_of_radical_line` in `Fiber.EvaluationAlgebra` | finite-dimensional consequences proved | saturation, reduced-point evaluation injectivity, and Gorenstein pairing derivation remain | none |
| Proposition 5.3 | explanatory remark | no formal statement required | Cayley--Bacharach interpretation only | none |
| Proposition 5.4 (evaluation representation) | `linearFunctional_coordinate_representation`, `linearFunctional_coordinate_representation_unique`, `linearFunctional_eq_smul_of_ker_le`, `scalar_real_of_conjugation_fixed_vectors` | finite coordinate representation, uniqueness, hyperplane-annihilator, and real-scalar mechanisms proved | geometric quotient/fiber instantiation remains | none |
| Lemma 6.1 (hyperplane inertia bound) | `hyperplane_inertia_bound` | proved | none | none |
| Proposition 6.2 (at most one conjugate pair) | `complexDiagonal_at_most_one_pair` in `Fiber.MultipleComplex` | finite-dimensional inertia core proved | geometric/evaluation representation of a reduced fiber remains | none |
| Lemma 7.1 (real diagonal hyperplane) | `diagonal_kernel_face_classification` and supporting declarations in `Fiber.RealDiagonal` | proved in kernel-face form | uses mapped radical equality to the explicit reciprocal line, which is the paper's stated radical conclusion; no geometric assumptions | none |
| Lemma 7.3 (Lorentzian hyperplane) | `lorentz_kernel_face_classification` and supporting declarations in `Fiber.Lorentzian` | proved in kernel-face form | all real diagonal coefficients are assumed positive, exactly as in Lemma 7.3; no geometric assumptions | none |
| Theorem 7.2 (real fiber classification/converse) | `diagonal_kernel_face_classification` | finite-dimensional coefficient core proved | evaluation-fiber/geometric bridge remains | none |
| Theorem 7.4 (one-pair classification/converse) | `lorentz_one_pair_kernel_face_classification`, `normalized_complex_coefficient_real_part_negative` | finite-dimensional coefficient core proved | evaluation-fiber/geometric bridge and normalization assembly remain | none |
| Lemma 8.1 (extreme supporting functionals) | `extremePoint_normalizedSlice_spansExtremeRay`, `spansExtremeRay_extremePoint_normalizedSlice`, `exists_extreme_dual_neg_of_not_mem_closed_convex_cone`, `exists_extreme_dual_eq_zero_of_mem_frontier_closed_convex_cone` | proved for finite-dimensional closed convex cones with nonempty interior, including the extreme-point/extreme-ray equivalence | hypotheses are the explicit abstract cone assumptions used in the paper | none |
| Theorem 8.2 (complete separation) | `complete_extreme_separation_of_evaluation_dichotomy` in `Convexity.FinalSeparation` | point-evaluation-specialized final convex assembly proved conditionally | the geometric Hankel identification and basepoint-free dimension/rank branch must be instantiated | none; additional interface hypotheses explicit |
| Theorem 8.3 (strictly positive boundary SOS) | `sosLength`, `boundary_extreme_support_good_of_ray_dichotomy`, `exists_minimalSquareRepresentation_length_eq_of_fiber_pair_data`, and their supporting lemmas | complete conditional exact-length assembly proved, including the literal equation `sosLength sq p = m+1`; the final theorem directly accepts explicit compact-source, continuous-map, dense-good-locus, omitted-point, degree, and pair-count data | only the scheme construction/instantiation of the finite kernel morphism, topological continuity/compact-source realization, a nonzero discriminant equation for its reduced locus, and degree-`c+2` fibers remain | none; all remaining geometric inputs are explicit |

Current global count: **0 `sorry`, 0 `admit`, 0 custom `axiom` declarations**.

## Fully machine-checked declarations currently available

- `hyperplane_inertia_bound` (PDF Lemma 6.1).
- `psd_eq_zero_iff_mem_ker` and `kernel_face_extreme_of_unique` (Cauchy--Schwarz
  radical fact and the kernel-uniqueness-to-extremality half of Lemma 3.2).
- `exists_diagonal_domination_of_posDef`,
  `exists_two_sided_psd_perturbation`, and `kernel_face_criterion` (the compact-sphere
  domination argument, radical-complement perturbation, and full Lemma 3.2).
- `rankOneBilin_isPosSemidef`, `rankOneBilin_unique_of_symmetric_space`, and
  `rankOne_spansExtremeRay` (generic extremality of nonzero rank-one evaluation
  forms, the abstract linear-algebra content of Corollary 3.3).
- `extreme_psd_eq_pos_smul_rankOne_of_ker_le` and
  `extreme_psd_evaluation_xor_basepointFree` (the exclusive
  basepoint/evaluation dichotomy of Lemma 4.1).
- `map_ker_restrict_eq_inf_orthogonal` and
  `hyperplane_restriction_radical_span` (common radical mechanism for Lemmas 7.1/7.3).
- `ker_eq_of_complement_restrict_nondegenerate`,
  `finrank_ker_eq_of_perfect_quotient`, `rank_from_perfect_quotient`, and
  `kernel_dimension_and_rank_from_perfect_quotient`
  (the perfect Gorenstein pairing conclusion used in Theorem 4.3).
- `socleFunctional_injective`,
  `nondegenerate_soclePairing_of_nonzero_functional`, and
  `parameterSpace_finrank_and_hankelRank_of_nonzeroHankel` (the specific nonzero
  functional induced on the one-dimensional socle yields the actual perfect Hankel
  pairing, radical dimension `m+1`, and rank `c`, with no auxiliary socle coordinate).
- `hankelForm_eq_pullbackQuotient_of_factorization` and
  `hankelKernel_eq_parameterSpace_and_finrank_and_rank_of_factorization` (a pointwise
  quotient-multiplication factorization identifies the original ambient Hankel form with
  the pullback and computes its actual radical as the parameter space, of dimension
  `m+1`, with rank `c`).
- `quotientMultiplication`, `descendedSocleFunctional`, and
  `hankelKernel_eq_parameterSpace_and_finrank_and_rank_of_ambientMultiplication` (products
  in `W * R₁` landing in the explicit degree-two relation space `J`, together with
  `ell(J)=0`, construct the quotient multiplication and induced functional rather than
  assuming them; the ambient Hankel kernel and rank conclusions then follow).
- `symmetricSquareMultiplication`,
  `tensorProduct_lift_surjective_of_symmetricSquareMultiplication_surjective`,
  `hankelForm_ne_zero_of_symmetricSquareMultiplication_surjective`, and
  `hankelKernel_eq_parameterSpace_and_finrank_and_rank_of_degreeTwoGenerated` (surjectivity
  of the PDF's multiplication `Sym²(R₁) → R₂` implies surjectivity of the tensor-linearized
  map and turns the paper's assumption `ell ≠ 0` into nonzeroness of the associated Hankel
  form, eliminating that separate input from the ambient endpoint).
- `parameterProductSubmodule`, `parameterProductSubmodule_le_ker_functional`, and
  `hankelKernel_eq_parameterSpace_and_finrank_and_rank_of_parameterProductSubmodule` (the
  degree-two part of the ideal generated by `W` is the canonical span of `W·R₁`; containment
  of `W` in the Hankel radical proves `ell` annihilates this span, eliminating the supplied
  relation space and its annihilation hypothesis).
- `finrank_quotient_eq_of_parameterSpace_finrank`,
  `ParameterProductGorensteinCertificate`, and
  `hankelKernel_eq_parameterSpace_and_rank_of_gorensteinCertificate` (the parameter-space
  dimension `m+1` now derives the degree-one quotient dimension `c`; the remaining
  Proposition 2.2 interface consists exactly of the canonical quotient's one-dimensional
  degree-two socle and its annihilator property).
- `ParameterProductPerfectPairingCertificate.scalarPairing_nondegenerate`,
  `ParameterProductPerfectPairingCertificate.toGorensteinCertificate`, and
  `hankelKernel_eq_parameterSpace_and_rank_of_perfectPairingCertificate` (the perfect scalar
  pairing is derived from the intrinsic socle-valued perfect Gorenstein multiplication; the
  latter directly gives the zero-annihilator property and feeds the strongest endpoint).
- `hankelKernel_eq_parameterSpace_and_rank_of_linearIndependentParameters` (the chosen
  parameter space is explicitly the span of a linearly independent `Fin (m+1)` family, so Lean
  derives its dimension instead of accepting `dim W=m+1` as a separate numerical hypothesis).
- `hankelKernel_eq_parameterSpan_and_rank_of_parameters_mem_hankelKernel` (the paper's
  pointwise facts `fᵢ ∈ ker Q_ell` now derive the required inclusion of their whole span; the
  conclusion identifies that span with the full Hankel kernel and computes rank `c`).
- `submoduleProductMultiplication`, `submoduleProductMultiplication_symmetric`,
  `symmetricSquare_submoduleProductMultiplication_surjective`, and
  `hankelKernel_eq_parameterSpan_and_rank_of_submoduleProductMultiplication` (actual
  multiplication of a degree-one submodule in a commutative algebra automatically supplies the
  symmetry and degree-two generation hypotheses used by the abstract endpoint).
- The degree-one/degree-two coefficient formulas, quadratic-deficiency polynomial
  identity, numerator-at-one degree calculation, and `a`-invariant arithmetic from
  Proposition 2.1 (`Algebra.HilbertArithmetic`).
- The real reciprocal identities, exact radical line, inertia sign bound, weighted
  Cauchy--Schwarz converse, and the combined theorem
  `diagonal_kernel_face_classification` (finite-dimensional content of Lemma 7.1).
- The mixed real/complex relation and reciprocal identities, exact radical line,
  complex null inequality, weighted Cauchy--Schwarz converse, and
  `lorentz_kernel_face_classification` (finite-dimensional content of Lemma 7.3).
- `complexSquareBilin_exists_negative`,
  `lorentz_real_coefficients_positive_of_psd`, and
  `lorentz_one_pair_kernel_face_classification` (the coefficient-sign and reciprocal
  classification core for Theorem 7.4).
- `complexDiagonal_at_most_one_pair` (the at-most-one-conjugate-pair linear-algebra
  conclusion of Proposition 6.2 for arbitrary hyperplane functionals).
- The expected-dimension evaluation hyperplane/isomorphism lemmas and
  `relation_coefficients_ne_zero_of_radical_line` (finite-dimensional conclusions
  of Proposition 5.2, including Cayley--Bacharach coefficient nonvanishing).
- `linearFunctional_eq_smul_of_ker_le` (the one-dimensional annihilator mechanism
  producing the proportional weight vector in Proposition 5.4).
- `vanishes_on_ker_iff_eq_smul` (the common zero set of a hyperplane of
  sections is exactly the projective fiber determined by its quotient functional).
- `no_evaluation_eq_smul_of_ker_basepointFree` and
  `exists_projective_evaluation_omitting_hyperplane` (a basepoint-free hyperplane
  constructs an actual point in mathlib's algebraic projectivization omitted by
  the projectivized evaluation map).
- `linearFunctional_coordinate_representation` and its uniqueness theorem (the
  weighted finite-coordinate expansion supplied by degree-two evaluation).
- `scalar_real_of_conjugation_fixed_vectors` (conjugation compatibility forces the
  proportionality scalar in Proposition 5.4 to be real).
- `exists_extremePoint_isMinOn` (the compact exposed-face and Krein--Milman step
  used to select an extreme supporting functional in Lemma 8.1).
- `extremePoint_normalizedSlice_spansExtremeRay` (normalizing conical
  decompositions turns extreme points of a slice into extreme rays).
- `normalizedDualSlice_isCompact_of_mem_interior`,
  `exists_dual_neg_of_not_mem_closed_convex_cone`, and
  `exists_dual_eq_zero_of_mem_frontier_closed_convex_cone` (compact dual-slice
  normalization and the two Hahn--Banach support orientations in Lemma 8.1).
- `exists_extreme_dual_neg_of_not_mem_closed_convex_cone` and
  `exists_extreme_dual_eq_zero_of_mem_frontier_closed_convex_cone` (the strict
  outside-point and vanishing boundary-point conclusions of Lemma 8.1).
- `nonnegative_on_finiteSumCone_iff` (the exact algebraic dual identity in
  Proposition 3.1 for an arbitrary square map).
- `isClosed_image_of_closed_cone_ker_eq_zero`,
  `finiteSumCone_eq_image_realGramCone`, and
  `finiteSumCone_isClosed_of_gram_of_spanning_evaluations` (the properness,
  PSD factorization, and real-evaluation density mechanisms for closedness in
  Proposition 3.1).
- `span_evaluations_eq_top_of_functionals_separate` and
  `finiteSumCone_closed_fullDimensional_dual_of_separating_evaluations` (the
  finite consequence of Zariski-density separation and the resulting full
  Proposition 3.1 package).
- `finiteSumCone_closed_fullDimensional_dual` (the combined abstract Gram-model
  version of all four conclusions of Proposition 3.1).
- `two_re_inv_mk` and `normalized_complex_coefficient_real_part_negative`
  (the final normalization and `α < 0` conclusion in Theorem 7.4).
- `complete_extreme_separation_of_ray_dichotomy` and
  `boundary_extreme_support_good_of_ray_dichotomy` (the final convex assemblies
  of Theorems 8.2 and 8.3 once the geometric ray dichotomy is supplied).
- `complete_extreme_separation_of_evaluation_dichotomy` and
  `boundary_extreme_support_good_of_evaluation_dichotomy` (the corresponding
  specializations to positive scalar multiples of point evaluations).
- `supported_psd_gram_finrank_le` (a supporting dual functional confines every
  representing PSD Gram matrix to its nullspace, giving the upper rank bound in
  Theorem 8.3).
- `support_vanishes_on_each_square` and the conjugate-pair cardinality lemmas in
  `Fiber.ConjugatePairs` (the summand-nullity and terminal finite combinatorics
  in Theorem 8.3).
- `gramOfFamily_posSemidef`, `map_gramOfFamily`, and
  `finrank_range_gramOfFamily_le_card` (an `r`-square representation produces a
  representing PSD Gram matrix of rank at most `r`).
- `posSemidef_eq_sum_rankOneGram_nonzero_eigenvectors`,
  `exists_gramFamily_card_eq_finrank_of_posSemidef`, and
  `exists_squareRepresentation_card_eq_finrank_of_posSemidef_gram` (spectral
  decomposition into exactly rank-many squares, completing the Gram-rank/SOS-
  length equivalence).
- `exists_squareRepresentation_card_le_of_supported` (a supported boundary SOS
  has an explicit representation by at most the nullspace dimension, hence by
  at most `m+1` squares in the paper's setting).
- `exists_isMinimalSquareRepresentation_of_mem_finiteSumCone` and
  `exists_minimalSquareRepresentation_card_le_of_supported` (well-ordering
  produces a shortest SOS representation; under support it lies in the nullspace
  and has length at most its dimension).
- `sosLength`, `exists_squareRepresentation_sosLength_of_mem_finiteSumCone`, and
  `sosLength_eq_of_isMinimalSquareRepresentation` (a literal natural-number SOS
  length, realized on the cone and equal to the size of every shortest family).
- `linearIndependent_of_isMinimalSquareRepresentation` (spectral replacement of
  a dependent Gram family would strictly shorten it).
- `exists_finrank_eq_containing_of_linearIndependent` and its prescribed-nullspace
  and minimal-SOS variants (a putative shortest family of length at most `m` in an
  `(m+1)`-dimensional nullspace extends to an `m`-plane inside that nullspace).
- `exists_mem_dense_not_mem_compact` and
  `compact_eq_univ_of_dense_fiber_pair_bounds`, together with the continuous-map
  specialization `surjective_of_dense_fiber_pair_bounds` (the Euclidean
  perturbation from a point outside the compact real image to a reduced fiber,
  followed by the at-least-two versus at-most-one conjugate-pair contradiction).
- `interior_mvPolynomial_zeroSet_eq_empty`, `dense_mvPolynomial_ne_zero`, and
  `dense_compl_of_subset_mvPolynomial_zeroSet` (a proper real algebraic subset
  cut out by a nonzero polynomial has empty Euclidean interior and dense
  complement, supplying the analytic density sentence in the PDF).
- `exists_minimalSquareRepresentation_length_eq_of_geometric_obstruction` (the
  complete conditional Theorem 8.3 length assembly: strict positivity turns a
  hypothetical short SOS into a basepoint-free `m`-plane, contradicting the sole
  remaining geometric obstruction, and hence proves the literal equality
  `sosLength sq p = m+1`).
- `IsBasepointFreeForEvaluation` and
  `no_basepointFree_submodule_of_dense_fiber_pair_bounds` (the opaque geometric
  obstruction is itself derived from a compact continuous real map, a dense good
  locus, an omitted point associated to each basepoint-free plane, and the
  incompatible lower/upper conjugate-pair bounds).
- `exists_minimalSquareRepresentation_length_eq_of_fiber_pair_data` (the expanded
  conditional Theorem 8.3 statement, obtaining exact SOS length directly from
  the explicit finite-fiber data rather than a prepackaged obstruction).

## Proof dependency graph

```text
Hilbert series -> Props. 2.1, 2.2 -> Thm. 4.3 -> Prop. 5.1
                         |              |            |
                         |              +------> Prop. 5.2 -> Prop. 5.4
                         |                               |          |
Prop. 3.1 -> Lemma 3.2 -> Cor. 3.3 / Lemma 4.1        |          +-> Prop. 6.2
     |                                                   |                 |
     +-> Lemma 8.1 -> Thm. 8.2                           +-> Lemmas 7.1/7.3
                                                            -> Thms. 7.2/7.4
Prop. 5.1 + Prop. 6.2 + Lemma 8.1 -------------------------------> Thm. 8.3
```
