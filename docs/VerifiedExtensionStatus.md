# Formalization status supplement (2026-08-13)

This records the results originally developed as a verified extension. The modules are now
integrated into the canonical `DelPezzoBlekherman/` subject hierarchy and the paths referenced by
the integration notes are their current locations.

These files were forced-fresh compiled with Lean `v4.33.0-rc2` and mathlib commit
`51e6992efd06126df61a496bebf8f49482a4e129`.

## Fully machine checked in this supplement

| PDF bridge | Principal Lean declaration | Status |
|---|---|---|
| Basepoint-free degree-one data induces a Proj morphism under radical irrelevant containment | `AlgebraicGeometry.Proj.projectiveAevalOfRadical` | proved |
| Finite graded polynomial-to-coordinate-ring map induces a finite projective morphism | `AlgebraicGeometry.Proj.projectiveAevalOfRadical_isFinite_of_toRingHom_finite` | proved |
| A basis of cardinality `c + 2` gives finiteness and rank `c + 2` | `AlgebraicGeometry.Proj.projectiveAevalOfRadical_isFinite_and_finrank_eq_add_two_of_basis` | proved |
| Reduced algebraically closed fiber has exactly `c + 2` geometric points | `Ideal.natCard_primeSpectrum_fiber_eq_add_two` | proved |
| Discriminant commutes with base change and its nonvanishing makes fibers reduced | `Algebra.map_discr_eq_discr_tensorProduct_basis`, `Ideal.isReduced_fiber_of_discr_not_mem` | proved |
| Generic fiber of an injective finite domain map is a field | `Ideal.isField_genericFiber_of_finite_of_isDomain` | proved |
| In characteristic zero the finite free domain map has nonzero discriminant | `Ideal.discr_ne_zero_of_finite_of_isDomain_of_charZero` | proved |
| An `(1,c,1)` graded free basis gives a finite projective map and a nonempty reduced `c+2`-point fiber locus | `AlgebraicGeometry.Proj.projectiveAevalOfRadical_hVectorOneCOne_fiber_card_eq_add_two` | proved from the explicit certificate |
| The `(1,c,1)` certificate gives a finite surjective kernel morphism of rank `c+2` with nonzero discriminant | `AlgebraicGeometry.Proj.projectiveAevalOfRadical_isFinite_surjective_discr_and_rank_of_hVectorOneCOne` | proved from the explicit certificate |
| Real closed points split into rational points and quadratic/conjugate-pair points | `MaximalSpectrum.equivRationalClosedPointSumQuadraticClosedPoint` | proved |
| Real fiber count is either `c+2` real points or `c` real points plus one pair | `IsArtinianRing.real_reduced_fiber_rational_point_dichotomy` | proved assuming at most one quadratic point |
| Exact reduced-real-fiber count formula `length = #real + 2·#pairs` | `IsArtinianRing.real_finrank_eq_rationalClosedPoint_add_two_mul_quadraticClosedPoint` | proved |
| Rank `c+2`, `c≥1`, and at most one pair force a real point | `IsArtinianRing.exists_rationalClosedPoint_of_finrank_add_two_of_pair_le_one` | proved |
| A reduced constant-rank real fiber family supplies `realCount`/`pairCount` and the exact count equation | `RealFiberFamily.count_eq_add_two_on` | proved |
| Rational fiber points lifting to the real source give zero real count outside its image | `RealFiberFamily.realCount_eq_zero_of_not_mem_range_of_lift` | proved |
| Exact minimal length from an actual reduced finite real fiber family | `SOSKernelLength.boundary_sos_has_exact_minimal_length_of_real_fiber_family` | proved from density, reducedness, rank `c+2`, pair bound, and rational-point lift |
| Concrete real projective coordinate fibers are finite real algebras of rank `c+2` | `RealProjectiveCoordinateFiber.hVector_fiber_finrank_eq_add_two` | proved from base change of the `(1,c,1)` basis |
| Evaluated discriminant nonvanishing makes each coordinate fiber reduced | `RealProjectiveCoordinateFiber.hVector_fiber_isReduced` | proved |
| A dense projective locus admits chosen affine representatives where the discriminant is nonzero, without assuming discriminant homogeneity | `MvPolynomial.dense_setOf_hasGoodCoordinates`, `MvPolynomial.directionOf_goodCoordinates` | proved |
| The resulting `(1,c,1)` good-coordinate fibers have rank `c+2` everywhere and are reduced on that dense locus | `RealProjectiveCoordinateFiber.hVectorGoodFiber_finrank_eq_add_two`, `RealProjectiveCoordinateFiber.hVectorGoodFiber_isReduced` | proved |
| Normalized complex-block nonnegativity and non-isotropy give the pair bound uniformly for the concrete good-fiber family | `RealProjectiveCoordinateFiber.hVectorGoodFiber_pairCount_le_one_of_normalizedComplexBlocks` | proved |
| A rational closed point of a finite fiber yields a real algebra point of the source coordinate ring | `RationalClosedPoint.algHom`, `RealProjectiveCoordinateFiber.sourceAlgHomOfRationalFiberPoint_algebraMap` | proved |
| For good `(1,c,1)` fibers, the lifted source point has exactly the chosen generator coordinates and recovers the original projective direction | `RealProjectiveCoordinateFiber.hVectorSourceAlgHomOfRationalFiberPoint_generator`, `RealProjectiveCoordinateFiber.directionOf_hVectorSourceAlgHomOfRationalFiberPoint_generators` | proved |
| Compatible realization of source algebra points implies zero real-fiber count off the projective image | `RealProjectiveCoordinateFiber.hVectorGoodFiber_realCount_eq_zero_outside_range` | proved |
| For the canonical source of nonzero real algebra points, zero real-fiber count off the generator-direction image is unconditional | `RealProjectiveCoordinateFiber.hVectorGoodFiber_realCount_eq_zero_outside_generatorDirection` | proved |
| A one-dimensional socle plus the Gorenstein annihilator property gives a perfect degree-one pairing | `ArtinianGorensteinDegreeOneCertificate.nondegenerate_soclePairing_of_annihilator` | proved |
| The parameter space has dimension `m+1` and its Hankel form has rank `c` | `ArtinianGorensteinDegreeOneCertificate.parameterSpace_finrank_and_hankelRank_of_socleAnnihilator` | proved from explicit Hilbert-dimension and socle inputs |
| Every nonzero functional on the one-dimensional socle is injective and preserves perfection of the multiplication pairing | `ArtinianGorensteinDegreeOneCertificate.socleFunctional_injective`, `ArtinianGorensteinDegreeOneCertificate.nondegenerate_soclePairing_of_nonzero_functional` | proved |
| The actual nonzero pulled-back Hankel form has radical dimension `m+1` and rank `c`, without choosing a socle coordinate | `ArtinianGorensteinDegreeOneCertificate.parameterSpace_finrank_and_hankelRank_of_nonzeroHankel` | proved from explicit Hilbert dimensions and the socle-annihilator input |
| An ambient Hankel form factoring pointwise through quotient multiplication has actual kernel equal to the parameter space, kernel dimension `m+1`, and rank `c` | `ArtinianGorensteinDegreeOneCertificate.hankelForm_eq_pullbackQuotient_of_factorization`, `ArtinianGorensteinDegreeOneCertificate.hankelKernel_eq_parameterSpace_and_finrank_and_rank_of_factorization` | proved from the explicit quotient multiplication, socle, factorization, and Hilbert-dimension inputs |
| Ambient multiplication and the degree-two functional descend through explicit relation spaces, recovering the original Hankel form and its exact kernel/dimension/rank | `ArtinianGorensteinDegreeOneCertificate.quotientMultiplication`, `ArtinianGorensteinDegreeOneCertificate.descendedSocleFunctional`, `ArtinianGorensteinDegreeOneCertificate.hankelKernel_eq_parameterSpace_and_finrank_and_rank_of_ambientMultiplication` | proved from `W * R₁ ⊆ J`, symmetry, `ell(J)=0`, quotient Hilbert dimensions, and the socle-annihilator input; the factorization is constructed internally |
| A nonzero degree-two functional has nonzero Hankel form when degree two is generated by the PDF's symmetric-square multiplication, yielding the strongest ambient Theorem 4.3 endpoint | `ArtinianGorensteinDegreeOneCertificate.symmetricSquareMultiplication_surjective_iff_tensorProduct_lift_surjective`, `ArtinianGorensteinDegreeOneCertificate.hankelForm_ne_zero_of_symmetricSquareMultiplication_surjective`, `ArtinianGorensteinDegreeOneCertificate.hankelKernel_eq_parameterSpace_and_finrank_and_rank_of_degreeTwoGenerated` | proved from surjectivity of `Sym²(U) → Q`, now shown equivalent to tensor-product generation; the local quotient construction supplies the currently missing mathlib universal property, and no separate Hankel-nonzeroness hypothesis remains |
| The degree-two relation space is canonically `span(W·R₁)`, and radical containment makes the functional descend through it | `ArtinianGorensteinDegreeOneCertificate.parameterProductSubmodule`, `ArtinianGorensteinDegreeOneCertificate.parameterProductSubmodule_le_ker_functional`, `ArtinianGorensteinDegreeOneCertificate.hankelKernel_eq_parameterSpace_and_finrank_and_rank_of_parameterProductSubmodule` | proved; no supplied `J`, product-containment assumption, or separate `ell(J)=0` input remains |
| The chosen parameter span's dimension derives the degree-one quotient dimension, and the remaining AG quotient facts feed one certificate endpoint | `ArtinianGorensteinDegreeOneCertificate.finrank_quotient_eq_of_parameterSpace_finrank`, `ArtinianGorensteinDegreeOneCertificate.ParameterProductGorensteinCertificate`, `ArtinianGorensteinDegreeOneCertificate.hankelKernel_eq_parameterSpace_and_rank_of_gorensteinCertificate` | proved; the certificate exposes exactly socle dimension one and the degree-one annihilator property |
| The PDF's intrinsic socle-valued perfect Gorenstein multiplication implies its scalar form, the annihilator certificate, and the ambient rank theorem | `ArtinianGorensteinDegreeOneCertificate.ParameterProductPerfectPairingCertificate.scalarPairing_nondegenerate`, `ArtinianGorensteinDegreeOneCertificate.ParameterProductPerfectPairingCertificate.toGorensteinCertificate`, `ArtinianGorensteinDegreeOneCertificate.hankelKernel_eq_parameterSpace_and_rank_of_perfectPairingCertificate` | proved; the remaining upstream interface is now exactly the one-dimensional socle and intrinsic perfect multiplication pairing asserted by Proposition 2.2 |
| The zero-annihilator and intrinsic perfect-pairing formulations are equivalent for the symmetric quotient multiplication | `ArtinianGorensteinDegreeOneCertificate.ParameterProductGorensteinCertificate.toPerfectPairingCertificate`, `ArtinianGorensteinDegreeOneCertificate.hankelKernel_eq_parameterSpan_and_rank_of_gorensteinCertificate` | proved; the strongest pointwise and graded endpoints consume the weaker one-dimensional-socle/zero-annihilator certificate directly |
| An explicit independent `(m+1)`-parameter sequence supplies the parameter-space dimension in the strongest Theorem 4.3 endpoint | `ArtinianGorensteinDegreeOneCertificate.hankelKernel_eq_parameterSpace_and_rank_of_linearIndependentParameters` | proved; `W = span(range parameters)` and linear independence derive `dim W=m+1`, removing the bare dimension hypothesis |
| Pointwise membership of the chosen parameters in the Hankel kernel supplies span containment and the final rank endpoint | `ArtinianGorensteinDegreeOneCertificate.hankelKernel_eq_parameterSpan_and_rank_of_parameters_mem_hankelKernel` | proved; the hypotheses now mirror the paper's choice `fᵢ ∈ W_ell`, and Lean identifies their span with the complete kernel |
| Canonical multiplication in a commutative algebra supplies symmetry and symmetric-square generation automatically | `ArtinianGorensteinDegreeOneCertificate.submoduleProductMultiplication_symmetric`, `ArtinianGorensteinDegreeOneCertificate.symmetricSquare_submoduleProductMultiplication_surjective`, `ArtinianGorensteinDegreeOneCertificate.hankelKernel_eq_parameterSpan_and_rank_of_submoduleProductMultiplication` | proved using mathlib's surjective `Submodule.mulMap'`; the ring-theoretic rank endpoint retains only the perfect parameter-quotient pairing and Hilbert/parameter data |
| Equality of the canonical product submodule with the named degree-two piece transports multiplication and the original functional into the rank theorem | `ArtinianGorensteinDegreeOneCertificate.submoduleMultiplicationToDegreeTwo`, `ArtinianGorensteinDegreeOneCertificate.symmetricSquare_submoduleMultiplicationToDegreeTwo_surjective`, `ArtinianGorensteinDegreeOneCertificate.hankelKernel_eq_parameterSpan_and_rank_of_degreeTwo_eq_product` | proved from `U * U = Q`; symmetry and generation are internal, leaving the standard-graded equality and Proposition 2.2 perfect quotient pairing as explicit upstream inputs |
| The PDF's degree-two consequence of standard gradedness proves the product equality and gives a direct graded rank endpoint | `ArtinianGorensteinDegreeOneCertificate.DegreeTwoGeneratedByDegreeOne`, `ArtinianGorensteinDegreeOneCertificate.degreeOne_mul_self_eq_degreeTwo`, `ArtinianGorensteinDegreeOneCertificate.hankelKernel_eq_parameterSpan_and_rank_of_degreeTwoGeneratedByDegreeOne` | proved for internal homogeneous components; the literal hypothesis is surjectivity of `Sym²(R₁) → R₂`, which supplies `R₁ * R₁ = R₂` via the equivalent tensor map, leaving only the Proposition 2.2 zero-annihilator certificate and parameter construction upstream |
| Equation (1) has machine-checked formal-power-series coefficients and supplies degree-one finite-dimensionality and dimension to the graded rank theorem | `DelPezzoBlekherman.delPezzoHilbertSeries`, `DelPezzoBlekherman.coeff_one_delPezzoHilbertSeries`, `DelPezzoBlekherman.coeff_two_delPezzoHilbertSeries`, `DelPezzoBlekherman.DelPezzoHilbertSeriesCertificate.moduleFinite_one`, `ArtinianGorensteinDegreeOneCertificate.hankelKernel_eq_parameterSpan_and_rank_of_hilbertSeriesCertificate` | proved; the remaining interface is construction of `DelPezzoHilbertSeriesCertificate` from the concrete homogeneous coordinate ring because mathlib has no packaged graded Hilbert-series API |
| Successive degree-one reduction recurrences yield the denominator identity, the Artinian Hilbert function `(1,c,1,0,...)`, and the quotient socle dimension in the strongest graded rank endpoint | `DelPezzoBlekherman.DegreeOneReductionComponentExactSequence.toFinrankRelation`, `DelPezzoBlekherman.SuccessiveDegreeOneReductionComponentExactSequences.toArtinianReductionHilbertSeriesCertificateOfInitialEquiv`, `DelPezzoBlekherman.SuccessiveDegreeOneReductionComponentExactSequences.toComponentsRelationOfInitialEquiv`, `DelPezzoBlekherman.SuccessiveLinearReductionComponentsRelation.toArtinianReductionDenominatorRelation`, `ArtinianGorensteinDegreeOneCertificate.ParameterProductGorensteinCertificate.ofArtinianReductionHilbertSeriesCertificate`, `ArtinianGorensteinDegreeOneCertificate.hankelKernel_eq_parameterSpan_and_rank_of_successiveLinearReductions`, `ArtinianGorensteinDegreeOneCertificate.hankelKernel_eq_parameterSpan_and_rank_of_successiveDegreeOneReductionExactSequences` | proved; an indexed degreewise short-exact-sequence family now derives the whole local-recurrence chain despite changing quotient carriers, and directly constructs both Hilbert conclusions and the rank theorem after an explicit degreewise initial equivalence. Constructing the concrete sequences, initial/socle equivalences from the actual regular sequence, and the Gorenstein zero-annihilator property remain explicit upstream inputs |
| Index-one inertia forces at most one complex-conjugate pair | `QuadraticForm.NonrealPairNegativeDirections.card_le_one_of_restrict` | proved once evaluation blocks supply independent negative directions |
| The real reciprocal identity and its converse | `ReciprocalHyperplane.reciprocal_identity_of_radical`, `ReciprocalHyperplane.radical_of_reciprocal_identity` | proved |
| The fully-real sign pattern has exactly one negative coefficient | `ReciprocalHyperplane.ncard_negative_eq_one_of_reciprocal_identity` | proved |
| The one-pair reciprocal identity and its converse | `MixedReciprocalHyperplane.reciprocal_identity_of_radical`, `MixedReciprocalHyperplane.radical_of_reciprocal_identity` | proved |
| The `b=α+βI` normalized real-coordinate identity and `α<0` sign mechanism | `MixedReciprocalHyperplane.reciprocal_identity_mk_iff`, `MixedReciprocalHyperplane.re_neg_of_nonnegative_on_relation_one` | proved, with non-isotropy as the strictness input |
| Negative complex blocks contribute one independent negative direction per conjugate pair | `QuadraticForm.NonrealPairNegativeDirections.ofComplexBlocks` | proved |
| Complex-block relation-kernel nonnegativity gives the exact real-fiber dichotomy | `IsArtinianRing.real_reduced_fiber_rational_point_dichotomy_of_complexBlocks` | proved from the normalized block model |
| Normalized relation-kernel nonnegativity plus block non-isotropy automatically gives the block signs, at most one pair, and the real-fiber dichotomy | `IsArtinianRing.real_reduced_fiber_rational_point_dichotomy_of_normalizedComplexBlocks` | proved |
| The degree-one evaluation relation is unique up to scalar and coefficient nonvanishing has an exact range criterion | `EvaluationHyperplane.unique_relation_coefficients`, `EvaluationHyperplane.coeff_ne_zero_iff_single_not_mem_range` | proved |
| Products of the evaluation hyperplane span the degree-two coordinate algebra | `EvaluationHyperplane.span_products_eq_top_of_three_le_card` | proved for at least three points and nonzero relation coefficients |
| Degree-two evaluation is an isomorphism | `EvaluationHyperplane.eval₂LinearEquivOfThreeLeCard` | proved from evaluation compatibility and equal dimensions |
| A supporting PSD Hankel form forces every boundary-SOS summand into its radical | `SOSKernelLength.each_mem_ker_of_sum_apply_self_eq_zero` | proved |
| Proper-subspace basepoints plus strict positivity force the summands to span the radical | `SOSKernelLength.span_eq_of_no_common_zero` | proved as the exact geometric interface |
| Boundary SOS length is at least `m+1` | `SOSKernelLength.boundary_sos_length_ge_add_one_of_basepoints` | proved from radical dimension `m+1` and the basepoint property |
| Strict positivity supplies the no-common-zero condition for every SOS representation | `SOSKernelLength.no_common_zero_of_strictlyPositive_sos` | proved |
| One explicitly dependent square can be eliminated without changing the represented quadratic datum or span | `SOSCompression.compress_one_extra_explicit_span` | proved by an explicit rank-one square-root update |
| Arbitrary finite Gram data compresses to the finrank of its summand span | `SOSCompression.exists_compression_to_finrank_span` | proved, including finite iteration and basis-subfamily extraction |
| A strictly positive boundary SOS has exact minimal length `m+1` | `SOSKernelLength.boundary_sos_has_exact_minimal_length` | proved from the explicit radical-dimension and proper-subspace basepoint inputs; no short representation is assumed |
| A dense reduced-fiber locus meets the complement of the compact real image | `SOSKernelLength.exists_mem_dense_outside_compact_range` | proved |
| The `c+2` count and at-most-one-pair bound force a real point when `c≥1` | `SOSKernelLength.real_count_pos_of_total_eq_add_two_and_pair_le_one` | proved |
| Boundary SOS length is at least `m+1` by the PDF's reduced-fiber perturbation argument | `SOSKernelLength.boundary_sos_length_ge_add_one_of_reduced_fiber_perturbation` | proved from the exact compactness, density, fiber-count, and projective-evaluation interfaces |
| Exact minimal length by the PDF's perturbation argument | `SOSKernelLength.boundary_sos_has_exact_minimal_length_of_reduced_fiber_perturbation` | proved, including Gram compression for the upper bound |
| Finite-dimensional real projective directions form a compact Hausdorff antipodal quotient, with the usual nonzero-scalar equality relation | `RealProjectiveTopology.directionOf_eq_iff_exists_smul` | proved; normalization and the quotient map are continuous |
| Strict positivity makes restricted radical evaluation nowhere zero | `SOSKernelLength.restrictedEval_ne_zero_of_strictlyPositive_sos` | proved from the supported SOS representation |
| Continuity of ordinary evaluation implies continuity of projective radical evaluation | `SOSKernelLength.continuous_realProjectiveEval` | proved by continuous restriction, normalization, and quotient formation |
| Ordinary evaluation continuity is reducible to continuity on the vectors of any finite basis | `SOSKernelLength.continuous_dual_evaluation_of_continuous_on_basis` | proved |
| A nonzero real multivariate polynomial has Euclidean-dense nonvanishing locus | `MvPolynomial.dense_setOf_eval_ne_zero` | proved by analyticity and the identity theorem |
| Its represented real projective directions are dense | `MvPolynomial.dense_directionOf_image_eval_ne_zero` | proved by density on the punctured vector space and the surjective antipodal quotient |
| The `(1,c,1)` certificate has a dense reduced-fiber discriminant locus over `ℝ` | `AlgebraicGeometry.Proj.dense_real_projective_discr_locus_of_hVectorOneCOne` | proved by composing its checked nonzero discriminant with projective polynomial density |
| A basis transports that dense locus to the Hankel-radical dual coordinate model | `AlgebraicGeometry.Proj.dense_real_projective_discr_locus_basis_of_hVectorOneCOne` | proved for any continuously normed finite-dimensional target |
| Exact minimal SOS length from ordinary evaluation continuity and a dense reduced locus | `SOSKernelLength.boundary_sos_has_exact_minimal_length_of_ordinary_continuity_and_dense_locus` | proved; the certificate theorem separately supplies the required dense locus |
| Exact minimal length with the projective target instantiated concretely | `SOSKernelLength.boundary_sos_has_exact_minimal_length_of_real_projective_perturbation` | proved; the abstract target and ray-identification assumptions have been eliminated |
| Projective evaluation surjectivity implies the proper-subspace basepoint property | `ProjectiveBasepoint.proper_subspace_has_common_zero_of_projective_surjective` | proved as a stronger conditional shortcut, not the route used in the PDF |
| Exact minimal length from projective evaluation surjectivity | `SOSKernelLength.boundary_sos_has_exact_minimal_length_of_projective_surjective` | proved as the corresponding stronger conditional shortcut |
| A point outside a proper cone has a strictly negative supporting functional | `ExtremeSeparator.properCone_separates` | proved via mathlib Farkas separation |
| Negativity on a compact base occurs at an extreme point | `ExtremeSeparator.exists_extremePoint_apply_neg` | proved via an exposed minimizing face and Krein--Milman |
| The SOS dual is exactly the functionals nonnegative on all squares, unchanged by closure | `SOSConeDual.nonnegative_on_sosCone_iff`, `SOSConeDual.nonnegative_on_closure_sosCone_iff` | proved |
| Extreme points of a strictly positive cone base generate extreme rays | `ExtremeRayBase.isExtremeRay_of_extremePoint_base` | proved |
| A negative point of a compact cone base can be replaced by a negative extreme-ray generator | `ExtremeRayBase.exists_extremeRay_apply_neg_of_compact_base` | proved |
| PSD kernel-face criterion | `PSDRangeOneExtreme.ker_add_eq_inf` | proved |
| Rank-one positive evaluation forms generate extreme PSD rays | `PSDRangeOneExtreme.rankOne_extreme_decomposition` | proved |
| A non-SOS element has a normalized negative extreme dual separator | `ConditionalSeparation.exists_normalized_extreme_separator` | proved from explicit dual-representation/compact-base inputs |
| Nonnegativity excludes the point-evaluation branch, yielding a basepoint-free extreme separator | `ConditionalSeparation.exists_basepointFree_extreme_separator` | proved from the extreme-ray dichotomy interface |

## Conditional boundary

`HVectorOneCOneFreeCertificate` and `SuccessiveLinearReductionComponentsRelation` are explicit
interfaces, not proofs of the PDF's Cohen--Macaulay/Gorenstein step. The remaining upstream
theorem must derive these certificates from the arithmetically Gorenstein standard graded
coordinate ring with Hilbert series
`(1 + c t + t^2)/(1-t)^(m+1)` and the chosen homogeneous system of parameters.  Current mathlib
does not expose Hilbert-series, Cohen--Macaulay, regular-sequence, or graded Gorenstein
infrastructure sufficient to state that derivation at the PDF's level without substantial new
library development. Once the one-dimensional socle and its annihilator property are supplied,
the specific functional induced by the paper's `ell` is now handled directly; no chosen
identification of the socle with the base field remains in the rank conclusion.

The finite evaluation algebra, evaluation-block inertia, abstract separation composition, and
the PDF-faithful SOS-length perturbation/lower-bound argument have now been checked here. What
remains is their instantiation from the PDF's concrete arithmetically Gorenstein variety, plus SOS
closedness, the concrete extreme-ray dichotomy, the real-topological projective evaluation map,
and the density/count properties of its reduced fibers. No claim in
this supplement treats an interface assumption as a proof of the original hypothesis.

## Audit against the nine requested targets

| Target | Status | Exact remaining boundary |
|---|---|---|
| 1. SOS cone closedness and dual | dual proved, closedness pending | `SOSConeDual.nonnegative_on_sosCone_iff` and closure invariance are proved; prove the concrete cone is closed |
| 2. Extreme-ray dichotomy | linear/convex ingredients proved, concrete dichotomy pending | kernel-face, rank-one evaluation extremality, compact-base extreme-ray selection are proved; classify the remaining concrete Hankel rays |
| 3. `dim W_ell=m+1`, `rank Q_ell=c` | paper-faithful successive-reduction endpoint proved conditionally | construct the independent parameter tuple, ambient Hilbert certificate, concrete indexed regular-sequence short exact sequences, reduction-to-quotient socle equivalence, and zero-annihilator property from the PDF's AG/CM hypotheses; the exact sequences now imply and assemble all one-step recurrences internally, and their iteration, the denominator/reduction certificates, `(1,c,1)` socle dimension, and all subsequent quotient/Hankel steps are internal |
| 4. Finite kernel morphism of degree `c+2` | conditional finite, surjective, rank-`c+2` theorem proved | strengthen the checked Artinian `(1,c,1)` component certificate to the finite free polynomial-module certificate from the AG/CM regular reduction; all stated Proj consequences are proved from it |
| 5. Reduced fibers and evaluation relations | substantial algebra proved | instantiate the abstract evaluation maps with the scheme fiber; relation uniqueness, nonzero-coefficient criterion, and degree-two isomorphism are proved |
| 6. At most one conjugate pair | normalized block theorem and concrete-family adapter proved | identify the concrete fiber Hankel form with the normalized complex-block coefficients and discharge relation-kernel nonnegativity and block non-isotropy |
| 7. Reciprocal identities and converses | proved in both fiber models | only the concrete evaluation-model identification remains |
| 8. Separation | final composition proved conditionally | instantiate SOS closedness, finite dual representation/compact base, and the concrete extreme-ray dichotomy |
| 9. Minimal SOS length | the perturbation proof, good-coordinate base-change family, dense reduced rank-`c+2` locus, algebraic rational-point lift, and its projective-coordinate compatibility are checked | instantiate ordinary evaluation continuity; identify real algebra points with `X(ℝ)` and its evaluation map; identify the concrete complex blocks and discharge their nonnegativity/non-isotropy |

## Verification

- Seventy-three thematic source modules, the root import, and the axiom audit: 75 Lean files
  totaling 11,936 source lines.
- No `sorry`, `admit`, custom `axiom`, `TODO`, `FIXME`, or `#check` in any extension source.
- The declarations listed by `Audit/Axioms.lean` depend only on `propext`, `Classical.choice`, and
  `Quot.sound`.
- The complete root import graph and the separate `Audit/Axioms.lean` check exited zero.
