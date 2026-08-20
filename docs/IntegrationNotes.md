# Verified extension integration notes

These modules were checked against Lean `v4.33.0-rc2` and mathlib commit
`51e6992efd06126df61a496bebf8f49482a4e129`. They were originally developed in a separate
permission-compatible staging area. On 2026-08-13 they were renamed and integrated into the
canonical `DelPezzoBlekherman/` hierarchy; the paths below are their current locations.

## `Geometry/Proj/GradedEvaluation.lean`

- graded polynomial evaluation into an arbitrary graded algebra;
- the irrelevant-ideal condition from degree-one generators, both strictly and up to radical;
- standard-chart arrow identification for `Proj.map`;
- local-to-global finiteness from finite degree-zero localization maps;
- polynomial projective evaluation morphisms under the strict condition.

## `Geometry/Proj/RadicalMap.lean`

- functoriality of `Proj` under the optimal irrelevant-ideal containment up to radical;
- continuous pullback on homogeneous primes, structure-sheaf map, stalk-locality, and genuine
  scheme morphism `mapOfRadical`;
- standard affine-chart formula and local-to-global finiteness;
- genuine basepoint-free projective evaluation morphism `projectiveAevalOfRadical`.

## `Geometry/Proj/Finite.lean`

- degree-compatible homogeneous generators remain finite generators after degree-zero
  localization at a degree-one element;
- arbitrary finite homogeneous module generators automatically have the required
  degree-compatible expressions;
- a finite graded ring hom induces finite maps on all degree-one `Away` charts;
- the polynomial variables cover projective space;
- end-to-end theorem
  `AlgebraicGeometry.Proj.projectiveAevalOfRadical_isFinite_of_toRingHom_finite`.
- a free-module basis indexed by `Fin (c + 2)` simultaneously proves projective finiteness
  and algebraic rank `c + 2`.

## `Fiber/ReducedAlgebra.lean`

- reduced finite-dimensional algebras over algebraically closed fields are products of copies
  of the base field;
- reduced finite flat fibers of rank `c + 2` have exactly `c + 2` geometric points;
- nondegenerate trace form, or nonzero trace determinant, implies reducedness;
- closed points over a field with quadratic algebraic closure have residue degree one or two;
- over `ℝ`, quadratic closed points have residue field `ℂ` and represent conjugate pairs;
- real reduced fibers satisfy `finrank = #closed points + #quadratic points`;
- rank `c + 2` plus at most one quadratic point gives the fully-real/one-pair count dichotomy.
- explicitly separating degree-one rational points from quadratic points gives the paper's
  geometric count: either `c + 2` real points, or `c` real points and one conjugate pair.

## `Geometry/Proj/KernelFiber.lean`

- one homogeneous basis certificate simultaneously gives a finite projective evaluation
  morphism and exactly `c + 2` points in every reduced geometric fiber;
- the projective morphism and affine fiber use the same polynomial-to-coordinate-ring map.

## `Algebra/DiscriminantFiber.lean`

- discriminants of finite free algebra bases commute with arbitrary base change;
- every prime fiber outside the basis discriminant is reduced;
- a nonzero discriminant over a domain gives a reduced generic fiber;
- in characteristic zero, a field generic fiber forces the discriminant to be nonzero, hence
  the reduced-fiber principal open is nonempty;
- combined with the `Fin (c + 2)` basis theorem, every geometric fiber outside the
  discriminant has exactly `c + 2` points.

## `Algebra/GenericFiber.lean`

- the generic fiber of an injective finite map of integral domains is a field, via its
  identification with a localization of the target domain;
- in characteristic zero this makes the discriminant of every finite basis nonzero;
- the projective evaluation theorem now packages finiteness with nonvanishing discriminant,
  so its reduced `c + 2`-point fiber locus is a nonempty principal open.

## `Algebra/HVectorCertificate.lean`

- a graded free-module certificate records one basis generator in degree zero, `c` in degree
  one, and one in degree two, i.e. Hilbert numerator `1 + c t + t²`;
- its index type is explicitly reindexed to `Fin (c + 2)`;
- this certificate feeds directly into the finite-projective-morphism and nonzero-discriminant
  theorem.
- at every algebraically closed base point off the discriminant, the resulting fiber has
  exactly `c + 2` points.

The same basis/discriminant certificate over `ℝ`, together with the paper's at-most-one-pair
input, feeds directly into the fully-real/one-conjugate-pair closed-point dichotomy.

## `Algebra/ArtinianGorenstein.lean`, `Algebra/SoclePairing.lean`, `Algebra/QuotientMultiplication.lean`, and `Algebra/StandardGradedMultiplication.lean`

- a nondegenerate bilinear form on `V/W`, pulled back to `V`, has radical exactly `W` and rank
  `dim(V/W)`;
- a one-dimensional degree-two socle is automatically linearly equivalent to the base field;
- symmetric degree-one multiplication and the Gorenstein socle-annihilator property imply that
  the scalar socle pairing is nondegenerate;
- with `dim R₁ = m+c+1` and `dim (R/(W))₁ = c`, this proves `dim W = m+1` and Hankel rank `c`.
- every nonzero functional induced on the one-dimensional socle is injective and therefore
  preserves perfection of the multiplication pairing;
- a pointwise factorization identifies the original ambient Hankel form with the quotient
  pullback, proves its actual kernel equals the parameter space, and yields the PDF's
  `m+1` kernel dimension and rank `c` conclusion without choosing a socle coordinate.
- ambient degree-one multiplication descends through `R₁/W` in both arguments whenever
  products involving `W` lie in an explicit degree-two relation space `J`;
- a degree-two functional annihilating `J` descends through `R₂/J`, and its composition with
  the descended multiplication is proved to recover the original Hankel form on representatives;
- the ambient-data endpoint constructs both descended maps internally and feeds them into the
  exact-kernel/dimension/rank theorem.
- the tensor square modulo swap relations gives a local `SymmetricSquare`, and every symmetric
  multiplication descends canonically to `Sym²(R₁) → R₂`;
- if this paper-facing symmetric-square multiplication is surjective, then the tensor-linearized
  multiplication is surjective (and conversely), so a nonzero functional on `R₂` cannot vanish
  on every product.
  The strongest endpoint now uses exactly the PDF's `Sym²(R₁) → R₂` generation statement
  and the original `ell ≠ 0`, rather than a separate Hankel-nonzeroness hypothesis.
- the degree-two relation space can be chosen canonically as `span(W·R₁)`; the product
  containment is then tautological, while `W ⊆ ker Q_ell` proves `ell` annihilates the whole
  span and therefore descends to the quotient socle.
- the known dimension `dim W=m+1` of the chosen homogeneous parameter span, together with
  `dim R₁=m+c+1`, derives `dim(R₁/W)=c`; it is no longer a separate quotient assumption;
- `ParameterProductGorensteinCertificate` isolates exactly the remaining Proposition 2.2
  outputs: the canonical quotient socle has dimension one and its degree-one multiplication
  has zero annihilator.
- `ParameterProductPerfectPairingCertificate` states the Proposition 2.2 output in the PDF's
  own intrinsic form: a one-dimensional socle whose socle-valued degree-one multiplication is
  nondegenerate. Perfectness proves the annihilator property internally; choosing the canonical
  socle coordinate is separately proved to produce a nondegenerate scalar pairing.
- conversely, the zero-annihilator `ParameterProductGorensteinCertificate` implies the intrinsic
  perfect certificate because quotient multiplication is symmetric. The strongest pointwise
  and internal-graded endpoints therefore consume the weaker annihilator formulation directly.
- an explicit linearly independent `Fin (m+1)` parameter family spanning `W` now derives
  `dim W=m+1` and feeds the final kernel/rank endpoint, matching the parameter choice made in
  Theorem 4.3.
- the strongest endpoint only assumes each chosen parameter lies in `ker Q_ell`; span
  containment is proved internally, matching the pointwise choice `fᵢ ∈ W_ell` in the paper.
- for a degree-one submodule `U` of an actual commutative algebra, canonical multiplication is
  valued in `U * U`; mathlib's `Submodule.mulMap'_surjective` proves the tensor map is onto that
  product submodule, and commutativity proves symmetry. The symmetric-square generation input
  and both structural multiplication hypotheses are therefore discharged internally.
- an explicit equality `U * U = Q` transports this multiplication to a named degree-two piece
  `Q`; the resulting endpoint accepts the paper's original functional `ell : Q → K` directly.
- for an internal multiplicative grading `𝒜`, Lean constructs the canonical map
  `𝒜 1 × 𝒜 1 → 𝒜 2`. The paper's literal degree-two standard-graded consequence—surjectivity
  of `Sym²(𝒜 1) → 𝒜 2`—proves `𝒜 1 * 𝒜 1 = 𝒜 2` and supplies the strongest graded endpoint;
  equivalence with tensor surjectivity is used only inside the proof.
- `Algebra.HilbertArithmetic` now defines the exact formal power series from equation (1) using
  mathlib's inverse `(1-t)^{-(m+1)}`, proves its coefficients through degree two, and packages
  coefficient/finrank compatibility. The strongest graded rank endpoint uses that certificate
  to derive finite-dimensionality and `dim R₁=m+c+1` instead of accepting either separately.
- Multiplying equation (1) by `(1-t)^(m+1)` is now proved to cancel exactly to
  `1+c t+t²`. Its coefficients are proved to be `(1,c,1,0,...)`, and
  `ArtinianReductionHilbertSeriesCertificate` turns those coefficients into the component
  dimensions of an abstract Artinian reduction.
- A degree-two linear equivalence from that reduction to the canonical parameter-product
  quotient transports the checked dimension-one result into
  `ParameterProductGorensteinCertificate`; the strongest graded Theorem 4.3 endpoint now performs
  this construction internally and retains only the zero-annihilator property as a separate
  Gorenstein input.
- `ArtinianReductionDenominatorRelation` records precisely the numerical identity produced by
  quotienting by the `(m+1)` linear parameters. Its conversion theorem uses exact cancellation
  to construct `ArtinianReductionHilbertSeriesCertificate`, so the strongest endpoint no longer
  asks for that downstream certificate independently.
- `DegreeOneReductionComponentExactSequence.toFinrankRelation` now derives
  `DegreeOneReductionFinrankRelation` from the finite-dimensional homogeneous short exact
  sequence for one degree-one nonzerodivisor. An indexed family of those exact sequences,
  even when the quotient carrier changes at every stage, automatically constructs
  `SuccessiveLinearReductionComponentsRelation`. Lean then multiplies the Hilbert series by
  `1-t` at each stage and directly constructs both `ArtinianReductionDenominatorRelation` and
  the final `(1,c,1)` Hilbert-series certificate. The direct strongest graded endpoint consumes
  this varying-carrier chain after an explicit degreewise linear equivalence identifies its
  initial carrier with the ambient algebra. The same transport now directly constructs both the
  denominator relation and the final `(1,c,1)` certificate; it is necessary because a concrete
  quotient model can carry a module instance distinct from the algebra-induced one.

## `LinearAlgebra/NonrealPairInertia.lean` and `Fiber/RealInertia.lean`

- restriction of a real quadratic form to a subspace cannot increase its negative index;
- one independent negative direction per quadratic closed point bounds the number of conjugate
  pairs by the negative index;
- an ambient Lorentzian/index-one form therefore gives at most one pair and discharges the
  pair-count hypothesis in the real reduced-fiber dichotomy.

## `Fiber/ReciprocalHyperplane.lean`

- two nonzero linear functionals with nested kernels differ by a scalar;
- a radical vector of a real diagonal form restricted to the unique evaluation-relation
  hyperplane forces the reciprocal identity `∑ uᵢ²/μᵢ = 0`;
- conversely, that identity constructs the radical vector `(uᵢ/μᵢ)ᵢ`;
- nonnegativity on the relation hyperplane forces exactly one negative coefficient.

## `Fiber/MixedReciprocalHyperplane.lean`

- the same radical/reciprocal equivalence for real evaluation points plus one
  complex-conjugate pair:
  `∑ uᵢ²/aᵢ + 2 Re(v²/b) = 0`;
- the exact real-coordinate expansion for `b = α + β I`;
- after normalizing the conjugate-pair relation coefficient to one, nonnegativity on the
  relation hyperplane forces `α = Re(b) ≤ 0`, and forces `α < 0` when the pure-imaginary
  direction is non-isotropic.

## `LinearAlgebra/NegativeDirections.lean` and `Fiber/ComplexBlock.lean`

- a diagonal negative-coordinate model constructs the negative-definite subspace certificate
  with dimension exactly the number of conjugate pairs;
- for complex evaluation blocks `2 Re(bₚ zₚ²)`, the real axes have weights `2 Re(bₚ)`;
- hence normalized signs `Re(bₚ) < 0` give one independent negative direction per pair;
- combined with nonnegativity on the evaluation-relation kernel, this directly proves the
  `c+2` real / `c` real plus one pair dichotomy without assuming the pair-count bound.
- more strongly, in the fully normalized model relation-kernel nonnegativity and block
  non-isotropy themselves force `Re(bₚ) < 0`, so the pair-count and real-fiber dichotomy need no
  separate sign hypothesis.

## `Fiber/EvaluationHyperplane.lean`

- a degree-one evaluation image equal to `ker (∑ uᵢxᵢ)` has a unique relation up to scalar;
- `uᵢ ≠ 0` is equivalent to the corresponding coordinate delta vector not lying in the
  degree-one image;
- with at least three points and all `uᵢ ≠ 0`, products of vectors in the evaluation
  hyperplane span the entire coordinate algebra;
- any compatible degree-two evaluation map is therefore surjective;
- when its source dimension equals the fiber length, it is a linear equivalence, formalizing
  the finite-dimensional core of Proposition 5.2.

## `SOS/KernelLength.lean`

- a PSD Hankel form annihilating a sum of diagonal values forces every summand into its
  radical, using the checked equality case of Cauchy--Schwarz;
- if the summands span the radical, their number is at least its dimension;
- the spanning input follows from the precise projective base-locus property: every proper
  subspace of the radical has a common zero, while strict positivity supplies no common zero for
  the SOS summands;
- with radical dimension `m+1`, this yields the lower bound `m+1` for boundary SOS length.
- strict positivity of a represented SOS automatically gives the no-common-zero input for every
  competing representation;
- therefore any supplied `m+1`-square boundary representation is minimal among all
  representations. The following compression modules now derive such a representation rather
  than assuming it.

## `SOS/Compression.lean`

- defines the explicit scalar `(sqrt (1 + S) - 1) / S` for the square root of a rank-one
  coefficient update and proves its exact polynomial identity;
- if an extra vector is supplied as `F = ∑ bᵢ fᵢ`, updates the existing family by
  `fᵢ ↦ fᵢ + lambda bᵢ F` and proves that its square-sum is the old square-sum plus `B F F`;
- handles the zero coefficient vector separately, so `compress_one_extra_explicit` requires only
  the explicit span relation;
- proves the update preserves the family span, then iterates it over arbitrary finite lists and
  finsets;
- extracts a basis subfamily from the original finite family and proves
  `exists_compression_to_finrank_span`, the complete finite Gram-rank upper bound.

## `SOS/ExactLength.lean`

- combines strict positivity, support by a PSD Hankel form, and the proper-subspace basepoint
  property to show the summands of every representation span the full Hankel radical;
- applies finite Gram compression and the radical dimension `m+1` to produce an `m+1`-square
  representation from an arbitrary finite representation;
- applies the checked lower bound to every competing representation, proving exact minimal SOS
  length `m+1` without taking a short representation as an input.

## `SOS/ProjectiveBasepoint.lean` and `SOS/SurjectiveLength.lean`

- every proper real subspace has a nonzero functional in its dual annihilator;
- if every nonzero functional direction on a linear system occurs, up to nonzero scalar, as a
  point evaluation, every proper subspace has a common zero;
- this is a stronger conditional shortcut from surjectivity of the projective evaluation map,
  not the perturbation argument used in the PDF;
- composing it with the compression/lower-bound theorem proves exact minimal length `m+1`
  directly from projective evaluation surjectivity.

## `SOS/Perturbation.lean`

- formalizes the actual lower-bound proof of Theorem 8.3 from the PDF;
- proves a dense subset meets the open complement of a compact continuous image;
- derives existence of a real point from fiber size `c+2`, `c≥1`, and at most one conjugate pair;
- turns any hypothetical representation by at most `m` squares into an annihilating projective
  direction outside the real evaluation image, perturbs it into the reduced-fiber locus, and
  obtains a contradiction from the real-point count;
- combines that lower bound with finite Gram compression to prove exact minimal length `m+1`.

## `Geometry/RealProjective/Topology.lean` and `SOS/RealProjectiveLength.lean`

- model finite-dimensional real projective directions as the unit sphere modulo the antipodal
  action of the two integer units `±1`;
- prove the quotient is compact Hausdorff and that normalization/direction formation is continuous;
- prove equality of directions is equivalent to multiplication by a nonzero real scalar;
- prove strict positivity of a supported SOS makes evaluation on the Hankel radical nowhere zero;
- reduce continuity of projective radical evaluation to continuity of the ordinary
  finite-dimensional continuous-dual evaluation map;
- instantiate the PDF-faithful perturbation theorem with this concrete projective target, removing
  the abstract target and ray-identification interfaces.

## `Analysis/AnalyticNonvanishing.lean` and `Geometry/RealProjective/PolynomialDensity.lean`

- prove the nonzero locus of a globally analytic nonzero function on a preconnected normed space
  is dense by the analytic identity theorem;
- specialize this to evaluation of a nonzero real multivariate polynomial;
- prove the normalization and antipodal direction maps are surjective;
- transport polynomial nonvanishing density to the compact real projective target.

## `Geometry/RealProjective/HVectorDensity.lean`

- specializes the `(1,c,1)` finite-free certificate to the real polynomial subring;
- extracts its already-checked nonzero algebra discriminant;
- composes with projective polynomial density to prove the reduced-fiber discriminant locus is
  Euclidean dense in real projective coordinates.
- transports the locus through an arbitrary continuous linear equivalence, with a basis-indexed
  specialization ready for the continuous dual of the Hankel radical.

## `SOS/DenseFiberLength.lean`

- composes strict positivity, supported-PSD radical containment, ordinary evaluation continuity,
  an arbitrary dense reduced locus, the perturbation lower bound, and Gram compression;
- proves exact minimal SOS length `m+1`; `Geometry/RealProjective/HVectorDensity.lean` separately supplies the
  dense locus from the certificate, leaving only concrete fiber count/pair count and
  real-point/image identifications explicit.

## `Fiber/RealCount.lean`

- proves length of a reduced finite real algebra equals the number of rational closed points plus
  twice the number of quadratic closed points;
- specializes this to the exact `c+2` count equation used by the perturbation theorem;
- proves rank `c+2`, `c≥1`, and at most one quadratic point force existence of a real rational
  closed point.

## `Fiber/RealFamily.lean`

- defines rational-real-point and quadratic-pair counts for a family of finite real algebras;
- derives the exact `c+2 = realCount + 2 * pairCount` equation from pointwise reducedness and
  constant rank;
- converts a pointwise at-most-one-quadratic-point theorem directly into the perturbation input.
- turns a compatible lift of rational fiber points to the real source into the required zero-count
  theorem outside the real evaluation image.

## `SOS/FiberFamilyLength.lean`

- instantiates the perturbation theorem's numerical functions with rational and quadratic
  closed-point counts of an actual family of finite real algebras;
- derives the count equation from reducedness and rank `c+2`, the outside-image condition from a
  rational-point lift, and exact minimal SOS length from the resulting concrete family interfaces.

## `Geometry/RealProjective/CoordinateFiber.lean`

- chooses coordinates for each compact real projective direction and evaluates the polynomial
  subring at that representative;
- defines the coordinate-ring fiber as base change `ℝ ⊗[MvPolynomial I ℝ] C`;
- verifies its real algebra and finite-module instances, transports arbitrary bases, and proves
  constant rank;
- specializes the `(1,c,1)` basis to rank `c+2` and proves discriminant nonvanishing implies
  reducedness.

## `Geometry/RealProjective/GoodCoordinates.lean` and `Geometry/RealProjective/HVectorFiberFamily.lean`

- replace arbitrary projective representatives by chosen affine coordinates on the dense
  discriminant-nonvanishing locus, avoiding any unstated homogeneity assumption;
- prove those chosen coordinates represent the original projective direction;
- define the resulting `(1,c,1)` tensor-product family, prove rank `c+2` everywhere, and prove
  reducedness on the dense good-coordinate locus.

## `Fiber/ComplexBlockFamily.lean` and `Geometry/RealProjective/HVectorPairBound.lean`

- apply the normalized complex-block calculation uniformly to a dependent finite-algebra family;
- specialize it to the good `(1,c,1)` fibers, reducing the pair bound to the concrete block
  coefficients, relation-kernel nonnegativity, and block non-isotropy.

## Rational-point lift modules

`Fiber/RationalPointLift.lean`, `Geometry/RealProjective/CoordinateFiberLift.lean`,
`Geometry/RealProjective/HVectorRationalLift.lean`, and `Geometry/RealProjective/HVectorRealCount.lean`:

- identify the degree-one residue field of a rational closed point with the base field and obtain
  an actual base-field-valued algebra homomorphism;
- restrict a rational tensor-product fiber point to the source coordinate ring and prove its
  polynomial parameters equal the coordinates defining the fiber;
- prove, for the `(1,c,1)` family, exact equality on the degree-one generators, nonvanishing, and
  recovery of the original projective direction;
- derive zero real-fiber count outside the projective image from only a compatible realization of
  nonzero real source algebra points in the geometric source;
- define the canonical generator-direction source and prove its zero-count theorem without any
  remaining lift or realization assumption.

## `SOS/EvaluationContinuity.lean`

- reduces continuity of a family of finite-dimensional dual evaluation functionals to scalar
  continuity on the vectors of any finite basis;
- supplies a finite coordinate-level interface for the ordinary evaluation-continuity input in
  the real-projective perturbation theorem.

## `Geometry/Proj/Surjectivity.lean`

- proves an injective graded ring map stays injective on every homogeneous degree-zero
  localization;
- combines finite chart maps with injectivity and lying-over to obtain surjectivity on each
  standard affine chart;
- uses the Zariski-local-at-target instance for scheme surjectivity to prove the induced radical
  `Proj` map is globally surjective;
- specializes this to basepoint-free polynomial evaluation maps;
- packages finiteness, surjectivity, algebraic rank `c+2`, and nonzero discriminant from the
  `(1,c,1)` free-basis certificate. For the PDF-faithful length proof, the remaining bridge is the
  real-topological projective evaluation map together with density and concrete fiber-count
  identifications.

## `Convexity/ExtremeSeparator.lean` and `SOS/DualCone.lean`

- Farkas/Hahn--Banach separates any point outside a proper cone by a continuous functional with
  the paper's sign convention;
- a functional negative somewhere on a compact set is negative at an extreme point, via an
  exposed minimizing face and Krein--Milman;
- the dual of the convex cone generated by squares consists exactly of functionals nonnegative
  on every individual square;
- taking the closure does not change this continuous dual, cleanly isolating the independent
  closedness theorem required to identify the generated cone itself with a proper cone.

## `Convexity/ExtremeRayBase.lean`

- defines the additive extreme-ray property faithfully: a cone decomposition of a generator has
  both summands on the same nonnegative ray;
- an extreme point of a base cut out by a functional strictly positive on nonzero cone elements
  generates an extreme ray;
- compactness of that base upgrades any negative base separator to a negative extreme-ray
  generator, completing the abstract convex reduction used by the extreme-ray dichotomy.

## `Convexity/RankOneExtreme.lean`

- the kernel of a sum of PSD bilinear forms is the intersection of their kernels, giving the
  kernel-face criterion used throughout the dual SOS analysis;
- a symmetric form whose kernel contains `ker f` is a scalar multiple of `f ⊗ f`;
- PSD forces that scalar to be nonnegative;
- consequently every nonzero rank-one point-evaluation form generates an extreme PSD ray.

## `Convexity/ConditionalSeparation.lean`

- represents continuous primal separators by an abstract finite-dimensional Hankel-data space;
- normalizes a separator on a compact strictly positive dual-cone base and replaces it by a
  negative extreme-ray generator;
- given the point-evaluation/basepoint-free extreme-ray dichotomy and nonnegativity of the target
  at point evaluations, excludes the evaluation branch and returns a basepoint-free extreme
  separator;
- this is the fully checked final logical composition for Theorem 1.1, conditional only on the
  explicitly listed cone representation/compactness and geometric dichotomy inputs.

## `SOS/ClosedCone.lean`

- identifies `SOSConeDual.sosCone` with the project-wide finite-sum SOS cone;
- transfers Gram-model closedness to the named convex-cone representation using only Gram
  compatibility and the faithful positive-semidefinite kernel criterion.

## Verification

- Compilation succeeds for the complete root import graph.
- Placeholder search finds no `sorry`, `admit`, custom `axiom`, `TODO`, `FIXME`, or `#check`.
- `#print axioms` for the principal new declarations reports only `propext`,
  `Classical.choice`, and `Quot.sound`.

## Remaining bridge work

- derive finiteness, flat rank `c + 2`, and the appropriate homogeneous module structure from
  the arithmetically Gorenstein/Hilbert-series hypotheses;
- derive the checked equation-(1) Hilbert certificate and instantiate
  `SuccessiveDegreeOneReductionComponentExactSequences` from the homogeneous short exact
  sequences of the actual regular sequence, the identification of the reduction's degree-two component with the
  canonical quotient socle, the
  socle-annihilator property, and the finite free polynomial-module basis from the PDF's
  arithmetically Gorenstein/Cohen--Macaulay regular-sequence hypotheses; cancellation to
  `(1,c,1)` and all later kernel/rank reasoning are already automatic;
- identify the paper's concrete fiber evaluation isomorphism with the checked complex-block
  quadratic model and prove its relation-kernel nonnegativity and block non-isotropy;
- realize the constructed real algebra points with nonzero degree-one generator vector as points
  of `X(ℝ)`, prove compatibility with projective evaluation, and establish ordinary evaluation
  continuity;
- complete the final theorem-chain audit after workspace access is restored.
