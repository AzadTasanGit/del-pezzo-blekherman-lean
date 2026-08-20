# Completion plan

This file is the authoritative roadmap to a native Lean statement of all six parts of Theorem
1.1. The larger status and progress documents are supporting inventories; when their scheduling
language conflicts with this file, this file controls.

## Definition of done

The project is complete only when declarations `theorem1_1_i` through `theorem1_1_vi` and an
aggregate `theorem1_1` compile from the paper's coordinate-ring, geometric, Hilbert-series, and
arithmetically Gorenstein hypotheses. Their public signatures must not mention any of the
following implementation interfaces:

- `HVectorOneCOneFreeCertificate`;
- `DelPezzoHilbertSeriesCertificate`;
- `SuccessiveDegreeOneReductionComponentExactSequences` or another supplied
  reduction-exact-sequence package;
- `ParameterProductGorensteinCertificate` or
  `ParameterProductPerfectPairingCertificate`;
- a Gram-kernel criterion, an abstract extreme-ray dichotomy, complex-block assumptions, or an
  evaluation-continuity assumption.

Completion also requires the root build and axiom audit to pass, a repository-wide placeholder
and custom-declaration scan to be empty, the status documents to agree with this roadmap, and a
clean tracked worktree after the final commit.

## Fixed public boundary

The paper-level setup will name the standard graded real coordinate ring `R`, its internal
homogeneous components `𝒜`, the projective real variety and its Zariski-dense real locus, integers
`m` and `c`, and the literal equation

```lean
∀ d, (Module.finrank ℝ (𝒜 d) : ℤ) =
  PowerSeries.coeff d (delPezzoHilbertSeries m c)
```

The native Gorenstein input is
`DelPezzoBlekherman.IsArithmeticallyGorenstein 𝒜 parameters`. It is operational rather than a
label for an unavailable canonical-module theory: it asserts that the actual degree-one
parameters form mathlib's ring-theoretic regular sequence, that their actual ideal quotient is
Artinian, and that multiplication on the concrete degree-one reduction is perfect into its
one-dimensional degree-two socle. The Hilbert-series equation stays separate.

The six final declarations have the following mathematical conclusions.

1. `theorem1_1_i`: the concrete cone `Σ_X` is closed and its dual is exactly the positive
   semidefinite Hankel functionals.
2. `theorem1_1_ii`: positive point evaluations are extreme, and every extreme dual ray is
   exclusively either a positive evaluation or has basepoint-free kernel of dimension `m+1` and
   Hankel rank `c`.
3. `theorem1_1_iii`: the basepoint-free branch gives a finite surjective degree-`c+2` morphism,
   a nonempty real-defined reduced-fiber open locus with real points, the evaluation hyperplane
   and degree-two evaluation equivalence, nonzero relation coefficients, and at most one
   conjugate pair.
4. `theorem1_1_iv`: a fully real reduced fiber has the unique reciprocal relation, exactly one
   negative coefficient, and the converse produces the stated rank-`c` extreme ray.
5. `theorem1_1_v`: a reduced fiber with one conjugate pair has the mixed reciprocal relation and
   signs, its converse, and the normalized `α < 0` form.
6. `theorem1_1_vi`: every nonnegative non-SOS quadratic is separated by a basepoint-free extreme
   ray, and every strictly positive boundary SOS has minimal length `m+1`.

The aggregate `theorem1_1` will return the conjunction/product of these six named results from a
single native setup. No final declaration may accept a theorem conclusion as an assumption.

## Serial critical path

Only one milestone is active at a time. A task should normally end in one to three independently
compiling declarations, and each merged task must eliminate a hypothesis from a final public
signature.

| Milestone | Owner | Exact next boundary | Acceptance condition | State |
|---|---|---|---|---|
| 1. Native algebraic boundary | Sol High | Derive the actual parameter quotient and generic degree from regular degree-one parameters and the literal Hilbert equation. | The finite-surjective and degree-`c+2` declarations expose none of the four algebra certificates, flatness/local freeness, or a chosen basis. | complete: quotient length `c+2`, origin-stalk freeness from regularity, and basis-free generic rank all compile |
| 2. Concrete SOS and Hankel layer | Terra Medium | Instantiate `kernel_face_criterion` and the real/complex point-evaluation arguments for the concrete graded multiplication. | `theorem1_1_i`, the evaluation branch, the real-point dichotomy, and the rank-two complex-basepoint exclusion compile with no Gram-kernel or abstract-dichotomy input. | complete: the concrete part (i), real dichotomy, and paper's indefinite-form exclusion of nonreal rank-two evaluations compile |
| 3. Kernel morphism and reduced fibers | Terra Medium; Sol High for a recorded blocker | Instantiate the proved real-locus kernel correspondence for a native complex Proj point type, extract a regular hsop from the complex-basepoint-free kernel, connect it to `projectiveAevalOfRadical`, and construct the reduced-fiber data. | `theorem1_1_ii` and `theorem1_1_iii` compile without an H-vector/free-basis certificate, assumed flatness/local freeness, or supplied fiber data. | active: complex linear-algebra exclusion, real/nonreal projective dichotomy, native kernel rank, actual reduction length, local freeness, and basis-free generic degree are complete; native Proj-point instantiation, regular-parameter selection, and reduced-fiber specialization remain |
| 4. Fiber classifications and topology | Terra Medium | Identify the concrete evaluation form with `ComplexBlockFamily`; prove relation-kernel nonnegativity and block non-isotropy; instantiate the pair bound and both reciprocal classifications. Prove ordinary evaluation continuity and identify the real coordinate-ring source with `X(ℝ)` compatibly with projective evaluation. | `theorem1_1_iv`, `theorem1_1_v`, and every premise required by the concrete SOS-length theorem compile without block or continuity assumptions. | queued |
| 5. Final composition | Sol High review, Terra Medium integration | Add `theorem1_1_i` through `theorem1_1_vi`, compose them in `theorem1_1`, and reconcile every status document and audit entry. | All conditions in “Definition of done” hold. | queued |

## Current checked algebra boundary

`DelPezzoBlekherman/Algebra/NativeGorenstein.lean` now provides:

- `degreeOneParameterIdeal`, the actual homogeneous parameter ideal;
- `degreeOneParameterIdeal_isHomogeneous`, proving that ideal homogeneous from the actual
  degree-one generators;
- `idealComponent`, `idealQuotientComponent`, and
  `idealQuotientComponentEquivRange`, constructing each degree of the parameter quotient and
  identifying it canonically with the corresponding image in the actual quotient;
- `moduleFinite_idealQuotientComponent`, transporting finite-dimensionality to every concrete
  quotient component;
- `idealQuotientComponentMul`, the actual homogeneous multiplication map on these quotient
  components, and `idealQuotientComponentMul_injective_of_isSMulRegular`, which derives its
  injectivity from ring-theoretic regularity on the full ideal quotient;
- `idealQuotientComponentMapOfLE`, the canonical degreewise map after enlarging the ideal,
  together with its surjectivity and the proof that it composes to zero after multiplication by
  an element of the enlarged ideal;
- the reverse kernel-to-range inclusion and the resulting concrete short exact sequence for
  adjoining one regular degree-one parameter;
- `degreeOneParameterPrefix_finrankRelations`, which iterates those actual quotient sequences;
- `degreeOneParameterIdeal_finrank_eq_delPezzoHilbertNumerator`, which derives the literal
  Artinian Hilbert function `(1,c,1,0,...)` from the paper's Hilbert equation; and
- `degreeOneParameterIdeal_quotient_finrank`, which proves that the actual full parameter
  quotient has total dimension `c+2`;
- `IsArithmeticallyGorenstein`, the regular, Artinian, one-dimensional-socle and perfect-pairing
  predicate described above;
- `moduleFinite_degreeOne_of_delPezzoHilbertSeries`, which consumes the literal equation rather
  than exposing a Hilbert certificate;
- `hankelKernel_eq_parameterSpan_and_rank_of_arithmeticallyGorenstein`, which concludes the
  actual Hankel kernel equality and rank `c` without any project-specific algebra certificate in
  its signature.

`DelPezzoBlekherman/TheoremOne.lean` now provides the first paper-facing endpoint:

- `eq_zero_of_vanishes_on_zariskiDense_realEvaluations`, which derives separation of coordinate
  functions from actual density of the real evaluation primes in `PrimeSpectrum` and reducedness;
- `dualCone_gradedSOSCone_eq_psdHankel`, which identifies the concrete continuous dual cone with
  positive-semidefinite Hankel forms for the actual degree-one multiplication;
- `theorem1_1_i`, proving both assertions of Theorem 1.1(i) from the literal Hilbert-component
  dimensions and genuine Zariski density. Its signature contains neither a Gram-kernel condition
  nor an assumed closedness/separation certificate.
- `theorem1_1_ii_pointEvaluation`, proving directly that every nonzero real point evaluation
  spans an extreme ray of the concrete dual SOS cone;
- `theorem1_1_ii_dichotomy`, proving that every concrete extreme dual ray is exclusively either
  a positive real point evaluation or its actual Hankel kernel has no common zero among the
  supplied real evaluations. It consumes no supplied Gram-kernel or abstract
  extreme-ray-dichotomy hypothesis;
- `extreme_hankel_no_complex_basepoint_of_surjective_evaluation`, formalizing the paper's
  indefinite `Re(e(u)e(v))` argument and excluding any complex basepoint whose degree-one
  evaluation is onto `ℂ` as a real-linear map;
- `isProjectivelyReal_or_surjective`, proving intrinsically that every nonzero complex
  degree-one evaluation is either a real projective line or is onto `ℂ` over `ℝ`;
- `extreme_hankel_no_nonreal_complex_basepoint`, which consequently excludes every nonreal
  complex basepoint without accepting surjectivity as an assumption;
- `theorem1_1_ii_complexDichotomy_of_realLocus`, which combines the concrete real-point
  dichotomy with the nonreal exclusion. Its only remaining geometric adapter is the exact
  bidirectional kernel correspondence between real points and projectively real complex
  evaluations; it contains no complex-block or rank-two premise;
- `theorem1_1_ii_kernelRank_of_arithmeticallyGorensteinParameters`, giving the dimension
  `m+1` and rank `c` conclusions once the regular parameters in the concrete kernel are selected,
  with no legacy algebra certificate in its public signature.

`DelPezzoBlekherman/Geometry/Proj/Finite.lean` and `Geometry/Proj/Surjectivity.lean` now provide:

- `MvPolynomial.standardGradedAevalHom_toRingHom_finite_of_basepointFree`, which constructs
  module finiteness from finite homogeneous pieces, finite generation of the irrelevant ideal,
  the standard-grading degree-power property, and basepoint-freeness;
- `AlgebraicGeometry.Proj.projectiveAevalOfRadical_isFinite_of_standardGraded_basepointFree`;
- `AlgebraicGeometry.Proj.projectiveAevalOfRadical_isFinite_surjective_of_standardGraded_hsop`,
  which adds algebraic independence of the parameters and concludes finite surjectivity without
  accepting `RingHom.Finite`, a polynomial-module basis, or an H-vector certificate.

`DelPezzoBlekherman/Algebra/NativeParameterRank.lean`, `Algebra/GenericFiber.lean`, and
`Geometry/Proj/KernelFiber.lean` additionally provide:

- `finrank_fiber_eq_finrank_of_free_atPrime`, which equates generic rank with the dimension of a
  prime fiber using freeness only at that prime;
- `Module.free_of_isRegular_of_span_eq_maximalIdeal`, which lifts freeness backwards through a
  regular sequence spanning a local ring's maximal ideal;
- `degreeOneParameter_free_at_origin_of_isRegular`, which applies that lemma at the polynomial
  parameter-space origin;
- `genericRank_eq_degreeOneParameterIdeal_quotient_of_free_at_origin`, which identifies the
  parameter-origin fiber with the actual parameter quotient;
- `genericRank_eq_degreeOneParameterIdeal_quotient_of_isRegular` and `genericRank_eq_add_two`,
  which derive local freeness internally and prove generic rank `c+2` without flatness, an assumed
  free stalk, a chosen module basis, or a project-specific certificate. The older local-free and
  flat declarations remain implementation-level wrappers;

- `Module.exists_nonzero_free_away_and_finrank_eq`, which proves that a finite module over a
  Noetherian domain becomes free after inverting one nonzero element, with localized rank equal
  to its basis-free generic `Module.finrank`;
- `AlgebraicGeometry.Proj.projectiveAevalOfRadical_isFinite_and_exists_nonzero_free_away_of_standardGraded`,
  which derives that nonempty principal-open free locus directly from the native finite-Proj
  hypotheses, without accepting a global basis, `Module.Free`, `RingHom.Finite`, or a numerical
  rank;
- `AlgebraicGeometry.Proj.projectiveAevalOfRadical_isFinite_surjective_genericallyFree_of_hsop`,
  which combines that generic-free locus with the certificate-free finite-surjective hsop
  endpoint.

The internal construction of old interfaces in a proof is permitted; exposing one in a final
signature is not. The numerical degree half of the old finite-Proj bridge is now complete: local
freeness is derived from the regular sequence and then consumed internally. Flatness, supplied
local/global freeness, and a global polynomial-module basis are not needed for degree, finiteness,
or surjectivity.

## Task handoff format

Every implementation handoff records:

- the exact target declaration and file;
- existing declarations to reuse;
- assumptions forbidden in its public signature;
- the focused compilation command;
- whether the task removed a final assumption.

Terra work escalates to Sol when 30–45 minutes yields helpers but removes no final assumption, or
when two materially different proof approaches fail. Before escalation, append the minimal
failing declaration, compiler errors, attempted approaches, and suspected missing lemma to the
blocker log below.

## Blocker log

### 2026-08-20: native finite-Proj and degree `c+2`

**Minimal target.** In `Geometry/Proj/Surjectivity.lean`, add a paper-facing specialization of
`projectiveAevalOfRadical_isFinite_surjective_and_finrank_eq_add_two_of_basis` for
`g : Fin (m + 1) → C`. Its inputs should be the standard graded coordinate-ring setup, the
literal Hilbert equation, basepoint-freeness, and
`IsArithmeticallyGorenstein 𝒸 parameters`; its conclusion should be

```lean
IsFinite (projectiveAevalOfRadical 𝒸 g hg hbasepointFree) ∧
  Surjective (projectiveAevalOfRadical 𝒸 g hg hbasepointFree) ∧
  (let f := MvPolynomial.standardGradedAevalHom 𝒸 g hg
   letI := f.toRingHom.toAlgebra
   Module.finrank (MvPolynomial (Fin (m + 1)) K) C = c + 2)
```

The signature must not contain a polynomial-module basis, `HVectorOneCOneFreeCertificate`, a
reduction-exact-sequence package, `RingHom.Finite`, or the asserted finrank equality as an input.

**What was tried.**

1. The existing finite-Proj route was traced through `Geometry/Proj/Finite.lean` and
   `Geometry/Proj/Surjectivity.lean`. The reusable endpoint
   `projectiveAevalOfRadical_isFinite_of_homogeneous_module_generators` needs a finite family
   whose polynomial-module span is all of `C`; the present native predicate supplies no theorem
   constructing those generators from the actual Artinian quotient.
2. The regular-sequence/Hilbert route was traced through `Algebra/HilbertArithmetic.lean`.
   `DegreeOneReductionComponentExactSequence` can prove the coefficient recurrence, but the
   repository only accepts its multiplication, injectivity, and cokernel equivalence as supplied
   fields. There is no construction of it from `RingTheory.Sequence.IsRegular` and the graded
   ideal quotient. Supplying that structure publicly would recreate a prohibited bridge
   assumption.
3. Mathlib's global freeness result for lifting across a regular element,
   `Module.free_quotSMulTop_iff_free`, was considered. It assumes the scalar lies in the
   Jacobson radical and finite presentation. Polynomial variables are not in the Jacobson
   radical of `K[X₀,…,Xₘ]`, and finite presentation is itself unavailable before the
   desired finiteness theorem, so this does not prove the required polynomial-module freeness.
4. No theorem was found in the repository or imported Mathlib API that converts the literal
   component Hilbert equality
   `H_C(t) = (1 + c t + t²)/(1-t)^(m+1)` into either finiteness over the chosen parameter
   polynomial ring or generic rank `c+2`. Assuming either fact directly would only rename the
   old certificate and was therefore rejected.
5. The generic-rank route was then separated from the numerical multiplicity calculation.
   Mathlib's `Module.FinitePresentation.exists_free_localizedModule_powers`, together with
   `IsLocalization.finrank_eq` and `IsLocalizedModule.finrank_eq`, proves that the already finite
   parameter extension is free of its generic rank after inverting one nonzero polynomial. This
   route succeeds and is now exposed by the two declarations listed above. It does not by itself
   compute that rank: generic freeness transports the generic rank to a dense principal open but
   contains no Hilbert-numerator/multiplicity theorem.
6. The flat-origin-fiber route was tested using Mathlib's
   `Ideal.finrank_fiber_eq_finrank`. Under `Module.Flat`, `Module.Finite`, and a domain base this
   identifies the generic rank with the finrank of the parameter-origin fiber. This route is now
   implemented: the fiber is identified with the actual parameter quotient and the new concrete
   quotient recurrence proves its total length is `1 + c + 1`. Deriving `Module.Flat` is the
   remaining step.
7. A materially different local projective-dimension route was tested: localize the parameter
   ring at its homogeneous maximal ideal and use
   `ModuleCat.projectiveDimension_quotient_eq_add_length_of_isWeaklyRegular` successively along
   the regular parameters, followed by Auslander--Buchsbaum/miracle flatness. The available API
   does not supply the required projective-dimension calculation for the resulting finite
   residue-field module, and this route again needs the absent concrete degreewise quotient and
   Hilbert-length identification. An asymptotic Hilbert-leading-coefficient proof was also
   surveyed; the imported API has no graded finite-module Hilbert polynomial or multiplicity
   theorem from which to recover the generic rank.
8. The proposed Mathlib Cohen--Macaulay PR `#26218` was inspected at pinned head
   `f23bd79b64731268daa2f18db0682058a8b094c5`. It adds the depth/CM predicates, localization,
   associated-prime consequences, and preservation under quotient by regular elements and
   sequences. It does not add graded quotient components, a Hilbert-series or multiplicity API,
   Artinian-reduction length, standard-graded module finiteness/freeness over an hsop, or the
   generic-rank equality needed here. Pinning the whole project to that unmerged fork would
   therefore add migration and cache risk without closing this blocker; the project stays on
   its current Mathlib revision. The upstream `HilbertPoly` file likewise only treats rational
   formal power series and explicitly does not construct Hilbert polynomials of finitely
   generated graded modules.

Those routes did not construct the polynomial-module finiteness directly from the operational
Artinian reduction. The obstruction was mathematical infrastructure rather than a Lean
elaboration error in a nearly complete proof.

**Smallest mathematically explicit strengthening.** The paper-level coordinate-ring setup
should record that `C` is a finite-type standard graded `K`-algebra (equivalently here, a
homogeneous quotient of the ambient polynomial ring, with degree zero equal to `K` and the
algebra generated by degree one). This is native geometric data, not a downstream certificate.
The chosen parameters should be stated as a homogeneous system of parameters; algebraic
independence may be a field of that setup if it cannot first be derived from regularity and the
dimension encoded by the Hilbert series.

**Progress on 2026-08-20.** The first required bridge is now proved, in a geometric form that is
both certificate-free and slightly more general than the proposed regular-reduction statement:

```text
finite homogeneous components
+ finitely generated irrelevant ideal
+ every degree-n component lies in irrelevant^n
+ basepoint-free parameters
-> standardGradedAevalHom_toRingHom_finite_of_basepointFree
-> projectiveAevalOfRadical_isFinite_of_standardGraded_basepointFree

+ algebraic independence of the parameters
-> projectiveAevalOfRadical_isFinite_surjective_of_standardGraded_hsop
```

The proof obtains a uniform power of the irrelevant ideal inside the parameter ideal, chooses
bases only in the finitely many lower homogeneous degrees, and uses strong induction plus graded
projection of the parameter coefficients to prove that those elements generate `C` over the
parameter polynomial ring. Thus it constructs `RingHom.Finite` internally rather than receiving
it or a basis as input. Algebraic independence is then exactly the hsop input needed by the
existing finite-plus-injective surjectivity theorem. This removes supplied `RingHom.Finite` and
the free-basis certificate from the public finite-surjective endpoint.

**Resolution of the numerical blocker.** The missing concrete quotient development is now
implemented in `Algebra/NativeGorenstein.lean`. Lean proves the reverse kernel-to-range
inclusion, obtains the one-step finrank recurrence for the actual successive parameter ideals,
iterates it, derives the quotient Hilbert function `(1,c,1,0,...)` from the literal Hilbert
series, and proves
`degreeOneParameterIdeal_quotient_finrank : finrank K (C / (parameters)) = c+2`.

`Algebra/NativeParameterRank.lean` then implements the successful origin-fiber route. It proves
that the kernel of constant coefficient is the polynomial irrelevant ideal, identifies its map
with the actual parameter ideal, and proves a generic-rank/fiber equality from freeness at one
prime. It then localizes the regular parameter sequence and applies
`Module.free_quotSMulTop_iff_free` backwards to derive that freeness internally. The final
`genericRank_eq_add_two` computes the basis-free generic rank as `c+2`; no flatness, assumed local
or global freeness, free basis, H-vector certificate, exact-sequence certificate, or asserted rank
is accepted. The unmerged Cohen--Macaulay stack is therefore not required for this bridge.

**Remaining exact blocker: native geometric instantiation.** The next missing result must turn a
basepoint-free extreme Hankel kernel for the paper's coordinate ring into the regular hsop used by
the algebra theorem and the concrete finite Proj morphism. After that, the reduced-fiber open and
evaluation isomorphism must be specialized to this morphism. This is a geometric integration gap,
not a missing freeness or multiplicity theorem.

The concrete SOS cone task was completed while this algebraic route was being isolated: no Gram
map, Gram-kernel criterion, or numerical degree assumption appears in its public theorem.

That abstract boundary is now implemented as
`SOSConeDual.sosCone_isClosed_of_separating_multiplicative_evaluations`. Its only substantive
inputs are degree-one/degree-two multiplication, compatible point evaluations, and separation
of degree one. The proof constructs its finite coordinate basis and Gram map internally and
derives the required kernel condition from separation. The remaining milestone-2 closedness
task is therefore the density-to-separation proof for the paper's coordinate ring: the generic
graded-algebra adapter `SOSConeDual.gradedSOSCone_isClosed_of_separating_evaluations` already
constructs the multiplication and evaluation maps, and exposes only separation. No further
Gram certificate is needed.

## Milestone verification

At each milestone boundary run, in order:

```sh
lake env lean DelPezzoBlekherman/Algebra/NativeGorenstein.lean
lake build
lake env lean DelPezzoBlekherman/Audit/Axioms.lean
```

Then run the repository-wide scan for proof placeholders, custom axiom declarations, and stale
work markers, update this file plus `VerifiedExtensionStatus.md`, `DependencyGraph.md`, and the
README, and create one atomic commit.
