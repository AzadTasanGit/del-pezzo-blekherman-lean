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
| 1. Native algebraic boundary | Sol High | Introduce the operational regular-reduction predicate and make the actual Hankel rank endpoint consume it plus the literal Hilbert equation. Next extend this boundary to the degree-`c+2` Proj morphism without a free-basis certificate. | The rank declaration exposes none of the four algebra certificates listed above; the morphism declaration eventually exposes none either. | Rank endpoint complete; morphism bridge specified and blocked on two reusable graded-commutative-algebra lemmas |
| 2. Concrete SOS and Hankel layer | Terra Medium | Define the square map, multiplication/Hankel embedding, dual cone, and point evaluations for `𝒜 1` and `𝒜 2`. Prove closedness from the compact normalized-square argument and Zariski density, then instantiate `kernel_face_criterion` and `extreme_psd_evaluation_xor_basepointFree`. | `theorem1_1_i` and the evaluation branch and exclusive dichotomy of `theorem1_1_ii` compile with no Gram-kernel or abstract-dichotomy input. | queued after milestone 1 morphism decision |
| 3. Kernel morphism and reduced fibers | Terra Medium; Sol High for a recorded blocker | Connect the concrete basepoint-free kernel to `AlgebraicGeometry.Proj.projectiveAevalOfRadical`; prove finite surjectivity and rank `c+2`, instantiate the discriminant open locus, evaluation hyperplane, nonzero relation coefficients, and degree-two evaluation equivalence. | `theorem1_1_iii` compiles without an H-vector/free-basis certificate or supplied fiber data. | queued |
| 4. Fiber classifications and topology | Terra Medium | Identify the concrete evaluation form with `ComplexBlockFamily`; prove relation-kernel nonnegativity and block non-isotropy; instantiate the pair bound and both reciprocal classifications. Prove ordinary evaluation continuity and identify the real coordinate-ring source with `X(ℝ)` compatibly with projective evaluation. | `theorem1_1_iv`, `theorem1_1_v`, and every premise required by the concrete SOS-length theorem compile without block or continuity assumptions. | queued |
| 5. Final composition | Sol High review, Terra Medium integration | Add `theorem1_1_i` through `theorem1_1_vi`, compose them in `theorem1_1`, and reconcile every status document and audit entry. | All conditions in “Definition of done” hold. | queued |

## Current checked algebra boundary

`DelPezzoBlekherman/Algebra/NativeGorenstein.lean` now provides:

- `degreeOneParameterIdeal`, the actual homogeneous parameter ideal;
- `IsArithmeticallyGorenstein`, the regular, Artinian, one-dimensional-socle and perfect-pairing
  predicate described above;
- `moduleFinite_degreeOne_of_delPezzoHilbertSeries`, which consumes the literal equation rather
  than exposing a Hilbert certificate;
- `hankelKernel_eq_parameterSpan_and_rank_of_arithmeticallyGorenstein`, which concludes the
  actual Hankel kernel equality and rank `c` without any project-specific algebra certificate in
  its signature.

The internal construction of old interfaces in a proof is permitted; exposing one in a final
signature is not. The currently open algebra task is the finite-Proj/degree bridge. It is
specified precisely in the blocker log below. A global polynomial-module basis may be
introduced only if it is proved internally from the native hypotheses and removes, in the same
change, the `HVectorOneCOneFreeCertificate` hypothesis from the public morphism declaration.

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

There is consequently no honest compiling replacement theorem from the *current* native setup:
the obstruction is a missing formal bridge, not a Lean elaboration error in a nearly complete
proof.

**Smallest mathematically explicit strengthening.** The paper-level coordinate-ring setup
should record that `C` is a finite-type standard graded `K`-algebra (equivalently here, a
homogeneous quotient of the ambient polynomial ring, with degree zero equal to `K` and the
algebra generated by degree one). This is native geometric data, not a downstream certificate.
The chosen parameters should be stated as a homogeneous system of parameters; algebraic
independence may be a field of that setup if it cannot first be derived from regularity and the
dimension encoded by the Hilbert series.

With that setup fixed, the missing implementation should consist of two reusable theorems, not
new certificate structures:

1. `moduleFinite_parameterAeval_of_regular_artinianReduction`: graded Nakayama/induction lifts
   finite homogeneous generators of the actual quotient `C/(g)` and proves
   `(MvPolynomial.standardGradedAevalHom 𝒸 g hg).toRingHom.Finite`.
2. `finrank_parameterAeval_eq_numeratorAtOne`: for this finite graded parameter extension, the
   regular-reduction coefficient recurrence and literal Hilbert equation prove generic rank
   `1 + c + 1 = c + 2` (without requiring a globally supplied free basis).

The first theorem also unlocks existing finite-Proj machinery; injectivity/algebraic
independence then unlocks the existing surjectivity theorem. The second removes the final
`HVectorOneCOneFreeCertificate` use from the degree statement. Until these two lemmas exist,
milestone 3 must not consume the old certificate through a differently named adapter.

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
