# Progress log

## 2026-08-09

- Read the complete 17-page source PDF, including proofs and footnotes.
- Confirmed the workspace initially contained no Lean project.
- Located Lean `v4.33.0-rc2` and a prebuilt mathlib checkout at commit
  `51e6992efd06126df61a496bebf8f49482a4e129`.
- Chose the layered representation described in `docs/FormalizationStatus.md`.
- Created the project skeleton, initial dependency graph, and status table.
- Began compiler-backed API exploration for Lemmas 3.2 and 6.1.
- Proved and compiled PDF Lemma 6.1 using mathlib's `QuadraticForm.sigNeg`.
- Proved the PSD zero-value/radical equivalence and the kernel-uniqueness implies
  extreme-ray direction of Lemma 3.2.
- Proved a general hyperplane restriction radical theorem for nondegenerate symmetric
  bilinear forms.
- Formalized the perfect-pairing kernel and rank mechanism used at the end of
  Theorem 4.3, with the missing Gorenstein derivation kept as an explicit dependency.
- Completed the finite-dimensional real diagonal classification: reciprocal identity,
  exact radical line, at most/exactly one negative coefficient, and the weighted
  Cauchy--Schwarz converse (`diagonal_kernel_face_classification`).
- Proved the normalized complex reciprocal formula and the forced sign `α < 0`.
- Completed the Lorentzian hyperplane classification (Lemma 7.3): nondegeneracy,
  the reciprocal representative and scalar identity, exact radical line, the
  two-real-dimensional complex null inequality, and the PSD converse via weighted
  Cauchy--Schwarz (`lorentz_kernel_face_classification`).
- Proved that the complex block supplies a negative direction and used an explicit
  vector in the relation hyperplane to force every real coefficient positive;
  assembled the one-conjugate-pair coefficient classification
  (`lorentz_one_pair_kernel_face_classification`).
- Proved the multiple-complex-block inertia theorem
  `complexDiagonal_at_most_one_pair`: a PSD restriction to the kernel of any real
  functional forces the complex-block index type to be subsingleton (the
  finite-dimensional core of Proposition 6.2).
- Proved the generic rank-one evaluation theorem: the square of any nonzero linear
  functional spans an extreme ray in every symmetric bilinear-form subspace that
  contains it (`rankOne_spansExtremeRay`), covering Corollary 3.3's abstract core.
- Proved the abstract Lemma 4.1 dichotomy: an extreme PSD form with a basepoint in
  a nonzero evaluation family is a positive multiple of that rank-one evaluation;
  otherwise its radical is basepoint-free, and proved the alternatives exclusive.
- Added the finite evaluation-algebra layer for Proposition 5.2: dimension-count
  lemmas turn injective degree-one/two evaluation into a hyperplane/isomorphism,
  and quotient-pairing radical perfection forces every relation coefficient nonzero.
- Proved the compact-slice extreme-minimizer step in Lemma 8.1 using an exposed
  minimizer face and Krein--Milman (`exists_extremePoint_isMinOn`).
- Proved the normalization correspondence needed in Lemma 8.1: an extreme point of
  a slice by a functional strictly positive on nonzero cone elements spans an
  extreme ray (`extremePoint_normalizedSlice_spansExtremeRay`).
- Completed Lemma 8.1: proved compactness of the normalized dual slice from an
  interior ball, oriented Hahn--Banach separators into the dual cone, and selected
  extreme-ray functionals which are strictly negative outside the cone or vanish
  at a boundary point.
- Proved Proposition 3.1's exact dual-cone identity abstractly for finite sums of
  values of any square map (`nonnegative_on_finiteSumCone_iff`).
- Completed an abstract finite-dimensional Gram-model version of Proposition 3.1:
  proved the PSD matrix cone closed, identified its linear image with finite sums
  of squares using PSD factorization, proved the closed-image norm criterion,
  derived the zero-kernel condition from spanning real evaluations, and combined
  closedness, convexity, nonempty interior, and the exact dual identity.
- Derived the Gram conic-scaling law automatically from rank-one matrices and
  replaced the raw evaluation-spanning assumption by the faithful statement that
  no nonzero linear functional vanishes on every real evaluation vector.
- Completed all of Lemma 3.2: proved a compact-unit-sphere domination bound for a
  positive-definite form, lifted it across a complement of the PSD radical to get
  `Q ± εP`, and assembled the full equivalence as `kernel_face_criterion`.
- Formalized Proposition 2.1's Hilbert-numerator arithmetic, including the doubled
  quadratic-deficiency identity, degree `c+2`, and `a`-invariant `1-m`.
- Proved the hyperplane-annihilator lemma used in Proposition 5.4: any functional
  vanishing on the kernel of a nonzero functional is its scalar multiple.
- Proved the accompanying conjugation lemma: proportional conjugation-compatible
  coordinate vectors have a real proportionality scalar.
- Added existence and uniqueness of weighted coordinate representations of
  functionals through a finite evaluation isomorphism, completing the finite
  coordinate part of Proposition 5.4.
- Added `docs/MathlibAudit.md`; current mathlib has strong bilinear, convex, regular
  sequence, Proj, and finite-morphism foundations, but no packaged Cohen--Macaulay,
  Gorenstein, or Hilbert-series theory.
- Repeated `lake build` successfully after integration; placeholder count remains zero.
- Proved the converse extreme-ray/extreme-point normalization in Lemma 8.1 and
  the conditional final separation assemblies for Theorems 8.2 and 8.3, which
  rule out point-evaluation rays by nonnegativity or strict positivity.
- Specialized both final convex assemblies to the paper's concrete evaluation-ray
  shape `a • evₓ` with `a > 0`.
- Proved the supported-Gram rank bound used in Theorem 8.3: a PSD Gram matrix
  annihilated by a nonnegative support functional has range in the functional's
  nullspace and rank at most its dimension.
- Proved that a supporting nonnegative functional vanishes on every square in a
  supported representation, and formalized the terminal conjugate-pair counting
  contradiction for a reduced fiber with no real points.
- Began the Gram-rank/SOS-length equivalence: defined the Gram matrix of a finite
  square family, proved it PSD and mapped to the corresponding sum of squares,
  and proved its rank is bounded by the number of summands. The reverse direction
  is isolated to a nonzero-eigenvalue spectral expansion.
- Completed that spectral expansion: every real PSD matrix is a sum of rank-one
  Gram matrices indexed by its nonzero eigenvalues, whose cardinality mathlib
  identifies with matrix rank. Combined both directions into the exact
  Gram-rank/SOS-length conversion.
- Applied the conversion to a supported boundary SOS, producing an explicit
  square representation with at most `finrank K` summands; this proves the
  `m+1` upper bound once the Hankel nullspace has dimension `m+1`.
- Proved by well-ordering that every finite SOS has a shortest `Fin r`-indexed
  representation, and strengthened the supported upper bound to a shortest
  representation lying termwise in the support nullspace.
- Proved that every shortest SOS family is linearly independent: dependence
  lowers the Gram rank, while PSD spectral decomposition supplies a strictly
  shorter family representing the same element.
- Formalized the next lower-bound step from Theorem 8.3: any independent family
  of length `r ≤ m` in an `(m+1)`-dimensional nullspace is contained in an
  `m`-dimensional subspace of that nullspace, constructed as the kernel of a
  nonzero linear functional.
- Proved the hyperplane common-zero/projective-fiber identity: an evaluation
  functional vanishes on `ker f` exactly when it is a scalar multiple of `f`.
- Formalized the topology and counting in the reduced-fiber perturbation: a dense
  good-fiber locus meets the complement of a compact real image, and a good fiber
  with at least three geometric points and no real point has at least two conjugate
  pairs, contradicting an at-most-one-pair inertia bound.
- Assembled a single conditional exact-length theorem for Theorem 8.3.  From the
  support data and strict positivity, Lean now constructs a shortest representation,
  proves its length at most `m+1`, and rules out length at most `m` by extending it
  to an `m`-plane and proving that plane basepoint-free.  The theorem isolates only
  the paper's remaining geometric `m`-plane obstruction as an explicit hypothesis.
- Proved the real-algebraic density fact used in that obstruction: the zero set
  of a nonzero real multivariate polynomial in finitely many variables has empty
  Euclidean interior, by analytic uniqueness; hence any algebraic subset contained
  in such a zero set has dense complement.
- Instantiated the compact-image part for continuous maps from compact sources:
  the fiber-pair hypotheses force surjectivity, so an omitted target point yields
  the desired contradiction.
- Connected the basepoint-free hyperplane to mathlib's algebraic projectivization:
  Lean constructs the projectivized evaluation map, proves every evaluation is
  nonzero, and proves that the projective point defined by the hyperplane is not
  in its range.
- Added a literal natural-number `sosLength`, proved it is attained for every
  element of the finite-sum cone and agrees with every shortest representation,
  and strengthened the conditional Theorem 8.3 assembly to conclude
  `sosLength sq p = m+1` exactly.
- Replaced the last opaque `m`-plane obstruction by a composable theorem:
  compactness and continuity, density of the good-fiber locus, an omitted target
  point for each basepoint-free plane, and the two fiber pair-count inequalities
  now mechanically imply that no such plane exists.
- Added the fully expanded conditional Theorem 8.3 assembly, which consumes those
  compact-map and fiber-count inputs directly and concludes both the existence of
  a shortest `m+1`-term representation and `sosLength sq p = m+1`.

## 2026-08-13: repository integration

- Initialized Git and committed the exact pre-migration workspace as a reversible baseline.
- Moved all verified extension modules out of the permission-era staging tree and into the
  canonical subject hierarchy under `DelPezzoBlekherman/`, removing every `Scratch` suffix.
- Added the extension endpoints to `DelPezzoBlekherman.lean`, so a normal `lake build` now
  compiles the complete checked theorem graph.
- Consolidated status material under `docs/`, moved the paper to `references/`, and added the
  repository-level `README.md`.
- Rebuilt all 71 theorem modules successfully, checked the separate axiom audit, and confirmed
  there are no proof placeholders or missing compiled modules.

## 2026-08-13: induced-socle-functional rank bridge

- Re-read PDF Proposition 2.2 and Theorem 4.3 and isolated the step applying the induced nonzero
  functional on the one-dimensional degree-two socle.
- Proved that this specific functional is injective, preserves nondegeneracy of the Gorenstein
  multiplication pairing, and gives the actual pulled-back Hankel form radical dimension `m+1`
  and rank `c` without choosing an auxiliary socle coordinate.
- Proved that pointwise factorization through quotient multiplication identifies the original
  ambient Hankel form with that pullback, hence its actual radical is the parameter space and its
  kernel dimension/rank are `m+1`/`c`.
- Added the new endpoint to the axiom audit, ran the full 3,717-job build, and confirmed the
  placeholder scan remains empty.
