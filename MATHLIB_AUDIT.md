# Mathlib infrastructure audit

Audited against mathlib commit `51e6992efd06126df61a496bebf8f49482a4e129`
(`v4.33.0-rc2`, 2026-08-03). Searches were made in source and important APIs were
checked in compiling scratch files before use.

## Available and already used

- Symmetric bilinear forms: `LinearMap.BilinForm`, `LinearMap.BilinForm.IsSymm`.
- Positive semidefiniteness: `LinearMap.BilinForm.IsPosSemidef` and its nonnegative
  diagonal field.
- Bilinear radicals: `LinearMap.ker B`; mathlib's PSD Cauchy--Schwarz theorem
  `LinearMap.BilinForm.apply_apply_same_eq_zero_iff` identifies zero quadratic values
  with the radical.
- Restrictions and orthogonal complements:
  `LinearMap.BilinForm.restrict`, `LinearMap.BilinForm.orthogonal`, and
  `LinearMap.BilinForm.finrank_orthogonal`.
- Inertia: `QuadraticForm.sigPos`, `sigNeg`, and Sylvester-law results in
  `Mathlib.LinearAlgebra.QuadraticForm.Signature` and `.Real`.
- Finite-dimensional rank/nullity and complement infrastructure:
  `LinearMap.finrank_range_add_finrank_ker`, `IsCompl`, and submodule finrank lemmas.
- Real symmetric-matrix spectral decomposition and eigenvalue/rank formulas, used
  to convert PSD Gram rank exactly into SOS length.
- Basis extension and dual separation of a proper subspace by a nonzero linear
  functional, used to place a short independent family inside a prescribed
  codimension-one subspace.
- Hausdorff compactness and density APIs, used for the Euclidean perturbation
  from a point outside the compact real image into the dense good-fiber locus.
- Analyticity of multivariate-polynomial evaluation, analytic uniqueness on
  connected real vector spaces, and polynomial function extensionality over
  infinite domains; together these prove density of real principal opens.
- Convex cones and faces: `ConvexCone`, `PointedCone`, `ProperCone`,
  `PointedCone.IsFaceOf`, and general convex `IsExtreme`.
- Dual closed cones and separation: `ProperCone.dual`,
  `ProperCone.hyperplane_separation_point`, and the geometric Hahn--Banach family.
- Graded rings/algebras: internal gradings via `GradedRing`/`GradedAlgebra`,
  homogeneous ideals, homogeneous localization, and graded base change.
- Regular sequences: `RingTheory.Sequence.IsWeaklyRegular` and
  `RingTheory.Sequence.IsRegular`, with quotient and permutation lemmas.
- Projective spectrum: `AlgebraicGeometry.ProjectiveSpectrum`, its scheme and
  structure sheaf, basic opens, and affine-chart comparison.
- Algebraic projectivization of a vector space and its scalar-equivalence API,
  used to construct the projective target point omitted by a basepoint-free
  hyperplane.  This algebraic type does not currently carry the finite-dimensional
  real quotient topology/compactness instance needed for the real-image argument.
- Scheme morphism properties: finite, proper, affine, etale, and quasi-finite
  morphism predicates; in particular `IsFinite.iff_isProper_and_isAffineHom`.
- Complex conjugation, real/complex linear structures, and explicit real/imaginary
  coordinate lemmas are present.

## Not found as packaged theories

Source searches found no mathlib declaration or file implementing:

- Cohen--Macaulay rings/modules;
- Gorenstein rings, Artinian Gorenstein algebras, canonical modules, or the
  perfect socle pairing theorem;
- Hilbert series/functions for graded algebras, multiplicity/degree extraction from
  a Hilbert numerator, or the Hilbert-series quotient-by-regular-sequence formula;
- a standard-graded coordinate-ring interface tying degree-one generation directly
  to projective embeddings;
- the specialized SOS/Gram cone for a graded coordinate ring;
- a ready-made theorem constructing the morphism associated to an arbitrary
  basepoint-free finite-dimensional subsystem of `O(1)`, or computing its degree
  from the eventual Hilbert function.

The absence claims above are about packaged APIs, not mathematical impossibility.
Regular sequences, Proj, and finite-morphism foundations exist, so parts of the
bridge can be developed locally. The Gorenstein/Hilbert-series layer is a substantial
independent commutative-algebra development and is tracked explicitly rather than
axiomatized silently.

## Representation consequence

The project therefore proves the independent finite-dimensional theorems directly,
packages the perfect-pairing conclusion needed from the Gorenstein reduction as a
transparent algebraic interface, and keeps the unproved derivation of that interface
from the PDF's ring hypotheses as a named bridge task. No theorem currently marked
proved assumes an unexplained custom axiom.
