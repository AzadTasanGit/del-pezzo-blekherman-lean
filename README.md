# Del Pezzo--Blekherman formalization

Lean 4 formalization of results from *A Del Pezzo--Blekherman Separation Theorem for
Arithmetically Gorenstein Varieties of Quadratic Deficiency One*.

The project is intentionally layered: machine-checked linear algebra, convexity, fiber algebra,
projective geometry, and SOS results live in the canonical `DelPezzoBlekherman` library. The
remaining boundary between the paper's arithmetically Gorenstein hypotheses and the explicit
Lean interfaces is recorded without silently weakening the main theorem.

## Layout

- `DelPezzoBlekherman.lean` -- root import for the complete checked library graph.
- `DelPezzoBlekherman/` -- Lean modules grouped by mathematical subject.
- `DelPezzoBlekherman/Audit/Axioms.lean` -- explicit axiom audit (kept outside the root import
  because it prints audit results).
- `docs/CompletionPlan.md` -- authoritative critical path and final public-signature policy.
- `docs/FormalizationStatus.md` -- PDF-to-Lean statement correspondence and remaining gaps.
- `docs/DependencyGraph.md` -- checked theorem chain and outstanding bridges.
- `docs/Progress.md` and `docs/VerifiedExtensionProgress.md` -- chronological work logs.
- `docs/MathlibAudit.md` -- audited mathlib infrastructure.
- `references/DelPezzoBlekhermanSeparation2026.pdf` -- source paper.

## Verification

From the repository root:

```sh
lake build
lake env lean DelPezzoBlekherman/Audit/Axioms.lean
```

The root build reaches every theorem module. The audit module is checked separately so its
`#print axioms` output remains visible without becoming part of normal imports.

## Current status

The codebase contains no `sorry`, `admit`, or custom `axiom` declarations. The first native
algebra boundary now states the regular Artinian reduction and perfect socle multiplication
directly and proves the paper's Hankel kernel/rank conclusion from that predicate and the literal
Hilbert equation. A basepoint-free homogeneous system of parameters now gives a finite
surjective Proj morphism from explicit standard-graded hypotheses, without a supplied module
basis or finiteness certificate. `DelPezzoBlekherman.theorem1_1_i` now proves the paper's concrete
SOS cone is closed and identifies its dual with the positive-semidefinite Hankel functionals.
It derives degree-one separation from genuine Zariski density in the spectrum of the reduced
coordinate ring; the coordinate basis and Gram map stay internal, so no Gram representation,
Gram-kernel, or supplied closedness assumption appears in its public interface. The
concrete point-evaluation branch and exclusive evaluation/basepoint-free-kernel dichotomy of
Theorem 1.1(ii) are also proved without a supplied Gram-kernel or abstract dichotomy. The
paper's indefinite-form argument now excludes every complex basepoint whose degree-one
evaluation has real rank two, and the native Gorenstein theorem supplies the kernel dimension
and Hankel rank once regular parameters have been selected. Identifying real versus nonreal
projective evaluations, extracting those regular parameters, proving degree `c+2` from the
Hilbert numerator, and the remaining geometric conclusions still remain.
See `docs/CompletionPlan.md` for the authoritative critical path and
`docs/FormalizationStatus.md` for the detailed inventory.
