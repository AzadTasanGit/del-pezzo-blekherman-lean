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
Hilbert equation. The finite-Proj/degree bridge and the concrete geometric instantiations remain.
See `docs/CompletionPlan.md` for the authoritative critical path and
`docs/FormalizationStatus.md` for the detailed inventory.
