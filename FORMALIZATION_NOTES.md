# Formalization notes

## Claim boundary

The manuscript's principal mathematical result applies to every odd positive
squarefree congruent integer `n`, because Tunnell's established theorem gives
the required cardinality identity. The general Lean interface isolates that
external theorem as the hypothesis

```text
Nat.card (BRep n) = 2 * Nat.card (ARep n)
```

and constructs an ordinary computable map with exactly two distinct and
exhaustive preimages over every target. Tunnell's modular-form proof, the
congruent-number criterion, and the elliptic-curve characterization of
congruent numbers are not formalized. This is a boundary of the Lean
development, not an unproved assumption in the mathematical theorem.

Entry A registers the fallback-free map, the exact two-preimage theorem, the
even branch, three explicit quarter-turn branches, the residual-target
property, and the projectively ranked stable residual matching with its
preferred-sign lift. Thus the registered claims exclude an arbitrary
permutation of residual targets. The short Challenge specifies the
family-level mathematical output; the supporting library contains the
stateful generator, deferred-acceptance implementation, and proof that the
implementation computes that output.

The supporting library also formalizes the manuscript's convention that a
stable matching may initially be partial. It uses Mathlib's standard
`PartialEquiv`: on finite complete bipartite sides of equal cardinality,
stability rules out an unmatched source and an unmatched target, hence every
stable partial matching is perfect. It then proves uniqueness among all stable
partial matchings by reduction to the registered uniqueness theorem for stable
equivalences.

The residual map and inverse are separately registered and fallback-free. The
submitted inverse reruns the same executable machine through an `Option`
interface; the registered statements prove agreement with the assembled map
and both inverse identities, determining the inverse extensionally rather than
its operational provenance.

Entry B is an unconditional finite certificate at `n = 41`: it proves the two
representation counts by exhaustive kernel computation and registers the
assembled map, four residual pairs, two complete fibres, and a literal
six-event deferred-acceptance trace certificate. In addition, the supporting
library contains the literal sixteen-row table from the companion note and a
kernel-checked certificate that its target column exhausts all 16 targets and
that its 32 source-target edges are exactly the full graph of the public map.
The submitted Solution
defines that list from the instrumented run, but the finite Challenge does not
independently reconstruct the full generator and therefore does not pin that
producer provenance.

## Manuscript correspondence

The formalization follows manuscript version v1 in
`Papers/v1/2_to_1.tex`. Its PDF, bibliography, and companion example note are
kept in the same folder. [Papers/README.md](Papers/README.md) records manuscript
versions and their Palomar correspondence; registration of the prepared v1
submission is pending.
Two cost statements were corrected during the formal
audit:

1. The `n = 41` run has six generator advances and six proposal-processing
   steps, of which exactly two compare a new key with a held record.
2. The general accounting theorem proves at most one held-key comparison per
   proposal, not exactly one comparison per proposal.

The Challenge modules use integer products instead of the project's `Triple`
structure. The Solution modules contain explicit coordinate equivalences. The
general public map and the `n = 41` registered map are both fallback-free.
The registered literal trace has two events that are not acceptances by a free
target. The supporting development retains the richer outcomes and proves that
both are rejections. A separate machine-level counter theorem proves that the
same run performs two key comparisons against held records; neither fact is
inferred from the registered Boolean count.

The complete companion table is certified in
`TunnellMap/N41TotalMap.lean` by `completeFibreTable41_targets` and
`completeFibreTable41_certificate`. The first theorem checks that the sixteen
rows list the exhaustive target roster. The second identifies the flattened
thirty-two table entries, up to order, with the graph obtained by applying the
public fallback-free map to the exhaustive source roster.

## Verification performed before publication

The proof development was rebuilt from source with Lean 4.28.0 and
the Mathlib revision pinned in `lake-manifest.json`. The full build and both
Solution-module builds succeeded. Executable regressions at `n = 5` and
`n = 41` passed.

The Solution modules and the underlying `TunnellMap` library contain no
`sorry` or `admit`; deliberate holes occur only in the two Challenge modules.
Source scans found no project axiom, `unsafe`, `opaque`, `extern`,
`implemented_by`, `native_decide`, `Lean.ofReduceBool`, or
`Lean.trustCompiler`. Axiom inspection of the repaired principal declarations
found only subsets of `propext`, `Classical.choice`, and `Quot.sound`.

Palomar's protected Comparator, Landrun, and NanoDa checks are not claimed as
local results. They are performed by Palomar's mechanical verifier against the
exact public commit selected at submission.
