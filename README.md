# A two-to-one map for Tunnell's ternary forms

[![Palomar CI](https://github.com/GrgAakash/tunnell-two-to-one-map/actions/workflows/ci.yml/badge.svg?branch=main&event=push)](https://github.com/GrgAakash/tunnell-two-to-one-map/actions/workflows/ci.yml)

This Lean 4 project formalizes the deterministic two-to-one map developed in
the manuscript *Stable Matching and a Two-to-One Map for Tunnell's Ternary
Forms* by Aakash Gurung and Kyungyong Lee.

Manuscript versions, PDFs, TeX sources, and worked examples are listed in
[Papers/README.md](Papers/README.md).

## Mathematical scope

For every odd positive squarefree congruent number `n`, Tunnell's theorem
establishes the identity `|B(n)| = 2|A(n)|`. Combining that theorem with the
formalized construction gives an executable map from representations by
`2x^2 + y^2 + 8z^2` to representations by
`2x^2 + y^2 + 32z^2`, with exactly two distinct preimages over every target.
The Lean interface isolates the established cardinality identity as an
explicit hypothesis because Tunnell's modular-form argument is outside this
formalization. This is a formalization boundary, not a conjectural assumption.

The repository also contains an unconditional finite certificate at `n = 41`,
including the representation counts, residual matching, a literal proposal
trace certificate, and two complete fibres. The supporting Lean library also
certifies the companion note's full sixteen-row table: its target column is the
exhaustive 16-point target roster, and its 32 flattened entries are exactly the
graph of the public map on the exhaustive source roster.

## Formal verification

This formalization is registered in the Palomar Registry as
[PALOMAR-2026-09-07-000010 v2](https://palomar-registry.org/entry.html?id=PALOMAR-2026-09-07-000010&version=2).
Its Comparator, Lean kernel, and NanoDa checks succeeded.

Palomar is a registry of machine-checked results, not a journal or a substitute
for expert mathematical peer review.

## Local verification

```text
lake build
lake build +Solution
lake build +Palomar.EntryB.Solution
```

The Solution modules contain no `sorry`. The deliberate holes occur only in
the statement-only Challenge modules. The project declares no custom axioms;
the compared results use only `propext`, `Quot.sound`, and
`Classical.choice` where required by Mathlib constructions.

GitHub Actions checks the metadata and licence, builds the Lean project, and
runs pinned Comparator and NanoDa checks for both Entry A and Entry B. The
badge above reports this repository's CI status, not Palomar registration or
editorial approval.

To run the CI support tests locally:

```text
ruby test/validate_formalization_test.rb
ruby scripts/validate-formalization.rb
ruby scripts/validate-formalization.rb Palomar/EntryB/formalization.yaml
./test/landrun_wrapper_test.sh
ruby test/verify_comparator_test.rb
```

On Linux with Git, Go, Rust/Cargo, Python 3, Lean, and Landlock support, run
the full statement comparisons with:

```text
./scripts/verify-comparator.sh
./scripts/verify-comparator.sh Palomar/EntryB/comparator.json
```

## Palomar entries

The general map (Entry A) is registered under the record linked above, using
the root-level Comparator configuration. Entry B remains an optional finite
regression entry; it is not separately registered and should be submitted
separately only if Palomar confirms that it has independent research interest:

| Entry | Comparator | Metadata |
|---|---|---|
| General map under the Tunnell balance | `comparator.json` | `formalization.yaml` |
| Executable `n = 41` certificate | `Palomar/EntryB/comparator.json` | `Palomar/EntryB/formalization.yaml` |

Entry A registers the explicit local branches, the residual-target property,
and the projectively ranked stable residual perfect equivalence with its
preferred-sign lift and uniqueness among stable perfect equivalences, in addition to the exact
two-preimage theorem. The Challenge specifies
the mathematical output; the full generator and deferred-acceptance machine
implementation and correctness proofs remain in the supporting library.
The supporting library also proves the manuscript's partial-matching
convention is equivalent here: on finite complete bipartite sides of equal
size, every stable partial matching is perfect, and the stable partial matching
is unique.

Both public maps are fallback-free. Entry A also registers a fallback-free
residual map and inverse, agreement with the assembled map, and both inverse
identities. The submitted Solution computes the inverse by rerunning the same
deterministic machine; the Comparator contract determines it extensionally.
Entry B registers the literal trace and the images of events accepted by free
targets; the submitted
Solution links it to the instrumented run, but that producer linkage is not
independently reconstructed by Entry B's Mathlib-only Challenge.

## Assistance and acknowledgements

The development used OpenAI ChatGPT and Codex through a human-directed
solver-referee workflow, and Aristotle (Harmonic) for substantial Lean proof
development. Human review of the mathematical arguments, cited sources,
exposition, and manuscript-to-Lean correspondence is ongoing. The work grew
out of the 2026 IPAM RIPS program at UCLA and was supported by OpenAI's
sponsorship of the RIPS project.

The Lean repository snapshot is licensed under Apache-2.0. The cited
mathematical literature and external dependencies retain their own licences.
