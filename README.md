# A two-to-one map for Tunnell's ternary forms

This Lean 4 project formalizes the deterministic two-to-one map developed in
the manuscript *Stable Matching and a Two-to-One Map for Tunnell's Ternary
Forms* by Aakash Gurung and Kyungyong Lee.

The manuscript source is `2_to_1.tex`, with its BibTeX database in
`references.bib`. Its records follow the MathSciNet BibTeX format and were
checked with AMS BatchMRef. The bibliography is rendered with the standard
`amsplain` style, including MR numbers for every matched record.

The separate companion `n41_complete_fibre_table.tex` and its PDF give the
complete execution of the map at `n = 41`: all 16 targets, all 32 sources,
their two-element fibres, and the manuscript result supporting each branch.

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
trace certificate, and two complete fibres.

## Verification

```text
lake build
lake build +Solution
lake build +Palomar.EntryB.Solution
```

The Solution modules contain no `sorry`. The deliberate holes occur only in
the statement-only Challenge modules. The project declares no custom axioms;
the compared results use only `propext`, `Quot.sound`, and
`Classical.choice` where required by Mathlib constructions.

## Palomar entries

The root-level Comparator configuration is the principal Palomar submission,
following the same single-entry layout as the submitted factorial-hypergraph
repository. Entry B remains an optional finite regression entry and should be
submitted separately only if Palomar confirms that it has independent research
interest:

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
development. The authors reviewed the mathematical statements and the
manuscript-to-Lean correspondence. The work grew out of the 2026 IPAM RIPS
program at UCLA and was supported by OpenAI's sponsorship of the RIPS project.

The Lean repository snapshot is licensed under Apache-2.0. The cited
mathematical literature and external dependencies retain their own licences.
