# Palomar submission instructions

Palomar accepts a public GitHub repository at an exact commit, not a ZIP
upload. Publish this directory as the root of a public repository, commit it,
and retain the full 40-character commit SHA.

The manuscript for this prepared submission is `Papers/v1/2_to_1.tex`, with
its PDF, bibliography, and companion example note in `Papers/v1/`. Keep the
Lean project and the principal submission files at the repository root.
Preserve v1 once submitted; put subsequent manuscript revisions in
`Papers/v2/`, `Papers/v3/`, and so on. After registration, record the Palomar
identifier and checked commit in [Papers/README.md](Papers/README.md).

Entry A is the principal research submission. Entry B is retained as a finite
regression certificate, but should not be submitted as a standalone Palomar
entry unless Palomar confirms that the worked instance meets its independent
research-interest threshold. If both are submitted, they must be separate
entries from the same commit.

## Entry A: general map under the Tunnell balance

- Selected project: repository root
- Comparator path: `comparator.json`
- Metadata path: `formalization.yaml`
- Challenge path: `Challenge.lean`
- Solution path: `Solution.lean`

## Entry B: optional finite certificate at n = 41

- Selected project: repository root
- Comparator path: `Palomar/EntryB/comparator.json`
- Metadata path: `Palomar/EntryB/formalization.yaml`

For the authorization question, the submitter must truthfully select either
that they are a responsible author or maintainer of the formalization, or that
they have approval from one. Repository write access alone is not the
authorization statement.

Before publishing, both authors should confirm the public authorship metadata,
Aakash Gurung's maintainer role, and use of Apache-2.0 for the submitted
repository snapshot. No ORCID is included because none was verified.

Do not publish local build products. The repository root includes a
`.gitignore` excluding `.lake/`, generated Lean object files, and common macOS
metadata. Before pushing, verify that the selected commit contains sources and
metadata but no `.lake` cache.

The local preflight performed for this candidate includes a full source build,
direct builds of both Solution modules, metadata validation against the current
Palomar template validator, licence and dependency checks, forbidden-construct
scans, and source-archive integrity testing. Palomar's protected Comparator,
Landrun, and NanoDa checks run after submission against the selected public
commit; this package does not claim those protected checks have already run.
