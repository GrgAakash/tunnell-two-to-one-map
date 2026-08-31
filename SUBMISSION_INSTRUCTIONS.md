# Palomar submission instructions

Palomar accepts a public GitHub repository at an exact commit, not a ZIP
upload. Publish this directory as the root of a public repository, commit it,
and retain the full 40-character commit SHA.

Entry A is the principal research submission. Entry B is retained as a finite
regression certificate, but should not be submitted as a standalone Palomar
entry unless Palomar confirms that the worked instance meets its independent
research-interest threshold. If both are submitted, they must be separate
entries from the same commit.

## Entry A: general conditional map

- Selected project: repository root
- Comparator path: `Palomar/EntryA/comparator.json`
- Metadata path: `Palomar/EntryA/formalization.yaml`

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
