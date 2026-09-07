# CI verification tools

The workflow, metadata validator, Landrun wrapper, and their tests are adapted
from [PalomarTemplate](https://github.com/PalomarRegistry/PalomarTemplate),
via the working [Moh repository CI setup](https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/tree/c288c1b9ecc2290d6c0ca07895b65fd726c0987c).
They are distributed under Apache-2.0, as in those repositories.

The Tunnell adaptations validate both metadata files and run Comparator for
both configurations. `verify-comparator.sh` accepts a repository-relative
configuration path, defaulting to `comparator.json`, and refuses a configuration
that does not enable NanoDa. It uses these fixed revisions:

| Tool | Commit |
|---|---|
| Comparator | `68a064109f01c08f47c8edc9f51d6a2bbffaa188` |
| lean4export | `d065b0009aed0520e9e99752847a33b337661690` |
| Landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` |
| NanoDa | `68d5ca9db226849b41a6fff59d796ff19d0a8840` |

The exporter targets Lean 4.28.0, matching this project's `lean-toolchain`.
Do not replace its revision with a newer template pin without checking Lean
and export-format compatibility. GitHub Actions installs the build tools on
Linux; a full replay downloads these repositories and writes generated files
under `.cache/` and `.lake/`, which are ignored by Git.

These are repository-owned pre-submission checks. They do not run Palomar's
editorial review or create a registry entry.
