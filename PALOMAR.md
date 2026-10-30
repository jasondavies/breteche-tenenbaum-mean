# Palomar submission package

Prepared for the [current submission instructions](https://palomar-registry.org/how-to-submit).
This is the substantive proof development, not a wrapper around another repository.

## Submission fields

| Field | Value |
|---|---|
| Public repository | `https://github.com/jasondavies/breteche-tenenbaum-mean` |
| Commit | Full 40-character SHA of the final committed and pushed snapshot; obtain with `git rev-parse HEAD` |
| Project path | Repository root (leave the optional path blank) |
| Comparator config | `comparator.json` (default) |
| Metadata | `formalization.yaml` (default) |
| Relationship | Responsible author/maintainer, confirmed by Jason Davies |
| Existing Palomar ID | Leave blank for a new result |

No submission or publication has been performed. The repository has no remote
configured yet, so there is no submission SHA. Only the immutable public snapshot
is reviewed; local uncommitted files do not count.

## Statement surface

`Challenge.lean` imports only Mathlib and has 210 lines (about 10 KiB).
Its thirty definitions give their full mathematical meanings. They are mirrored
from the Mathlib-only `BretecheTenenbaumMean/Definitions.lean` so that generated
helper declarations also match. `definition_names` is empty: no mathematical
notion is an unspecified definition hole.

`comparator.json` names ten results: the eight targets assembled by
`paper_main_results`, the exact Parseval formula, and absolute integrability.
`Solution.lean` imports their proved declarations. It does not import Challenge.
The Challenge has ten deliberate theorem-proof holes; the Solution development
has none. The separate axiom audit never loads the Challenge.

The necessary T-dependent cutoff in Proposition 2.1's lower tail is explicit.
The Challenge and metadata explain the other conventions and source corrections.
No independent human mathematical review is claimed.

## Local validation

Run from the repository root:

```sh
ruby scripts/validate-formalization.rb
python3 scripts/check-lean-sources.py
python3 scripts/check-palomar.py
bash scripts/check.sh
bash scripts/verify-comparator.sh
```

The metadata has also been validated against the upstream formalization.yaml
v0.4 JSON Schema. The module/size scan covers all local Lean sources, including
vendored modules. The project-specific preflight checks all ten comparison
targets, the definition block, dependency revisions, and the hashes of 15
vendored modules. After fetching dependencies,
`python3 scripts/check-palomar.py --check-dependencies` also checks all 127
imported Nair–Tenenbaum module hashes against the pinned Git revision
`0f778ee8366de1204c118e212264ef096ec82b49`, plus all 109 imported Tau Ceti
modules at the v4.35.0 release commit
`1f9b4414105d86e487a4ac4c3d3397076a44d0d2`. The root project's Mathlib
v4.35.0 pin is retained, overriding Tau Ceti's own Mathlib revision; this
combination builds without source adaptations. This additional check runs in
`scripts/check.sh` and CI. The Git ignore rules retain
all three paper/provenance JSON manifests.

The Comparator runner uses the Lean 4.35.0 bundled Lean checker, NanoDa and
con-ron, with the usual bubblewrap sandbox. It never disables that sandbox.
On this hosted environment bubblewrap required elevated process permissions;
the first sandbox-restricted attempt failed to create its network namespace.
The CI configuration enables the necessary namespaces on its disposable runner.

The full Lean build passed (9,514 jobs). The exhaustive axiom audit checked
7,347 project, vendor, and imported dependency declarations and found only `propext`,
`Classical.choice`, and `Quot.sound`. Metadata validation, the source scan,
and the provenance preflight all passed.

Comparator passed all ten statement comparisons, finishing with
`Your solution is okay!`. Lean's default kernel, NanoDa, and con-ron each
accepted the Solution; con-ron reported 88,550 accepted declarations in the
exported dependency closure.
These local checks completed on 2026-10-30 with Lean 4.35.0. GitHub CI has
not yet run because the snapshot has not been pushed.

## Publish the reviewed snapshot

After reviewing the prepared files, commit them and push to the public repository:

```sh
git remote add origin https://github.com/jasondavies/breteche-tenenbaum-mean.git
git push -u origin HEAD
git status --short
git rev-parse HEAD
```

If a remote has since been configured, use that remote instead of adding it again.
Wait for the committed snapshot's CI to pass and ensure `git status --short` is
empty. Then submit the full SHA at https://submit.palomar-registry.org/.
Palomar's verification/review and the later choice to register are separate steps.
For a future automated submission, use Palomar's agent protocol rather than
browser automation of its form. Preserve the private status-page link returned
by the intake service.
