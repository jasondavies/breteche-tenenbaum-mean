# Selected prime number theorem sources

This directory contains the 15-module import closure of `StrongPNT` copied
byte-for-byte from the user's example project, `../iwaniec-linear-sieve`.
The selected files and their SHA-256 hashes are recorded in [SNAPSHOT.json](SNAPSHOT.json),
which pins that project's revision and also records the sources of the adapted
`BretecheTenenbaumMean/PrimeSums/Error.lean` and `Mertens.lean` modules.

The original mathematical source is
[PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd),
revision `127b50e33f6033e2147921167a117af96d9ba4ea`. Its Apache-2.0 license is
preserved in [LICENSE](LICENSE); the example project's license is preserved in
[IWANIEC-LICENSE](IWANIEC-LICENSE).

[UPSTREAM.json](UPSTREAM.json) is the example project's original provenance
record, including its import renaming, module-system conversion and Lean 4.35
module import patches. Upstream already uses Lean 4.35.0: current HEAD was
downloaded on 29 October 2026 and all 14 original mathematical source hashes
were verified to match this revision. The retained patches support our module
conversion, not a Lean-version upgrade. It describes a larger source collection: its
`IEANTN/Mertens.lean` entry is **not included here**. `SNAPSHOT.json` is the exact
inventory for this project. `Architect.lean` supplies only blueprint annotation
syntax; it introduces no mathematical axioms.

The source is built locally against the same pinned Mathlib as the rest of
this project. There are no path dependencies on the sibling project, no
additional remote Lake packages, and no Tau Ceti dependency. The axiom audit
in `scripts/CheckAxioms.lean` checks every declaration in these modules as well
as the project's own modules.
