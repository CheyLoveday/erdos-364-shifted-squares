# Additional Lean assurance for Paper I — 25 October 2026

**The frozen Lean formalisation selected for Paper I—61 source modules and
their required logical dependency closure—passed all six checkers bundled
with Lean 4.35.0. Its three selected theorem statements matched the frozen
reference, and their dependencies passed the standard-axiom check.**

The selected formal verification is **PASS**. The broader release-assurance
record remains **INCOMPLETE**. This is an evidence update for a named snapshot,
not certification of every mathematical claim in the manuscript or a new
article/evidence release.

## Results and foundations

Each linked execution receipt records `complete: true`, `returncode: 0`,
`errors: []` and confirmed process cleanup.

| Checker | Result | Original execution receipt |
| --- | --- | --- |
| Lean's `leanchecker` | PASS | [Receipt](records/2026-10-25-lean435/artifacts/leanchecker-positive.json) |
| `leanchecker-paranoid` | PASS | [Receipt](records/2026-10-25-lean435/artifacts/leanchecker-paranoid-positive.json) |
| Lean4Lean | PASS | [Receipt](records/2026-10-25-lean435/artifacts/lean4lean-positive.json) |
| Nanoda | PASS | [Receipt](records/2026-10-25-lean435/artifacts/nanoda-positive.json) |
| con-leche | PASS | [Receipt](records/2026-10-25-lean435/artifacts/con-leche-positive.json) |
| con-ron | PASS | [Receipt](records/2026-10-25-lean435/artifacts/con-ron-positive.json) |

The separate [protected inspection receipt](records/2026-10-25-lean435/artifacts/inspect-positive.json)
and [comparison configuration](records/2026-10-25-lean435/artifacts/comparison.json)
cover the three selected statements and the permitted foundations:
`propext`, `Classical.choice` and `Quot.sound`. The accepted result excludes
`sorryAx` and additional unapproved axioms; it is **not an axiom-free claim**.
The [Nanoda configuration](records/2026-10-25-lean435/artifacts/nanoda.json)
does not itself make unpermitted axioms a hard error, so its exit code alone
must not be used as the strict axiom audit. That audit is part of the separate
protected inspection and validated evidence chain.

These passes provide strong evidence for the validity of the selected formal
proof terms under the recorded foundations. They are six executable passes,
not six independent mathematical proofs. The hardened native checker shares
its underlying implementation with the native checker; the checkers also
share the selected exported input and foundational assumptions. The
[Lean 4.35.0 release documentation](https://lean-lang.org/doc/reference/latest/releases/v4.35.0/)
describes the bundled checker implementations and allocator hardening.

## Exact scope and source correspondence

The run selected `project_all`, `reachable_dependencies` and
`DEPENDENCY_COMPLETE`: all 60 selected `Erdos364` source modules plus
`PaperTheoremAxiomAudit`, and their required logical dependency closure.
This does not mean all of Mathlib or all of the current Lab repository.
The [project configuration](records/2026-10-25-lean435/artifacts/project-config.json)
retains every selected module, source-file hash and target declaration.

The three statement-comparison targets are:

| Declaration | Existing paper-facing correspondence |
| --- | --- |
| `Erdos364.no_sm2LucasReal_shiftedSquare_of_positive_even_index` | [Free positive-even-index theorem](../reading/theorem-formal-crosswalk.md#free-positive-even-index-shifted-square-theorem) |
| `Erdos364.no_sm2LucasReal_shiftedSquare_of_positive_index_factor` | [All-positive-index factor theorem](../reading/theorem-formal-crosswalk.md#all-positive-index-factor-theorem) |
| `Erdos364.ss41_shiftedSquare_impossible` | [Fixed-index 41 theorem](../reading/theorem-formal-crosswalk.md#ss41-pure-fixed-index-theorem) |

The selected sources came from Lab commit
`4cb014775b335f29cf749ea6a49c3493dd68f287`, with one reviewed compatibility
change to `Erdos364/SquareMiddle/LeafCompiler.lean`: import
`Mathlib.Data.Fintype.Sum` and replace the deriving-clause `Fintype` with an
explicit `derive_fintype%` instance. The run used Lean **4.35.0** and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`. The
[environment receipt](records/2026-10-25-lean435/artifacts/environment.json)
and [binary identities](records/2026-10-25-lean435/artifacts/tools.json)
identify the selected environment and checker executables. The preparatory
environment receipt retains its original `PREPARED_UNQUALIFIED` label; it is
not itself the successful run receipt.

The public v1.0.0 source release still pins Lean 4.31.0. A byte comparison
against public commit `4aba4a5ea2d243bc49c4ec31e805bdabe599619a` found
**58 of the 61 selected source files identical**, mapping the audit module
back to `verification/PaperTheoremAxiomAudit.lean`. The three differences are:

| Selected file | Difference from the public source release |
| --- | --- |
| `Erdos364/SquareMiddle/LeafCompiler.lean` | The Lean 4.35 compatibility change described above. |
| `Erdos364/SquareMiddle/PellDivisibilityRank.lean` | Later Lab additions present in the frozen selection. |
| `Erdos364/SquareMiddle/QuarticPellCohn.lean` | Later Lab additions present in the frozen selection. |

The files containing all three selected theorem declarations,
`ShiftedSquarePropagation.lean` and `Sm2LowerSquareOuterFortyOne.lean`, are
byte-identical to that public revision. Their dependencies and toolchain
still differ as specified above. The new result belongs to the frozen
selection; it does not retrospectively turn the public Lean 4.31 build into
a six-checker run or verify later Lab changes.

## Evidence identity and recovery

The [validated final receipt](records/2026-10-25-lean435/artifacts/validated-receipt.json)
records `verification_status: PASS`, `assurance_status: INCOMPLETE`, the
selected coverage and both export identities. The
[evidence-validation process](records/2026-10-25-lean435/artifacts/validate-evidence.json)
also completed successfully. Its validation checked the source, dependency,
export, checker-input, comparison and receipt bindings on the retained remote
bytes; this documentation update has not rerun the checkers.

| Identity | Recorded value |
| --- | --- |
| Attempt | `fc-project-f9a2ea7611fde9af3bdc5efce0d03356` |
| Candidate and frozen-reference source bundle SHA-256 | `6b6e03af11d97237a5c3616ccd2ae5985f95a8940a3c373bca208bdb64bd3001` |
| Configuration SHA-256 | `0afabc828da289ddfaac724a7eb374102c98b10559e38c1def0550ec683c6c04` |
| Each exported proof environment | 336,350,990 bytes; SHA-256 `9602ca17bcc0ac6bcbd19cf3977f5825c66877fdd1bf0d394e94939f4d32776e` |
| Committed evidence-checkpoint SHA-256 | `2b3fc75dff13426196b93b1058c9d662c3b65032c4fc7156013f84100298f516` |

Candidate and reference use the same selected source bundle, and their
exports are byte-identical. Matching that frozen reference establishes
formal agreement; equality does not itself establish an independent human
semantic review of the manuscript.

The original local controller did not finalize. The remote supervisor
completed and committed its evidence, which was subsequently recovered and
reviewed. The original controller journal remains `UNKNOWN`; the separate
recovered result is `RECOVERED_SCOPED_VERIFICATION_PASS`. The retained build
records show 61 resumed modules for each of the candidate and reference,
two current no-build checks each, and fresh inventories and exports. This
was not a fresh compilation of every module from an empty cache.

The retained read-only automated review by `review_nanoda_correction`
reported no blocking findings in the recovered result, checkpoint hashes,
scope, checker outcomes and cleanup. Its report is retained in `formal-code`
at commit `46199cd907d6cdc1e224ed1e27365b7896227cb3`, path
`plans/implementation/paper-i-recovery.review.md`, SHA-256
`26ac4aa03e36398e35b7775d15c4153b13fbcc29d59f4f9537b7c8c9645460d4`.
This is automated evidence review, not independent human mathematical review.

The accompanying [original checkpoint manifest](records/2026-10-25-lean435/manifest.json)
is retained unchanged. The 14 files under its `artifacts/` subdirectory
are a bounded public metadata subset, each matching the original manifest's
byte length and SHA-256. Execution receipts, environment and configuration
were copied; `tools.json`, `comparison.json` and `nanoda.json` were recovered
from the frozen inputs and checked against those same original byte hashes.
The manifest also names artifacts not included here. In particular, the
large proof exports, source archive, inventories and raw output streams have
not been copied into this repository. These metadata support inspection of
the recorded outcome; they are not a complete public replay bundle.

## What remains outside this result

The [theorem–formal crosswalk](../reading/theorem-formal-crosswalk.md),
[proof record](../reading/PROOF_RECORD.md) and
[Hilbert–Jacobi crosswalk](../reading/hilbert-jacobi-crosswalk.md) remain
necessary to assess correspondence with the paper. The human Hilbert-reciprocity,
maximality and Pell arguments are not made Lean-formalised by checking the
integer-Jacobi and recurrence development. Lean's
[validation guidance](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)
distinguishes proof validity from the meaning of the formal statement.

Broader release assurance remains **INCOMPLETE**: this receipt does not
complete the paper-to-Lean semantic review, establish a clean independent
reproduction, or supply independent human mathematical review. It does not
establish journal peer review, a new release, canonical acceptance or a
solution of Erdős Problem 364. The article editions, publication sources,
original proof records and earlier execution receipts retain their existing
identities and status.
