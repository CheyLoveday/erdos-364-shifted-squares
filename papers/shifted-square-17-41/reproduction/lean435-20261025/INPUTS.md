# Exact verification inputs

This package freezes the mathematical sources and verification selection used
by attempt `fc-project-f9a2ea7611fde9af3bdc5efce0d03356`. It was prepared against
public repository base `fd35ce953306db0361a376e2b1993f5f2e0eb32f`, after PR #8.
The package's own Git commit, rather than that base, identifies its new files.

## Source authority and custody

`frozen/source.tar` is the recovered original archive, not a reconstruction from
current LAB. The original candidate and reference archives were byte-identical:

```text
bytes: 1443840
SHA-256: 6b6e03af11d97237a5c3616ccd2ae5985f95a8940a3c373bca208bdb64bd3001
```

All 61 regular members match the paths, sizes and SHA-256 values in the
[already-public October configuration](../../verification/records/2026-10-25-lean435/artifacts/project-config.json).
The historical LAB base was `4cb014775b335f29cf749ea6a49c3493dd68f287`, with dirty
inputs; that commit alone does not identify the verified source. Original
archives were recovered from the archived formal-code request, under
`var/validation/paper-i-durable-20261024-03/request/{candidate, trusted}/`.
No private repository access is needed to use the supplied archive.

Relative to the public 4.31 source, the three changed local modules are
`LeafCompiler.lean` (the recorded 4.35 compatibility port),
`PellDivisibilityRank.lean` and `QuarticPellCohn.lean` (later LAB dependency
versions). These are historical differences, not edits to the public source.
The audit is retained as `PaperTheoremAxiomAudit.lean` at the archive root.

The executable source allowlist is exactly those 61 archived Lean files and
four small inspection/preparation helpers. No service configuration, credentials,
provider launcher, whole private repository history, or unrelated research
material is included.

## Lean and dependency pins

| Input | Immutable identity |
| --- | --- |
| Lean | 4.35.0, source commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Linux/amd64 |
| Linux release archive | [lean-4.35.0-linux.tar.zst](https://github.com/leanprover/lean4/releases/download/v4.35.0/lean-4.35.0-linux.tar.zst), 594481375 bytes, SHA-256 `7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d` |
| Cli | [c24fe6078c630e89b489bffe59b3e20ac30d12c8](https://github.com/leanprover/lean4-cli/tree/c24fe6078c630e89b489bffe59b3e20ac30d12c8) |
| LeanSearchClient | [d6b4c7be5be75ec4917c873ac50c756dc1436372](https://github.com/leanprover-community/LeanSearchClient/tree/d6b4c7be5be75ec4917c873ac50c756dc1436372) |
| Qq | [dce0ad79c486cb1fb504af04f953c3466b0c6db8](https://github.com/leanprover-community/quote4/tree/dce0ad79c486cb1fb504af04f953c3466b0c6db8) |
| aesop | [4a174c490d8707121c4a9290800489f105d85e07](https://github.com/leanprover-community/aesop/tree/4a174c490d8707121c4a9290800489f105d85e07) |
| batteries | [66e469188fe07963e5cf666c7d4433f45b8131c5](https://github.com/leanprover-community/batteries/tree/66e469188fe07963e5cf666c7d4433f45b8131c5) |
| importGraph | [a41f0e9a4dea23188ea9cc1c41ac9f8bbafe0b93](https://github.com/leanprover-community/import-graph/tree/a41f0e9a4dea23188ea9cc1c41ac9f8bbafe0b93) |
| Mathlib | [56a005855ea17e0b0958f73ec801ae140b0a1679](https://github.com/leanprover-community/mathlib4/tree/56a005855ea17e0b0958f73ec801ae140b0a1679) |
| plausible | [dfa4f38190d07c37e315953e08b90fe2d95b3c24](https://github.com/leanprover-community/plausible/tree/dfa4f38190d07c37e315953e08b90fe2d95b3c24) |
| proofwidgets | [df72b022e558978a1c50264cfc4d7fec86fa8e04](https://github.com/leanprover-community/ProofWidgets4/tree/df72b022e558978a1c50264cfc4d7fec86fa8e04) |

[frozen/mathlib-recipe.json](frozen/mathlib-recipe.json) also pins each repository
URL, Git tree, configuration, manifest, toolchain file and source-tree digest.
Its byte hash `b69e6425f952a21738765a9d2a2527f6935a15020243bdf658a9df629b9a72b0`
matches `spec_digest` in the October environment receipt.
[frozen/lean-recipe.json](frozen/lean-recipe.json) retains the original Lean
download, Ubuntu image and package recipe. Its historical recipe identifier
uses canonical JSON; its ordinary file checksum is recorded separately.
The frozen environment receipt says `PREPARED_UNQUALIFIED`; it is not fresh
platform qualification, and its Modal image identifier is not an OCI digest.

All nine public Git commit/tree identities and the Lean release asset metadata
were checked on 7 November 2026. See [checks/public-pins.json](checks/public-pins.json).
The dependency source archives and Lean binaries were not downloaded or executed
by this input-staging review.

## Selection and original helpers

The exact comparison endpoints are:

1. `Erdos364.no_sm2LucasReal_shiftedSquare_of_positive_even_index`
2. `Erdos364.no_sm2LucasReal_shiftedSquare_of_positive_index_factor`
3. `Erdos364.ss41_shiftedSquare_impossible`

`frozen/project-config.json` retains all 61 roots, 16 dependency entry modules,
`autoImplicit=false`, `maxRecDepth=100000`, and no module exclusions. The
comparison permits only `propext`, `Classical.choice` and `Quot.sound`.

The original `Build.py`, `Inventory.lean` and `Inspect.lean` bytes match their
hashes in the [October manifest](../../verification/records/2026-10-25-lean435/manifest.json).
They, and the small `HashInputs.lean` utility, were recovered from formal-code
commit `ccebe537a8605483f0b504021a489e7579a23b84`. Their source paths and hashes are
in [frozen-inputs.json](frozen-inputs.json). These copies are frozen execution
inputs, not a maintained fork of that service. The new staging script is the
only added implementation; it never imports or executes those helpers.

`frozen/tools.json` pins Lean, Lake, the exporter and all six checker binaries.
It also contains the historical Python executable hash. A future runner must
record its Python/OS versions and explain any environment difference rather
than describe a source-equivalent result as byte-identical service execution.

## Inputs, outputs and preservation

The frozen archive, configurations, recipes and helpers are necessary replay
inputs. Staged Lake files are generated path adapters. Prior receipts and
`checks/` are evidence for inspection; they are never accepted as a new replay.

The historical reference and candidate exports were each 336350990 bytes with
SHA-256 `9602ca17bcc0ac6bcbd19cf3977f5825c66877fdd1bf0d394e94939f4d32776e`.
A fresh run must generate and hash its own exports. Preserve and explain any
difference; do not change frozen inputs to force that hash. Keep large exports,
compiled dependencies and complete run logs outside Git, under a new retained
run directory with a checksum manifest.

The October run reused compiled checkpoints. Its successful result is not an
empty-cache build claim. The proposed fresh run starts with public sources and
no private compiled cache. Any later choice to reuse a public cache needs an
explicit identity and provenance record before execution.
