# Hosted Lean 4.35.0 verification · 19 November 2026

**The selected formal verification passed.** A frozen 61-module candidate and a separately built reference with the same source bytes passed all six checkers, the strict axiom audit and protected comparison of three Lean statements. An independent engineering reviewer rehashed the evidence and replayed the receipt offline with exit 0.

| Check | Observed result |
| --- | --- |
| Candidate and reference builds and exports | All four stages completed with exit 0 |
| Owned declaration coverage | 3,870 declarations reconciled with zero missing, extra or conflicting entries |
| Strict axiom audit | All exported axioms inspected. The audit found only `propext`, `Quot.sound` and `Classical.choice` |
| Protected comparison | All three theorem interfaces passed, including binder annotations and their referenced definitions |
| Retained evidence | Committed and verified. Offline receipt replay exited 0. Sandbox and process cleanup were confirmed |
| Claim assessment | `NOT_REQUESTED`. Formal assurance remains `INCOMPLETE` and consumer acceptance remains `NOT_ASSERTED` |

| Checker | Result | Exit |
| --- | --- | --- |
| `leanchecker` | PASS | 0 |
| `leanchecker-paranoid` | PASS | 0 |
| `lean4lean` | PASS | 0 |
| `nanoda` | PASS | 0 |
| `con-leche` | PASS | 0 |
| `con-ron` | PASS | 0 |

## Formal scope

The protected declarations cover positive even indices, positive indices divisible by 17 or 41, and the fixed 41 exclusion. The manuscript describes the Lean Jacobi route and the separate human proofs of Hilbert reciprocity and the Pell analysis. The replay covers the selected Lean declarations and dependencies. [October proof assurance](../../../../verification/LEAN-ASSURANCE-2026-10-25.md)

- `Erdos364.no_sm2LucasReal_shiftedSquare_of_positive_even_index`
- `Erdos364.no_sm2LucasReal_shiftedSquare_of_positive_index_factor`
- `Erdos364.ss41_shiftedSquare_impossible`

## Replay inputs and export identity

The frozen public source archive plus these exact Lake files reconstruct the 64-member source archive used for both roles. The normalized source SHA-256 is `fd097574db89819ade3f6bdb97fabac7117e393e8a04faf3b6a5432dba5e546e`. The run used a pinned prepared Mathlib cache, Lean 4.35.0, and an explicitly pinned compatible Nanoda binary. [Frozen source](../../frozen/source.tar) · [Toolchain](lean-toolchain) · [Lake configuration](lakefile.toml) · [Dependency lock](lake-manifest.json)

Both exports contain 336,278,853 bytes with SHA-256 `86984e389ed72f834b0ec9d3494e0114e9223f6268f73fd3e1be7baa254294d9` and match the earlier November hosted exports. The October assurance packet records 336,350,990 bytes and SHA-256 `9602ca17bcc0ac6bcbd19cf3977f5825c66877fdd1bf0d394e94939f4d32776e`. The two campaigns used different export preparation and dependency acquisition procedures. The cause of the byte difference remains unresolved. [October frozen identities](../../frozen-inputs.json)

The execution and retained inspection used the recorded odProof runtime and its hosted evidence store. The public files let a reader reconstruct the source inputs. Reproducing the hosted runtime and its result independently from the public package remains pending. [Linux replay plan](../../REPLAY.md) · [Machine-readable result](RESULT.json)
