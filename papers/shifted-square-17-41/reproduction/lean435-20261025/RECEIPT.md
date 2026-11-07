# Preparation receipt — 7 November 2026

**Recovered input identity and offline staging: PASS. Fresh Lean 4.35
reproduction: NOT_RUN.** The owner selected a reviewable preparation PR before
choosing a Linux/amd64 runner. No runner was provisioned or verification launched.

## What was checked

| Check | Result and evidence |
| --- | --- |
| Original source recovery | Candidate and reference archives are byte-identical; all 61 member paths, sizes and hashes match the original public configuration. [Recovery checks](checks/recovery.json) |
| Historical selection | Exact 61 roots, three endpoints, nine packages, compiler options and original comparison/Nanoda settings retained. [Frozen inputs](frozen-inputs.json) |
| Original verification helpers | Build, inventory and inspection helpers match the October manifest. Both generated project Lake files also match its recorded bytes. [Recovery checks](checks/recovery.json) |
| Public dependency availability | All nine commit/tree identities and the Lean release archive metadata match the pinned recipe. Metadata checks only. [Public pins](checks/public-pins.json) |
| Offline staging and rejection controls | Two fresh stagings are byte-identical; both retain every source byte. Existing outputs, corrupt input, duplicate/missing members, traversal and symlink members are rejected. [Check output](checks/staging.json) |
| Source-difference review | Exactly three historical module differences from the public release, listed in the recovery record. No new proof edit. |

Commands run for the executable offline checks:

```sh
python3 stage_inputs.py check
python3 check_staging.py
```

Both exited 0. Separate byte comparisons established the recovered helper and
generated Lake-file identities against the October manifest. Git diff and local
link checks are packaging checks; they do not establish Lean correctness or
visual mathematical typesetting. Temporary staging checks were removed after
passing; frozen inputs and the check results above are retained.

## What remains

| Required fresh check | Status |
| --- | --- |
| Runner/platform isolation and resource qualification | NOT_RUN |
| Downloaded dependency/tool binary identity and clean builds | NOT_RUN |
| Fresh logical inventories and export coverage | NOT_RUN |
| Three protected statement comparisons and strict axiom inspection | NOT_RUN |
| Lean, hardened Lean, Lean4Lean, Nanoda, con-leche and con-ron replay | NOT_RUN (each) |
| Independent review of the new PR's exact head | NOT_RUN |

The selected reproduction remains incomplete. The broader Lean assurance
release profile is **INCOMPLETE**, not waived by this bounded preparation task.
This receipt is an automated input/staging review by Codex in the assembly chat;
it is not an independent human mathematical review or a replay receipt.

## Preserved boundaries

PR #8 was merged as `fd35ce953306db0361a376e2b1993f5f2e0eb32f`; its public 4.31
reproduction package is unchanged. This preparation adds files under the new
`reproduction/lean435-20261025/` directory, a reproduction index, and one README
navigation link. It does not change the root Lean toolchain/locks or sources,
October receipts, manuscript editions, arithmetic verifier or release assets.
The old root checksum manifests are also retained; this is not a new v1.0.0
distributable release or an attempt to make its historical manifest cover new
navigation material. The new package has its own non-self-referential checksums.

No Lean build, GP/certificate replay, public dependency installation, paid
execution, archived service resumption, or release was performed. The next
bounded task is to choose a runner, finish the [execution wrapper and replay
checks](REPLAY.md), and add a separately dated result tied to exact inputs.
