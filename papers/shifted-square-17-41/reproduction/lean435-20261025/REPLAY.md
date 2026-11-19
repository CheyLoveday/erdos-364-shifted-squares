# Linux replay plan — execution pending

This is a runner handoff, not a claim that an end-to-end recipe has passed.
The owner selected an input-and-staging PR first and a runner decision afterward.
No archived provider configuration or old budget authorises a new cloud run.

## 1. Select and record the environment

Use Linux/amd64 with the pinned Lean 4.35 release. Record the OS, kernel,
Python, bubblewrap and libc versions, available disk, CPU/memory allocation,
outer limits, selected wall-clock ceiling and retention location before work.
The original recipe used Ubuntu 24.04 and bubblewrap 0.9.0, with an eight-CPU,
32-GiB machine envelope. These historical allocations are planning evidence,
not a measured capacity guarantee for a new runner. Choose and enforce the
new resource budget before provisioning or replay.

First validate filesystem isolation, disabled networking, timeout/cancellation,
log capture and cleanup on that runner. Use a separate unprivileged builder and
judge; do not grant either access to the owner's home or credentials. The
historical commands used `setpriv` and bubblewrap with user, PID, network, IPC,
UTS and cgroup namespaces, no capabilities, a cleared environment and read-only
root. Their complete invocations remain in the October per-checker receipts.
Do not weaken isolation merely to obtain a pass.

The remaining implementation is a small runner-specific command wrapper and
evidence collector around the steps below. Do not restart the archived service,
alter its journal or budgets, or introduce a new general verification framework.

## 2. Prepare public tools and sources

Preparation may use the network. Verification may not.

1. Download the exact Lean archive in [INPUTS.md](INPUTS.md); check its size and
   SHA-256 before extracting it to the isolated `/opt/lean` toolchain location.
   Verify the nine Lean/Lake/exporter/checker executable hashes in
   `frozen/tools.json`. Record the host Python hash separately.
2. Obtain all nine repositories at their exact commits in
   `frozen/mathlib-recipe.json`, not branch tips. Verify each Git tree and the
   pinned configuration, toolchain and manifest hashes before any execution.
   Preserve tracked modes and symlinks. Do not run `lake update` or substitute
   the public release's 4.31 manifest.
3. Run `stage_inputs.py stage NEW_DIRECTORY`. Its generated `inputs/` tree is
   mounted at `/inputs`. Place the checked packages at `/inputs/packages/NAME`.
   Every package's source remains read-only during verification; only its
   separate `.lake` build directory is writable during dependency preparation.
4. Complete the original ProofWidgets hash preparation with the pinned
   `helpers/HashInputs.lean`: read `package.json` as text, `package-lock.json` as
   bytes, `rollup.config.js` and `tsconfig.json` as text, and the sorted
   `.ts/.tsx/.js/.jsx` files under `widget/src` as text. The helper reads
   `/inputs/hash-inputs.json`, an array of `[absolute_path, text_boolean]` pairs,
   and prints Lake's hashes. Bind the resulting hash strings read-only at each
   corresponding `PATH.hash`. Keep the tracked widget assets; no npm install,
   unrecorded asset rebuild, implicit hydration or network access is permitted.

The package retains the original recipes rather than pretending that this
staging PR has recreated their compiled image. Any environmental change must
be stated in the new receipt.

## 3. Build, inventory and export separately

Use the staged manifests and `--packages=/inputs/overrides.json`; all dependency
resolution is explicit. With networking disabled, first build the 16
`dependency_modules` from `frozen/project-config.json` using:

```text
/opt/lean/bin/lake --no-cache --fail-fast --packages=/inputs/overrides.json
  -d /inputs/dependency-build build +MODULE:olean ...
```

The command above is a template: expand exactly the configured 16 module
names as separate argv entries. After that build, freeze and hash the dependency
outputs. Mount them read-only for both source builds and for every subsequent
step. This cache is produced by the new run, not restored from private history.

For each role, `reference` then `positive`, provide a fresh `/work`, map its
writable Lake metadata directory to `/inputs/proofs/ROLE/.lake`, and execute:

```text
/usr/bin/python3 -I -B /inputs/Build.py ROLE
```

`Build.py` is the original helper. It explicitly builds all 61 roots, compiles
the aggregate, emits a logical inventory, and serialises the entire selected
logical closure plus the fixed primitives. Its `inventory` and `export` modes
can split production if the selected runner requires separate disk sinks.
Use the historical builder settings `LEAN_NUM_THREADS=2`,
`LEAN_STACK_SIZE_KB=16384`, `LEAN_ABORT_ON_PANIC=1` and `LAKE_NO_CACHE=true`.
Retain full diagnostics, generated `.olean` inventories, both fresh logical
inventories, export sizes/hashes and source/dependency hashes before and after.

Do not count a generic green default target as checking these roots. Do not
reuse a successful reference build as the candidate build without an explicitly
revised scope and receipt.

## 4. Judge serialised exports and retain separate outcomes

The judge receives only the read-only toolchain, original `Inspect.lean`,
frozen comparison/Nanoda configurations and the two exports. It receives no
candidate `.olean`, source metaprogram, package build tree, home or credential.
Use `LEAN_NUM_THREADS=1`, `LEAN_STACK_SIZE_KB=16384` and
`LEAN_ABORT_ON_PANIC=1` for the judge.

Parse each export using the original `Inspect.lean` in its one-export mode.
Compare the full name/reference graph with its builder's logical inventory:
all 61 roots must be represented, every selected endpoint must be owned by a
project module, the dependency closure must be complete, and there must be no
missing, extra or conflicting logical units. Retain nonlogical `unsafe`/`partial`
exclusions from Lean safety metadata; a name pattern is not a valid exclusion.
Reference and candidate ownership/exclusion inventories must agree.

Run the exact statement comparison and transitive axiom inspection:

```text
/opt/lean/bin/lean -j1 -s16384 -M0 --run /trusted/Inspect.lean
  /challenge/export.ndjson /inputs/export.ndjson /challenge/comparison.json
```

Then run each checker separately against the same candidate export:

| Checker | Argv after the isolation wrapper |
| --- | --- |
| Lean | `/opt/lean/bin/leanchecker --silent --from-export /inputs/export.ndjson` |
| Hardened Lean | `/opt/lean/bin/leanchecker-paranoid --silent --from-export /inputs/export.ndjson` |
| Lean4Lean | `/opt/lean/bin/lean4lean --import /inputs/export.ndjson` |
| Nanoda | `/opt/lean/bin/nanoda_bin /inputs/nanoda.json` |
| con-leche | `/opt/lean/bin/con-leche /inputs/export.ndjson` |
| con-ron | `/opt/lean/bin/con-ron /inputs/export.ndjson` |

The historical Nanoda setting `unpermitted_axiom_hard_error=false` is preserved.
Its exit status alone is therefore not the axiom gate. Require the protected
comparison/axiom inspection and explicitly check that the reported `used_axioms`
contain only `propext`, `Classical.choice` and `Quot.sound`. Reject `sorryAx`
and all additional axioms. Keep each exit code, stdout/stderr, tool hash, input
hash, elapsed time, timeout/truncation status and cleanup result separately.

## 5. Acceptance and new receipt

Report separate outcomes for input identity, dependency acquisition, source
builds, logical coverage, three statement comparisons, strict axiom inspection,
and each of the six checkers. Missing, skipped, timed-out or truncated required
checks cannot count as passed. Preserve failures before any corrected retry.

Success means another operator can reproduce those selected checks from public
inputs under a documented runner without the private working tree. Bind the new
receipt to the package commit and hashes, and name all differences from the
historical runtime and cache policy. Compare the two new exports and record
their relationship to the October hash; explain any discrepancy before claiming
the historical selection was reproduced.

Add a new dated run receipt and a small index update after execution. Do not
overwrite this preparation receipt, the October records, the public 4.31 locks
or sources, the public reproduction package, manuscript editions or release
assets. A scoped executable pass is not a full assurance-profile completion,
independent mathematical review, or a stronger mathematical theorem.

## Documentation checked for this handoff

Consulted 7 November 2026:

- [Lean 4.35 release notes](https://lean-lang.org/doc/reference/latest/releases/v4.35.0/): bundled checker suite, export support and Linux-only build sandbox.
- [Lean's CLI help at the pinned source](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/lake/Lake/CLI/Help.lean): explicit package overrides, `--no-cache`, `--no-build`, and module targets. A bare update upgrades dependencies.
- [bubblewrap 0.9.0 manual](https://github.com/containers/bubblewrap/blob/v0.9.0/bwrap.xml): ordered mounts, read-only bindings, cleared environment, network/PID/user namespaces and termination behavior. Distribution permissions and actual isolation still need verification on the selected host.

These source checks do not establish live runner compatibility. Research the
chosen host/VM/container platform's current official documentation and its exact
version before implementing that setup.
