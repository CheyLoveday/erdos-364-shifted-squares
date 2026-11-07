# Frozen Lean 4.35 selection: recovered inputs

**Input recovery and offline staging: checked. Fresh Linux build and six-checker
reproduction: not run.** This package prepares the separately frozen October
selection for a new replay. It does not close that reproduction target yet.

Start with [the input inventory](INPUTS.md), [the current receipt](RECEIPT.md),
and [the Linux replay plan](REPLAY.md). The [October assurance note](../../verification/LEAN-ASSURANCE-2026-10-25.md)
and its receipts retain their historical meaning. For the completed public
Lean 4.31 reproduction, use [the separate public package](../public-c663b4e/).

## Check and stage the inputs

With Python 3.11 or later, from this directory:

```sh
python3 stage_inputs.py check
python3 check_staging.py
python3 stage_inputs.py stage /absolute/path/to/NEW_OUTPUT_DIRECTORY
```

These commands require no network, Lean installation, provider, or credentials.
They check the frozen identities and safely materialise two separate source
trees, the compiler options, path manifests, original inspection helpers and
aggregate module. They do not download dependencies, compile Lean, or launch
checkers. An existing output directory is refused. Keep a failed output for
diagnosis and choose a new directory for another attempt.

Every generated file is listed in `staging-receipt.json`, with its input source
and SHA-256. The receipt also records the generator hash and command. Generated
files are execution inputs, not new editable proof authorities; regenerate them
from this package. The original archive remains authoritative for the 61 Lean
files. Candidate and reference copies are deliberately identical to the original
selection; their comparison does not supply independent mathematical review.

`SHA256SUMS` lists the package files except itself. Verify it with
`sha256sum -c SHA256SUMS` on Linux or `shasum -a 256 -c SHA256SUMS` on macOS.
It identifies this package, not any future compiled result.

## Scope

The fixed target is 61 source modules, three selected theorem declarations and
their complete required logical dependency closure under Lean 4.35.0. The
historical compiler options are `autoImplicit=false` and `maxRecDepth=100000`.
The exact nine dependency revisions and checker binary digests are retained.

The archive is a historical verification input, not a second manuscript or an
upgrade of the public Lean 4.31 source release. It includes the recorded
`LeafCompiler.lean` compatibility change and two later LAB dependency versions.
No new mathematical result, whole-Erdős-364 claim, external human review,
service qualification, or historical receipt repair is asserted.

## Next step

Select a Linux/amd64 runner and resource envelope, complete the runner-specific
containment and execution steps in [REPLAY.md](REPLAY.md), and retain a new
receipt for the actual run. The current PR is an input-and-staging delivery;
it contains no unattended cloud launcher or finished end-to-end replay wrapper.
