# Reproduction target and immutable inputs

## Scope

This package reproduces selected checks for the **public release** at
`c663b4e1e65c99846d41270a288f154559cc9fd6`.
It is **not** a reconstruction of the separately frozen Lean 4.35 six-checker
selection, and it does not combine that selection's sources with the public
release's dependencies. No modifications to the earlier assurance records
are made or implied.

The target consists of:

- dependency and source identity checks;
- Lean build of `Erdos364.DicksonLucas.ShiftedSquarePropagation`;
- elaboration of the 17 selected paper declarations and four supporting
  declarations in `verification/PaperTheoremAxiomAudit.lean`;
- the allowed-axiom check on their `#print axioms` output;
- the GP17, GP41 and independent fixed-field certificates;
- the independent finite, propagation, Jacobi block, Jacobi certificate and
  Jacobi telescope checks.

Human-only Hilbert, maximality and Pell routes, the full six-checker run and
full publication/TeX reproduction are outside this target.

## Public inputs

| Input | Identifier and SHA-256 |
|---|---|
| Source archive | `https://codeload.github.com/CheyLoveday/erdos-364-shifted-squares/tar.gz/c663b4e1e65c99846d41270a288f154559cc9fd6` |
| Archive SHA-256 | `f9ea4c1cf80f3223e9e0a7b27bffac27b92ab4b75b2827ed472cb1a50d8d9e74` |
| Lean archive | `https://github.com/leanprover/lean4/releases/download/v4.31.0/lean-4.31.0-linux.tar.zst` |
| Lean archive SHA-256 | `07a633cc8d9151cbc08825ea4cdda50d4b02a2c9cb852c0131b13046f49cad7f` |
| Required Lean | `leanprover/lean4:v4.31.0` in `lean-toolchain` |
| Lean build commit | `68218e876d2a38b1985b8590fff244a83c321783` |
| Required Mathlib | `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` in `lakefile.toml` and `lake-manifest.json` |
| Python packages | Exact hashes in `verification/requirements.lock` |
| Verifier scripts | Exact files named in `reproduce.sh` at the source commit |

The nine Lake dependencies are identified by the exact revisions and URLs in
`lake-manifest.json` at the source commit. The usual public Mathlib build cache
matching those versions is obtained with `lake exe cache get`.

PARI/GP 2.17.3 and Python 3.11 or later are required. The recorded experiment
uses Python 3.12.14, SymPy 1.14.0, mpmath 1.3.0, beautifulsoup4 4.14.3,
soupsieve 2.8.4 and typing-extensions 4.16.0.

## Declared metadata reconciliation patch

The public commit contains four stale checksum/provenance entries: three in
`SHA256SUMS` (for `README.md`, the manuscript `revision/README.md`, and
`theorem-formal-crosswalk.md`) and one duplicate stale crosswalk hash in
`verification/imports.json`. Updating the latter changes its own digest, so a
fifth entry in `SHA256SUMS`, covering `verification/imports.json` itself, must
also be adjusted. Unpatched, `sha256sum -c SHA256SUMS` reports the first three
documentation mismatches, and `run_core.py` rejects the crosswalk hash before
executing Lean. The independent package run detected and retained the
additional self-hash requirement.

`metadata-hashes.patch` is therefore a **required, explicitly declared** input
of this reproduction recipe. It changes only those five checksum values to the
appropriate digests of the pinned public bytes (including the digest of the
reconciled `imports.json` file). It
does not alter document bytes, definitions, theorem statements, proofs or
verifier scripts. The `source_revision` provenance field in `imports.json` is
left unchanged. The patch and unmodified upstream manifests
[`SHA256SUMS.upstream`](SHA256SUMS.upstream) and
[`imports.upstream.json`](imports.upstream.json) are retained so the change is
fully inspectable rather than hidden. Both unpatched preflight failures are
recorded in the receipt.

A reproduction that excludes all metadata patches must report the preflight
failure rather than silently treating the official core runner as having
passed.

## Cache policy

- No private Git history or private build output is used.
- The downloaded public Lake dependency cache is allowed and recorded. The
  experiment does not require an artificially empty network cache.
- `LEAN_PATH` is unset during Lean operations. A locally downloaded Lean 4.31
  toolchain is used, not the host's Lean 4.35 or `/opt/mathlib` installation.
- `TMPDIR` is set within the reproduction workspace.
- Resources used in the recorded run: 4 CPUs, 15 GiB RAM, and ample storage
  for the public Mathlib cache and project build outputs. Prepare at least
  several GiB of free space and a network connection for downloads.
- Existing output directories are deliberately not overwritten.

`reproduce.sh` is a necessary input of this package. Files under `logs/` and
`RECEIPT.md` are reproduction outputs retained for inspection, not proof
inputs. The source archive and Lean archive are kept only in the scratch
workspace, not duplicated here.

## Run

From an independently provisioned runner with Bash, curl, zstd, tar, Python 3
and PARI/GP available:

```bash
bash reproduce.sh NEW_OUTPUT_DIRECTORY
```

The script downloads only the pinned inputs above, writes each operation's log
and exit status separately, and stops with nonzero status if any reported step
fails. A successful Lean build is not treated as shorthand for the other
operations. The unpatched documentation and import-manifest mismatches are
preserved in this receipt, after which the declared metadata patch and full
`sha256sum -c` run are also checked; no preflight failure is silently waived.
