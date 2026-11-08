# Provenance and inclusion policy

## Source identity

The mathematical audit examined the public repository at `c663b4e1e65c99846d41270a288f154559cc9fd6`. This package is added above merge commit `fd35ce953306db0361a376e2b1993f5f2e0eb32f`, which contains reproduction PR #8. The merged reproduction recipe is not changed by this audit.

The investigation ran as Ultramath swarm `smw70l62n` with eight members and a separate referee. Submissions were checked by reading their proofs and rerunning relevant programs. Rejected drafts were not accepted until corrected; the final Corollary 1.5 sieve was repaired and rerun by the referee instead of accepting the defective submitted file.

## Accepted report map

| Included report | Original investigated direction | Preserved runnable material |
|---|---|---|
| `reports/formal-statement.md` | m5 / d4 | `scripts/formal/`, `logs/run_log.txt`, `logs/printed_statements.txt`, `logs/axiom_footprint.txt` |
| `reports/finite-certificates.md` and `reports/theorem-1-2-rederivation.md` | m4 / d7 | `scripts/finite-certificates/` |
| `reports/direct-dyadic.md` | m3 / d2 | `scripts/direct-dyadic/` |
| `reports/hilbert-chain.md` | m6 / d3 | `scripts/hilbert/` |
| `reports/elementary-routes.md`, `reports/no-fixed-modulus.md`, `reports/route-scope.md`, `reports/elementary-conditions.md` | m7 / d5 | `scripts/elementary-routes/` |
| `reports/literature.md` | m1 / d6 | `scripts/literature/` |
| `reports/corollary-1-5.md` | m8 / d1, completed by referee correction | corrected `scripts/cor15/cor15_audit.py`, its cross-check, and `logs/cor15_*` |

Some per-direction reports retain their original working paths, such as `work/`, `cert/` or a historical `.ultramath/smw70l62n/` path. Those are references for provenance, not promises that temporary swarm directories ship in this PR. This table gives the corresponding packaged locations.

## Corollary 1.5 correction

The packaged `cor15_audit.py` is the submitted audit with exactly one mathematical-code correction:

```diff
- inv = pow(2 * y0 * (y0 * y0 + 1) % q, -1, q)
+ inv = pow(4 * y0 * (y0 * y0 + 1) % q, -1, q)
```

This makes the Hensel lift use `N'(y)=4y(y²+1)`. The corrected full search reports 748,369 survivors instead of the defective run's 748,263, and zero candidates. The complete corrected `all` output, the focused sieve output, self-test and SymPy cross-check are included under `logs/`.

## Lean artifacts

The actual audited Lean build products were out of tree and are not committed. `scripts/formal/build.py` supports `ERDOS_BUILD` so a reviewer can keep output in `.scratch/` or another external build directory.

The two changes it needed under Lean 4.35 / Mathlib `a3a10db` are retained only as:

- `provenance/leaf-compiler.patch`;
- `provenance/outer-forty-one-recursion.patch`.

They alter no theorem statement or proof step. The maintained public sources in this PR are not replaced by those patched copies.

## Deliberately excluded material

- downloaded books and paper PDFs, and their extracted text;
- temporary swarm workspaces and conversation records;
- `__pycache__`, temporary scripts and exploratory duplicates;
- `leanbuild/` directories, `.olean`/`.ilean` files and compiled caches;
- the full duplicated 60-module patched source tree.

The source literature is identified in `reports/literature.md` and by the paper's own bibliographic links. The proof checks do not depend on including those cached documents in the PR.

## Claims not made

This package does not assert journal peer review, a complete formal proof of the Hilbert argument or Corollary 1.5, a six-checker reproduction, a new detector, or a resolution of Erdős 364. The public reproduction, this independent audit and the separately frozen historical six-checker run remain distinct evidence packages.

## Checksum reconciliation for the comment edit

The `source_revision` on `outer41_verify.gp` in `verification/imports.json` remains its upstream import identifier. Its `sha256` now covers the comment-corrected bytes introduced here, and its role explicitly records a comment-only `c_0` correction. The root `SHA256SUMS` contains both that new file digest and the resulting new `imports.json` digest. This keeps direct hash verification working without pretending that the comment edit was present in the historical upstream source.
