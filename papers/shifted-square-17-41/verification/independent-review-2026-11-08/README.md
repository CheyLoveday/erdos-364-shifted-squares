# Independent review package — 8 November 2026

This directory preserves the curated evidence from an eight-direction mathematical and computational audit of the shifted-square paper at public mathematical baseline `c663b4e1e65c99846d41270a288f154559cc9fd6`.

**Start with [REVIEW.md](REVIEW.md).** It gives the verdict, scope, test inventory, corrected review errors and remaining limitations. [PROVENANCE.md](PROVENANCE.md) maps the preserved files to the original investigations.

This is an agent-assisted independent audit with referee review of its submissions. It is **not external human peer review**, a new journal acceptance, a solution of Erdős 364, or a formalisation of every human argument in the paper.

## Headline outcome

No mathematical error or counterexample was found in the paper. Six submissions were accepted after referee corrections. They provide:

- a kernel-checked paper-strength bridge for Theorems 1.1, 1.2, 1.3, the hard-phase conclusion of 4.2, and Corollary 1.4;
- independent reconstruction of all finite fixed-field certificates;
- direct local computation of the dyadic Hilbert signs;
- an expanded audit of the odd-prime/Hilbert–Jacobi bridge;
- a human proof extending the Jacobi identity to both phases of `A ≡ 2 (mod 4)`;
- published and independently rederived support for the Pell-rank argument;
- a proof that no fixed-modulus covering-congruence certificate exists;
- a corrected exhaustive numerical sieve for the Corollary 1.5 hypothesis class with `X ≤ 10^14`.

The only repository source correction made by this PR is a **comment-only** clarification in `experiments/sm2_four_translate/interpolation/outer41_verify.gp`: `c_0` multiplies `1`, not `D_0 = 2`. No detector, definition, theorem statement, proof or executable formula changes.

## Layout

- `REVIEW.md` — complete referee report and scope boundaries.
- `PROVENANCE.md` — origin map, review errata and exclusions.
- `reports/` — the six accepted full reports plus the independently checked Corollary 1.5 report and supporting mathematical notes.
- `scripts/` — runnable evidence, grouped by subject.
- `logs/` — captured axiom, build, arithmetic and sieve output.
- `provenance/` — the two small Lean-4.35 compatibility patches, retained as diffs rather than copied build trees.

Downloaded primary-source PDFs, extracted literature texts, `__pycache__`, Lean oleans and out-of-tree build directories are deliberately not included. The reports identify the relevant public sources; no missing cache is treated as a proof dependency.

## Selected reruns

Run from the repository root. Set:

```bash
PKG=papers/shifted-square-17-41/verification/independent-review-2026-11-08
```

### Finite certificates (51 checks)

```bash
python3 "$PKG/scripts/finite-certificates/verify_independent.py"
```

Expected final line: `FIXED_CERTIFICATE_INDEPENDENT_OK`.

### Direct dyadic signs

```bash
gp -q < "$PKG/scripts/direct-dyadic/dyadic17.gp"
gp -q < "$PKG/scripts/direct-dyadic/dyadic41.gp"
gp -q < "$PKG/scripts/direct-dyadic/nfhilbert_validation.gp"
```

Both dyadic products must be `-1`.

### Arbitrary-valuation odd-prime bridge

```bash
gp -q < "$PKG/scripts/hilbert/audit_bridge.gp"
gp -q < "$PKG/scripts/hilbert/audit_extra.gp"
```

### Corrected Corollary 1.5 audit and exhaustive sieve

```bash
python3 "$PKG/scripts/cor15/cor15_audit.py" selftest
python3 "$PKG/scripts/cor15/cor15_audit.py" E
python3 "$PKG/scripts/cor15/crosscheck_sympy.py"
```

The full `E` search covers every odd `y ≤ 10^7`; it currently reports **748,369 survivors and zero candidates**. Captured output is in `logs/cor15_sieve_output.txt` and `logs/cor15_sieve_selftest.txt`.

### Large exact-arithmetic statement audit

```bash
python3 "$PKG/scripts/formal/audit_statements.py"
```

Expected result: **2,078,952 assertions, 0 failures**, followed by `STATEMENT_AUDIT_OK`.

### Elementary-route computation

```bash
python3 "$PKG/scripts/elementary-routes/verify_route_scope.py"
python3 "$PKG/scripts/elementary-routes/route_scope_checks.py"
python3 "$PKG/scripts/elementary-routes/jacobi_extended.py"
python3 "$PKG/scripts/literature/walker.py" 5000
```

### Formal bridge build

The original audited build used Lean **4.35.0** and Mathlib `a3a10db`, not the repository's pinned Lean 4.31 / Mathlib `fabf563a`. Apply the two retained compatibility patches only to a scratch source copy. Do not overwrite the pinned public source.

```bash
AUDIT_SRC="$PWD/.scratch/lean-audit-src"
AUDIT_BUILD="$PWD/.scratch/lean-audit-build"
mkdir -p "$AUDIT_SRC" "$AUDIT_BUILD"
cp -a Erdos364 "$AUDIT_SRC/"
patch -d "$AUDIT_SRC" -p1 < "$PKG/provenance/leaf-compiler.patch"
patch -d "$AUDIT_SRC" -p1 < "$PKG/provenance/outer-forty-one-recursion.patch"
ERDOS_SRC="$AUDIT_SRC" ERDOS_BUILD="$AUDIT_BUILD" \
  python3 "$PKG/scripts/formal/build.py" --jobs 3
LEAN_PATH="$AUDIT_BUILD:$LEAN_PATH" lean -R "$AUDIT_SRC" \
  -o "$AUDIT_BUILD/PaperStatementBridge.olean" \
  "$PKG/scripts/formal/PaperStatementBridge.lean"
```

The accepted bridge's original build log is preserved in `logs/run_log.txt`; its printed types and axiom footprints are in `logs/printed_statements.txt` and `logs/axiom_footprint.txt`. This PR does not import the bridge into `Erdos364.lean` or alter the maintained proof surface.
