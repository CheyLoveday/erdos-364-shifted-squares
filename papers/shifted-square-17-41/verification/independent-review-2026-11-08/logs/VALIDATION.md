# Final validation before the audit PR

Run from the repository root on 8 November 2026 unless the preserved per-direction log says otherwise.

| Check | Outcome |
|---|---|
| `gp -q -f experiments/sm2_four_translate/interpolation/outer41_verify.gp` | `OUTER41_CERTIFICATE_OK pari=2.17.3`, target `no_sm2LucasReal_forty_one_square_of_mod_eight_two` |
| `python3 scripts/finite-certificates/verify_independent.py` | 51 checks; `FIXED_CERTIFICATE_INDEPENDENT_OK` |
| `gp -q < scripts/direct-dyadic/dyadic17.gp` | signs `+1,+1,-1`, product `-1`, bare-theta product `+1` |
| `gp -q < scripts/direct-dyadic/dyadic41.gp` | signs `+1,-1,+1`, product `-1` |
| `gp -q < scripts/direct-dyadic/nfhilbert_validation.gp` | all seven `Q_2` convention checks passed |
| `gp -q < scripts/hilbert/audit_bridge.gp` | all six non-reference points and 28 support-character checks passed |
| `python3 scripts/formal/audit_statements.py` | 2,078,952 assertions; 0 failures; `STATEMENT_AUDIT_OK` |
| `python3 scripts/elementary-routes/verify_route_scope.py` | `ROUTE_SCOPE_OK` |
| `python3 scripts/elementary-routes/route_scope_checks.py` | `ROUTE_SCOPE_CHECKS_OK` |
| `python3 scripts/elementary-routes/jacobi_extended.py` | `JACOBI_EXTENDED_OK` |
| `python3 scripts/cor15/cor15_audit.py selftest` | brute-force agreement; 2,000 random tests, 0 mismatches |
| `python3 scripts/cor15/cor15_audit.py all` | corrected full output preserved in `cor15_audit_output.txt` |
| `python3 scripts/cor15/cor15_audit.py E` | 748,369 survivors; 0 candidates |
| `python3 scripts/cor15/crosscheck_sympy.py` | `CROSSCHECK_OK` |
| `LEAN_PATH=... lean -R ... PaperStatementBridge.lean` | exit 0; principal bridge theorems use only `propext`, `Classical.choice`, `Quot.sound` |
| Root `SHA256SUMS`, excluding three known stale baseline entries | Every listed source passed, including the two hashes changed by this PR |
| `python3 .../verification/test_run_core.py` | 6 focused tests passed |
| `python3 .../verification/test_release.py` | 6 focused tests passed |
| `sha256sum -c SHA256SUMS` inside this review package | All 107 inventory rows passed |

`PKG` in these commands abbreviates `papers/shifted-square-17-41/verification/independent-review-2026-11-08`.

## Known baseline checksum limitation

An unfiltered `sha256sum -c SHA256SUMS` still reports the three metadata mismatches already documented by the public reproduction recipe:

- `README.md`;
- `papers/shifted-square-17-41/manuscript/revision/README.md`;
- `papers/shifted-square-17-41/theorem-formal-crosswalk.md`.

Those unrelated historical document hashes were deliberately not changed in this audit PR. The reproduction recipe's declared metadata reconciliation is the evidence for that older replay, not an accidental claim that the public baseline was hash-clean. My changed `outer41_verify.gp`, `verification/imports.json`, and the resulting `imports.json` entry in the root checksum file all passed the filtered check.

The filtered output is preserved as `checksums-filtered.txt`. No full Lean rebuild was rerun during final packaging; the exact successful build and bridge outputs were previously checked and are retained in `run_log.txt` and `axiom_footprint.txt`.
