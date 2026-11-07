#!/usr/bin/env bash
# Reproduce selected checks for the public shifted-square release.
set -u -o pipefail
if [ "$#" -ne 1 ]; then
  printf 'usage: %s NEW_OUTPUT_DIRECTORY\n' "$0" >&2
  exit 2
fi
OUT=$1
if [ -e "$OUT" ]; then
  printf 'refusing to reuse existing directory: %s\n' "$OUT" >&2
  exit 2
fi
mkdir -p "$OUT/work" "$OUT/logs"
OUT=$(cd "$OUT" && pwd)
WORK=$OUT/work
SRC=$WORK/source
LOG=$OUT/logs
PACKAGE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)

COMMIT=c663b4e1e65c99846d41270a288f154559cc9fd6
ARCHIVE_SHA=f9ea4c1cf80f3223e9e0a7b27bffac27b92ab4b75b2827ed472cb1a50d8d9e74
LEAN_SHA=07a633cc8d9151cbc08825ea4cdda50d4b02a2c9cb852c0131b13046f49cad7f
fetch() {
  curl -L --fail --silent --show-error "$1" -o "$2"
  printf '%s  %s\n' "$3" "$2" | sha256sum -c -
}
fetch "https://codeload.github.com/CheyLoveday/erdos-364-shifted-squares/tar.gz/$COMMIT" "$WORK/public.tar.gz" "$ARCHIVE_SHA" >"$LOG/fetch-source.log" 2>&1 || exit 1
mkdir "$SRC"
tar -xzf "$WORK/public.tar.gz" -C "$SRC" --strip-components=1

# Declared metadata reconciliation only. The bytes of every document, Lean
# declaration and verifier remain those fetched from the pinned public commit.
# The two original metadata files and their pre-patch failures are preserved
# under INPUTS.md and logs/ in this package.
cp "$PACKAGE/metadata-hashes.patch" "$LOG/metadata-hashes.patch"
cp "$PACKAGE/SHA256SUMS.upstream" "$LOG/SHA256SUMS.upstream"
cp "$PACKAGE/imports.upstream.json" "$LOG/imports.upstream.json"
patch -d "$SRC" -p1 <"$LOG/metadata-hashes.patch" >"$LOG/metadata-patch.log" 2>&1 || exit 1

fetch "https://github.com/leanprover/lean4/releases/download/v4.31.0/lean-4.31.0-linux.tar.zst" "$WORK/lean.tar.zst" "$LEAN_SHA" >"$LOG/fetch-lean.log" 2>&1 || exit 1
mkdir "$WORK/lean"
zstd -d "$WORK/lean.tar.zst" -c | tar -x -C "$WORK/lean" --strip-components=1

export PATH="$WORK/lean/bin:/opt/math/bin:/usr/local/bin:/usr/bin:/bin"
export TMPDIR="$WORK"
unset LEAN_PATH
{
  printf 'commit: %s\n' "$COMMIT"
  printf 'source archive sha256: %s\n' "$ARCHIVE_SHA"
  printf 'Lean archive sha256: %s\n' "$LEAN_SHA"
  lean --version
  lake --version
  gp --version
  printf 'cache policy: public Lake dependency cache; no private build cache\n'
} >"$LOG/environment.log" 2>&1

python3 -m venv "$WORK/venv" >"$LOG/venv.log" 2>&1 || exit 1
"$WORK/venv/bin/pip" install --require-hashes -r "$SRC/papers/shifted-square-17-41/verification/requirements.lock" >>"$LOG/venv.log" 2>&1 || exit 1

fail=0
run() {
  name=$1
  shift
  if (cd "$SRC" && "$@") >"$LOG/$name.log" 2>&1; then
    printf 'PASS %s\n' "$name" | tee -a "$OUT/status.tsv"
  else
    rc=$?
    printf 'FAIL(%s) %s\n' "$rc" "$name" | tee -a "$OUT/status.tsv"
    fail=1
  fi
}
run source-manifest sha256sum -c SHA256SUMS
run lake-dependencies lake update
run mathlib-cache lake exe cache get
run lean-build lake --no-cache build Erdos364.DicksonLucas.ShiftedSquarePropagation
run axiom-audit lake --no-cache env lean papers/shifted-square-17-41/verification/PaperTheoremAxiomAudit.lean
run gp17 gp -q -f experiments/sm2_outer_seventeen/outer17_verify.gp
run gp41 gp -q -f experiments/sm2_four_translate/interpolation/outer41_verify.gp
run gp-fixed gp -q -f papers/shifted-square-17-41/verification/replay/independent_fixed_fields.gp
run py-fixed "$WORK/venv/bin/python" -B papers/shifted-square-17-41/manuscript/revision/anc/verify_fixed_fields.py
run py-independent "$WORK/venv/bin/python" -B papers/shifted-square-17-41/verification/replay/independent_finite.py
run py-propagation "$WORK/venv/bin/python" -B experiments/shifted_square_propagation/replay.py
run py-block "$WORK/venv/bin/python" -B experiments/sm2_four_translate/interpolation/outer41_jacobi_block.py --self-test
run py-certificate "$WORK/venv/bin/python" -B experiments/sm2_four_translate/interpolation/outer41_jacobi_certificate.py --self-test
run py-telescope "$WORK/venv/bin/python" -B experiments/sm2_four_translate/interpolation/outer41_jacobi_telescope.py --self-test
run core-runner "$WORK/venv/bin/python" papers/shifted-square-17-41/verification/run_core.py --output "$WORK/core-results"

cat "$OUT/status.tsv"
exit "$fail"
