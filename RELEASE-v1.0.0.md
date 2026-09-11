# Release record — version 1.0.0, 11 September 2026

Chey G. A. Loveday (Overdog.ai Ltd, Colchester, England),
**Shifted-square obstructions at indices divisible by 17 or 41 in a family of
Lucas sequences**. Public repository `CheyLoveday/erdos-364-shifted-squares`,
tag `v1.0.0`:
<https://github.com/CheyLoveday/erdos-364-shifted-squares/releases/tag/v1.0.0>.

This file is an external execution record. It is not a member of the evidence
archive it identifies, so the archive does not contain its own hash. In the
public repository the commit carrying this file is the one the tag `v1.0.0`
points to.

## Source identity

| Item | Value |
| --- | --- |
| LAB source commit (private integration record) | `f7e55b1ec65f1223d4520d4ed2eecbd17c4f5367` |
| LAB source tree | `7423a9668e3538fc9c1de2d7141ea930c6782868` |
| Exported source inventory SHA-256 (`source_sha256` in every gate record) | `62affe13a91b0c88b4f45b715599a6e6ef86f0a01f611530298111706459a223` |
| Evidence archive members | 188 files: 181 allowlisted sources plus `README.md`, `LICENSE.md`, `CITATION.cff`, `LICENSES/Apache-2.0.txt`, `LICENSES/CC-BY-4.0.txt`, `Makefile`, `Erdos364.lean`, and the archive's `SHA256SUMS` |

## Package identities

| Package | SHA-256 |
| --- | --- |
| `paper1-arxiv-source.zip` | `04bd88064b99569332afdc8e3e6678d38bf1e99146c34d2509197922140c8491` |
| `paper1-evidence-source.tar.gz` | `b5fd90819a14ae38c3842d3e13bef5b584ed76c67e001c12a95b6c5a12d80a3f` |

Both values were produced by `paper1-stage` and reproduced byte-for-byte by
the independent staging inside `paper1-check-export`. The arXiv source ZIP is
byte-identical to `manuscript/candidate/paper_1_release_candidate_source.zip`.

## Manuscript identities (release views)

| File (under `papers/shifted-square-17-41/`) | SHA-256 |
| --- | --- |
| `manuscript/candidate/paper_1_release_candidate.md` | `d27fffb9a760272d44f45d67919d41bd9596fc77e6fdca95ac86ee8266873dd2` |
| `manuscript/candidate/paper_1_release_candidate_source.zip` | `04bd88064b99569332afdc8e3e6678d38bf1e99146c34d2509197922140c8491` |
| `manuscript/candidate/paper_1_release_candidate.html` | `05bac0be394138fe7bb29c088eb53ed4381bbb1a85a1f604bd57985b22ea82c5` |
| `manuscript/candidate/paper_1_release_candidate.pdf` | `39352be32b135fc7c79aa648ae989618bc84b787ee1919aadcf8dd3dc307d37e` |
| `manuscript/paper_1_final_frozen_portable.md` | `043ec6a71b38bc64126ad404005c4caa8e7ef08c833627a2eaa05e2b9c84b8a4` |
| `manuscript/explanation/paper_1_explained.md` | `ba9b92ac8cf2c735a3440aa43b9ebdf6106d32c916fe942c874f63b7c46874b2` |
| `manuscript/explanation/paper_1_explained_illustrated.html` | `5abe1166e5f9dd26d01eb74acf3799d0faedc5236f061f494b53b23058277196` |

These differ from the supplied frozen manuscript (delivery copy SHA-256
`1570a324a4aa51c44b5981fc6578b335547345076d94e6f12d52332a68b0f694`) only by
the bounded metadata update recorded in `manuscript/METADATA_UPDATE.md`:
author line and affiliation, an Acknowledgements section with the author's
AI-use statement, reference [8] citing this release, and one Appendix C
sentence. The ordered mathematical AST digest in `manuscript/audit/math-freeze.json`
is unchanged: 696 expressions and 12 numbered result blocks in the Markdown
and the rebuilt HTML; the printed verifier equals the standalone
`anc/verify_fixed_fields.py`.

## Release gates at the source commit

All five operations were executed against source inventory `62affe13…` on
11 September 2026 (10:55–11:09 UTC). Records are under
`records/2026-09-11-v1.0.0/` (JSON only; built artifacts are not committed;
the local temporary-extraction and virtual-environment paths are normalised
to `<EXTRACTION_ROOT>` and `<PYTHON_ENV>`).

| Gate | Result | Record |
| --- | --- | --- |
| `make paper1-check` | PASS | `records/2026-09-11-v1.0.0/check/result.json` |
| `make paper1-verify` | PASS | `records/2026-09-11-v1.0.0/verify/result.json` |
| `make paper1-build` | PASS | `records/2026-09-11-v1.0.0/build/result.json` |
| `make paper1-stage` | PASS | `records/2026-09-11-v1.0.0/stage/result.json` |
| `make paper1-check-export` | PASS | `records/2026-09-11-v1.0.0/check-export/result.json` |

What passed, concretely:

- `check`: source and manuscript identities, mathematical freeze digest,
  HTML embedded source equal to the Markdown, printed program equal to the
  standalone verifier, pinned Python dependency versions.
- `verify`: the unchanged ancillary verifier (`FIXED_FIELDS_OK`), the 12
  archive/arithmetic failure-control unit tests, the original GP checks for
  17 and 41, the implementation-distinct GP and Python replays, the
  propagation replay, the Lean build of
  `Erdos364.DicksonLucas.ShiftedSquarePropagation`, and the axiom audit of
  21 declarations, which admits only `propext`, `Classical.choice` and
  `Quot.sound`.
- `build`: PDF from the release TeX with Tectonic 0.16.9
  (`--untrusted --only-cached`; 22 pages; no LaTeX diagnostics) and the HTML
  from the supplied recipe, byte-identical to the shipped HTML. The PDF built
  in this gate (`943dd4c23b918cd5fe38d779c210a688a451201711b13a0a25ad25197df23e56`)
  has the same extracted text (`pdftotext`) as the shipped PDF; PDF bytes are
  not asserted to be reproducible across runs or engines.
- `stage`: the two packages above from the explicit allowlists.
- `check-export`: fresh extraction of both packages in a temporary directory
  without private Git history or inherited Python/Lean search paths; every
  payload hash checked; article PDF/HTML rebuilt and ancillary verifier run
  from the extracted ZIP; the extracted evidence tree's own `check`, `verify`
  and `build` operations executed; the nine public Lake dependencies copied
  from a separately prepared cache at the pinned revisions; the default
  exported Lean root built from source, rebuilding all 60 local modules.

Environment: Python 3.13.1 with SymPy 1.14.0, mpmath 1.3.0, beautifulsoup4
4.14.3, soupsieve 2.8.4, typing_extensions 4.16.0; PARI/GP 2.17.3; Lean
4.31.0 (Lake 5.0.0); Tectonic 0.16.9; Pandoc; Poppler `pdftotext`; macOS
arm64.

## Publication decisions recorded

- Author: Chey G. A. Loveday; affiliation Overdog.ai Ltd, Colchester, England.
- Licences: CC BY 4.0 for the article, explanatory guide, its five figures
  and the data/certificates; Apache-2.0 for the original code
  (`LICENSE.md`, `LICENSES/`).
- AI-use statement: as printed in the article's Acknowledgements and the
  repository README.
- Reference [8] now cites this release. That is the only bibliographical
  change; it is recorded in `manuscript/METADATA_UPDATE.md`.
- Companion branches `paper1/bootstrap` and
  `paper1/spine-ledger-review-20260909` (a Tranche-0 skeleton and superseded
  planning material) were deleted before publication; their commits remain
  reachable by hash until GitHub garbage-collects them. A read-only scan of
  those branches found no secrets, private paths or personal data.
- The companion's five open planning issues from the superseded bootstrap
  (#1–#5) were closed as not planned before publication.

## Limitations and non-claims

- No DOI, arXiv identifier, journal submission or peer review is asserted.
  The independent reviews of this release were agent reviews, not external
  human mathematical review.
- The human Hilbert-reciprocity, maximality and Pell arguments are not
  Lean-formalised; the Lean development covers the integer-Jacobi and
  recurrence exclusions and their propagation, as the proof record states.
- Three historical Magma input scripts (17-B, 41-A, 41-B) remain unrecovered;
  the archived Magma responses are secondary corroboration, not a complete
  replay, and the article's required verifier and the GP/Lean checks do not
  depend on them. The archived Magma comparison files link to the private
  tracker in which the responses were received; those links are not publicly
  resolvable.
- No 73/97 result, Brauer continuation, complete resolution of Erdős 364,
  canonical promotion or Ledger admission is included.
- A later bibliographical, licensing or metadata change creates new file and
  package identities and must be re-checked and released as a new version;
  `v1.0.0` is not to be mutated.
