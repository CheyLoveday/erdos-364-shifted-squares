# Bounded metadata update for version 1.0.0

Date: 11 September 2026. Author decision recorded: Chey G. A. Loveday,
Overdog.ai Ltd, Colchester, England; CC BY 4.0 for the article, guide,
figures and data; Apache-2.0 for code; the AI-use statement below; release
tag `v1.0.0` in `CheyLoveday/erdos-364-shifted-squares`.

This is the bibliographical and metadata update anticipated by the release
instructions. It changes file identities, not the mathematical freeze. The
supplied frozen manuscript remains byte-identical under
`manuscript/delivery/paper_1_final_frozen.md` (SHA-256
`1570a324a4aa51c44b5981fc6578b335547345076d94e6f12d52332a68b0f694`) and the
handoff `baseline/` and `audit/` records are untouched.

## Exact edits

Applied identically to the article Markdown, the TeX source in the source
ZIP, the portable Markdown and, where the item exists there, the HTML
template and the explanatory guide:

1. Author line `Chey Loveday` → `Chey G. A. Loveday`, with the affiliation
   `Overdog.ai Ltd, Colchester, England` added beneath it (YAML `affiliation`
   key; `\author` and `pdfauthor` in TeX; author and affiliation lines and the
   `<meta name="author">` in the HTML template).
2. A new unnumbered section **Acknowledgements** immediately before
   **References**, containing only the approved statement: “AI assistants
   (Anthropic Claude and OpenAI ChatGPT/Codex) were used for drafting and
   editing prose, challenging arguments, writing and running verifiers, and
   repository engineering. All mathematical statements, proofs and publication
   decisions were reviewed by the author, who takes sole responsibility for
   them.” The HTML template's static contents list gained the matching entry.
3. Reference [8] now cites the public release: “C. G. A. Loveday. *Fixed-field
   certificates and integer-Jacobi formal proofs for the 17/41 shifted-square
   obstruction*. Software, data and Lean development, version 1.0.0
   (11 September 2026). Public release:
   <https://github.com/CheyLoveday/erdos-364-shifted-squares/releases/tag/v1.0.0>.
   Section 7 and Appendix B specify the mathematical statements and their
   formal correspondence.” The former “unpublished … no public archival
   identifier” wording is removed.
4. One sentence in Appendix C: “reproducible independently of the unpublished
   Lean archive” → “reproducible independently of the separately released Lean
   archive [8]”.
5. Source-ZIP `README.md`: author/affiliation, the article licence line, and
   the reference [8] paragraph; ZIP entry timestamps set to 2026-09-11 12:00;
   its internal `SHA256SUMS` regenerated.
6. Explanatory guide (Markdown and the byte-identical embedded Markdown in its
   HTML): the “Mathematical basis” citation names the author as above and the
   version as 1.0.0 of 11 September 2026 (content frozen 10 September 2026);
   the “Workflow basis” note now points to the article's Acknowledgements for
   the author's AI-use statement. Its 462 mathematical blocks and five figures
   are unchanged.

No theorem statement, proof, hypothesis, numbering, coefficient, table,
equation or verifier line was changed. `make paper1-check` passed after the
edits: the ordered Pandoc mathematical AST digest in `audit/math-freeze.json`
is unchanged, with 696 expressions and 12 numbered result blocks in both the
Markdown and the rebuilt HTML.

## Second pass after independent review

An independent read-only agent review of the first pass found the following
defects, corrected before any gate result was recorded:

- The Tectonic/T1 build printed the section sign in reference [5] as “ğ”.
  The two `§` characters in the TeX source are now `\S`; the Markdown keeps
  `§`. The TeX source is otherwise unchanged.
- Reference [8] showed only the link text “Public release” in print. All
  views now print the URL.
- `PROOF_RECORD.md` stated the frozen manuscript hash as the hash of the
  linked release view; it now distinguishes the two and points here.
- `source-theorem.md` and `theorem-formal-crosswalk.md` linked Lean sources
  by permalink into the private integration repository. They now link the
  same files shipped in this release (`Erdos364/`). Seven of the eight files
  are byte-identical to the permalinked revision; the propagation file
  gained one line at its top (and later material after line 258), so its
  three line anchors are shifted by one.
- The historical 10 September manuscript-check records carried a local
  virtual-environment path and a home-directory path; both are normalised
  to `<PYTHON_ENV>` and `<HOME>`. No result value changed.
- `CITATION.cff` now names the release as reference [8] does and gives the
  article as the preferred citation.
- The HTML was rendered with the supplied recipe under Pandoc 3.9.0.2,
  whereas the handoff recorded Pandoc 3.1.11.1. The recipe's own parity
  check passed: equation geometry, article text and link targets are
  identical to the supplied rendering, and `paper1-build` reproduces the
  shipped HTML byte-for-byte. The newer Pandoc omits the `odd`, `even` and
  `header` class attributes on the 41 table rows; no rule in the template's
  CSS targets those classes, so the displayed tables are unchanged.

The historical Magma comparison files reference the private tracker issue
in which the Magma responses were received; those files are pinned
historical assets and are left unchanged, so those links are not publicly
resolvable.

## Rebuilt views

The HTML was rebuilt with the supplied `rendering/render_html.py` recipe and
the unchanged equation cache. The PDF was rebuilt from the updated TeX with
Tectonic 0.16.9 (`--untrusted --only-cached`, 22 pages, no LaTeX diagnostics);
Tectonic replaces the pdfLaTeX build of the supplied candidate PDF, as the
10 September records already noted for the build check. PDF bytes are not
asserted to be reproducible across TeX engines.

## Identities

| File (under `papers/shifted-square-17-41/`) | Before | After |
| --- | --- | --- |
| `manuscript/candidate/paper_1_release_candidate.md` | `1570a324a4aa51c44b5981fc6578b335547345076d94e6f12d52332a68b0f694` | `d27fffb9a760272d44f45d67919d41bd9596fc77e6fdca95ac86ee8266873dd2` |
| `manuscript/candidate/paper_1_release_candidate_source.zip` | `1e0279f23e0e4457f97fe69c322017e05a9478d611b2dbe4f9707c09b3b2053b` | `04bd88064b99569332afdc8e3e6678d38bf1e99146c34d2509197922140c8491` |
| `manuscript/candidate/paper_1_release_candidate.html` | `6e198d258fb69a789d8b9fba7bf7d87365f560750bc5528372e5f141a87adb51` | `05bac0be394138fe7bb29c088eb53ed4381bbb1a85a1f604bd57985b22ea82c5` |
| `manuscript/candidate/paper_1_release_candidate.pdf` | `b79b38feed42fbe2729b39e01cb8990c7b40edb39d668a400fcb71b6d156d931` | `39352be32b135fc7c79aa648ae989618bc84b787ee1919aadcf8dd3dc307d37e` |
| `manuscript/candidate/rendering/template.html` | `a058e987af385baafe983bf0ac14c1b457f5bc9f25f195fd4c7aac90c2cfc6e0` | `1835ed0ecdc41d58c5ad99686428a38d1b35a9d6d95882e5e7501331f5922d17` |
| `manuscript/paper_1_final_frozen_portable.md` | `253a948acf6e9a6aece4b63cfef0680f2317467b7a1b8584a6c942007ff7f8ab` | `043ec6a71b38bc64126ad404005c4caa8e7ef08c833627a2eaa05e2b9c84b8a4` |
| `manuscript/explanation/paper_1_explained.md` | `54cc17408f0356d0093960102ea26212715ebba716b22e62d31b95a9a64cf46c` | `ba9b92ac8cf2c735a3440aa43b9ebdf6106d32c916fe942c874f63b7c46874b2` |
| `manuscript/explanation/paper_1_explained_illustrated.html` | `3cf832a7b67b4953df92870771481a4c24771eaa8be66686e029e22c00ebdc5d` | `5abe1166e5f9dd26d01eb74acf3799d0faedc5236f061f494b53b23058277196` |

The pinned identities in `verification/release.py`,
`verification/manuscript-inputs.json` and `manuscript/SHA256SUMS` were moved
to the “after” column. The “before” column holds the values immediately
before this update: for the five `candidate/` files these are the handoff
values; for the portable Markdown and the two guide files they are the
values of the 10–11 September presentation and link corrections, which
postdate the handoff. The unchanged `rendering/README.md`,
`math-cache.json`, `render_html.py` and `requirements.txt` keep their
handoff identities.

## Boundaries

This record documents a metadata change. It does not assert peer review, a
DOI, an arXiv identifier, canonical acceptance, or any new mathematical
result. The release-gate results for the final commit are recorded outside
the evidence archive, so that the archive does not contain its own hash.
