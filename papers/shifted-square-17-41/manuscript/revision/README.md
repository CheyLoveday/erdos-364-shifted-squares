# Paper I — article version 1.0.1, 30 September 2026

Read the [PDF](https://github.com/CheyLoveday/erdos-364-shifted-squares/releases/download/v1.0.1/paper1.pdf),
[GitHub reading view](paper_1_github.md),
[standalone MathML HTML](https://github.com/CheyLoveday/erdos-364-shifted-squares/releases/download/v1.0.1/paper1.html), and
[Pandoc source](paper_1.md). The PDF is the primary fixed reading
version; the GitHub view is for on-site reading. Download the standalone HTML
and open it locally. The Pandoc file is publication source, not a GitHub reading
edition. The numbered References section is the bibliography. Download the [complete article sources](https://github.com/CheyLoveday/erdos-364-shifted-squares/releases/download/v1.0.1/paper1-source.zip) and
[checksums](SHA256SUMS). This is an editorial correction of the article;
the selected mathematical results are unchanged.

The formal and arithmetic support remains the separately identified
[v1.0.0 evidence release](https://github.com/CheyLoveday/erdos-364-shifted-squares/releases/tag/v1.0.0),
which is reference [8]. No v1.0.0 manuscript view, Lean source, checker, arithmetic
input, dependency pin, notice or release asset is replaced.

## Corrections and proof correspondence

Source: companion main `5094ae2a06268cfc3f2eb972956b276cdbebf566`, specifically
`manuscript/candidate/paper_1_release_candidate.md`. Reference [8] still identifies
v1.0.0, not this candidate. The [frozen proof record](https://github.com/CheyLoveday/erdos-364-shifted-squares/blob/v1.0.0/papers/shifted-square-17-41/PROOF_RECORD.md) and its
historical executions retain their exact original meaning.

| Location | Change and proof boundary |
| --- | --- |
| Related work and §6.3 | Related work and §6.3 credit Walker [14], equation (3), Theorems 2.2(2)–(3), 2.5 and Lemma 2.4. For odd squarefree K, property Q is K dividing the second coefficient. His product of missing primes is K/gcd(K,v), including the empty product. Negative-Pell solutions use odd powers; norm-one exponents are relative to ε². |
| §2.3 | §2.3 gives Sanna [15, Theorem 1.5, p. 119] with a=2A, b=1. Since w₂=2A and 2 divides the discriminant, the even clause gives v₂(wᵣ)=v₂(r)+v₂(A). The norm and doubling identities give Theorem 1.3 in both parities. A≥2 ensures nondegeneracy. The original proof and Lean endpoint remain unchanged. |
| §5.2 | §5.2 credits classical Dickson composition [16]. Dₘ(Dₙ(T,a),aⁿ)=Dₘₙ(T,a), with a=−1 and n odd, retains parameter −1. Equation (2.2) supplies the factors of two. The lemma's proof, domain and parity guard remain unchanged. |
| Reference [12] | Reference [12] now cites She, Integers 25 (2025), A103. The stated literature comparison is unchanged. |
| Corollary 1.5 and §6.2 | Corollary 1.5 makes X≡2 (mod 8) a consequence; §6.2 proves it. Odd X gives v₂(X²+1)=1, impossible for powerfulness. Even X and X−1=y² make y odd, giving the residue. This is equivalent to the old hypotheses. |
| Corollary 1.5 and §6.3 | The corollary includes 17∣R; §6.3 states its implication. R∣N and gcd(N,17·41)=1 already exclude either prime dividing R or E. Equation (6.8) is explicitly illustrative and unchanged. |

Walker, Sanna and She's primary PDFs were read at the cited locators. Dickson
normalization was checked algebraically using the retained conjugate-power proof.
The monograph is a standard reference without an invented theorem/page locator;
its full text was unavailable in this pass. Mullen's [author lecture, slides 5–6](https://www.fields.utoronto.ca/programs/scientific/10-11/finitefields/GaryMullenPermutation.pdf)
supplies the defining recurrence and functional equation. No literature-wide
originality determination is asserted.

## Verification and limits

The revision preserves all 696 original mathematical AST entries and all twelve
numbered result identifiers. It has 741 mathematical expressions after the
explanatory additions. Only Corollary 1.5's equivalent premise wording and
explicit consequence list alter a numbered result block. Sections 3, 4, 7 and 8,
Appendices A–C, Acknowledgements and the embedded verifier are unchanged.

The reading checks cover all sixteen references, every MathML region, source and
rendered equation inventories, and every page of the 24-page PDF. The source ZIP
was freshly extracted outside the checkout, its checksums verified, its TeX
compiled and its unchanged standalone verifier run. PDF reproduction is checked
by extracted text; PDF bytes may differ between runs or engines. The precise
candidate, limited agent-review disposition and downloadable hashes are in the
[v1.0.1 release notes](https://github.com/CheyLoveday/erdos-364-shifted-squares/releases/tag/v1.0.1).

These checks and the limited independent agent review are not external human peer
review. The human Hilbert-reciprocity, maximality and Pell arguments remain human
proofs. Existing Lean covers the integer-Jacobi and recurrence exclusions and
propagation; it was not rebuilt for this editorial release. Historical audit/build
receipts are not relabelled as fresh runs. No new mathematical exclusion, DOI,
arXiv submission or journal acceptance is asserted. The guide remains v1.0.0.

## Reproduction

In a repository clone, enter `papers/shifted-square-17-41/manuscript/revision/`.
For the source ZIP, extract into a fresh directory and work there. All required
article inputs are included. Licence files are included in the ZIP and at the
repository root. The author, affiliation, AI-use statement and existing CC BY 4.0 /
Apache-2.0 rights decisions are retained.

Tested tools: Pandoc 3.9.0.2, Tectonic 0.16.9, Poppler `pdftotext`, Python 3.13,
SymPy 1.14.0 and mpmath 1.3.0. The TeX preamble uses the established release
packages. Tectonic's cached-only command requires an already populated public
TeX cache and does not download missing dependencies. Cached `lineno.sty` emits
an encoding warning; `inputenc` is ignored by the UTF-8 engine. No replacement
character or missing-glyph diagnostic occurs in the reading PDF.

Compile the included TeX:

```sh
tectonic --untrusted --only-cached --reruns 2 --keep-logs main.tex
pdftotext -layout main.pdf main.txt
```

Regenerate the derived TeX and HTML from the authoritative Markdown:

```sh
pandoc -f markdown+fenced_divs+tex_math_dollars --standalone -t latex \
  --template=reading-template.tex --lua-filter=reading.lua \
  --syntax-highlighting=none --shift-heading-level-by=-1 --fail-if-warnings \
  paper_1.md -o main.tex
pandoc -f markdown+fenced_divs+tex_math_dollars --standalone --mathml \
  --embed-resources --css=reading.css --syntax-highlighting=none --fail-if-warnings \
  paper_1.md -o paper1.html
```

The small LaTeX filter turns manually numbered reference blocks into ordinary
labelled paragraphs. It does not alter mathematical expressions. HTML uses native
MathML with embedded CSS, no scripts, remote fonts or rendering fallback.

Run the unchanged finite verifier with the versions in `anc/requirements.txt`
installed in the selected Python environment:

```sh
python3 -B anc/verify_fixed_fields.py
```

Expected final marker: `FIXED_FIELDS_OK`. This checks the retained finite 17/41
inputs; it is not a bounded substitute for the unbounded human argument. The
repository's original `make paper1-*` operations reproduce the preserved v1.0.0
payload rather than this correction bundle.

## GitHub reading views

One publication source produces independent reading artifacts:

| File | Role | Edited directly? |
| --- | --- | --- |
| [paper_1.md](paper_1.md) | Authoritative Pandoc publication source. | Yes, for authorised manuscript edits. |
| [paper_1_github.md](paper_1_github.md) | Generated on-site GitHub reading copy. | No. |
| [paper1.html](paper1.html) | Standalone MathML reading view; download and open locally. | No. |
| [main.tex](main.tex) | Generated publication intermediate. | No. |
| [paper1.pdf](paper1.pdf) | Fixed publication reading view. | No. |
| [paper1-source.zip](paper1-source.zip) | Preserved release source archive. | No. |

The PDF/HTML/TeX derive from the Pandoc manuscript, not from the GitHub copy.
The GitHub repair does not rebuild or replace released artifacts. Future
manuscript changes require regeneration of the affected reading artifacts;
never correct a generated copy independently.

The [direct generator](../../github_reading.py) also produces the nine
[technical reading copies](../../reading/) linked from the README and proof map.
Their original records are pinned by the frozen evidence inventory, so each
copy links back to its original source and records that source's SHA-256.
Only presentation syntax and reader links change. The proof-record projection
continues to cite the **v1.0.0** portable article; it is not silently rebound
to the current v1.0.1 manuscript.

The generator has a fixed list of ten source/output pairs. It converts Pandoc
heading/division IDs to anchors, equation tags to visible textual numbers, and
backslash math delimiters to GitHub syntax. Inline maths use backtick-dollar
delimiters to protect escaped braces and underscores. Display maths use fenced `math`
blocks at top level. Inside lists, separate paragraphs use protected display-style
expressions, because GitHub leaves indented math fences as literal code. Both
forms preserve the same mathematical content and equation labels.
Unsupported presentation syntax fails. Fenced verifier code is retained exactly.

From the repository root:

```sh
python3 papers/shifted-square-17-41/github_reading.py generate
python3 papers/shifted-square-17-41/github_reading.py check
python3 -B -m unittest discover -s papers/shifted-square-17-41 -p test_github_reading.py
```

`check` requires byte-for-byte agreement with fresh generation, rejects
Pandoc-only presentation constructs in the explicit reader surface, compares
ordered mathematical content, prose, headings and embedded code to each source,
and checks local reading links and section anchors. Equation-label syntax and
reader-link labels/targets are the intended presentation adaptations. The ten
generated views and six ordinary reader documents form its explicit allowlist;
it is not a recursive converter or a publication/release gate.

The repository's Markdown files were inspected for reader roles. The explanation
Markdown remains Pandoc source, with illustrated HTML as its intended reading
artifact. Existing v1.0.0 manuscript views, the old portable copy, release and
execution records, metadata history, checksum files, source archives and notices
remain preserved. Historical/source links are labelled accordingly; the current
reading routes use the generated views. Licences and notices already use
compatible ordinary Markdown and are checked without rewriting them.
