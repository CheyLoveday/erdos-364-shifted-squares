# Paper I — article version 1.0.1, 30 September 2026

Read the [PDF](https://github.com/CheyLoveday/erdos-364-shifted-squares/releases/download/v1.0.1/paper1.pdf), [standalone MathML HTML](https://github.com/CheyLoveday/erdos-364-shifted-squares/releases/download/v1.0.1/paper1.html), and
[editable manuscript](paper_1.md). Its numbered References section is the
bibliography. Download the [complete article sources](https://github.com/CheyLoveday/erdos-364-shifted-squares/releases/download/v1.0.1/paper1-source.zip) and
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
