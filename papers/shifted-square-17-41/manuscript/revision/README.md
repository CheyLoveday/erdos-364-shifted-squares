# Paper I: unreleased attribution revision, 30 September 2026

[Editable manuscript](paper_1.md). Its bibliography is the numbered References
section in that file. The v1.0.0 manuscript, portable view, PDF, HTML and source
archive remain under their existing names. This candidate has not been published
or independently approved.

## Bounded editing brief

Consumer: Chey's preparation and reading of the next Paper I revision.
Objective: resolve the integrated report's attribution/presentation findings F3–F8.
Deliverables: the manuscript with its bibliography; this correspondence/check
account; derived PDF and standalone native-MathML HTML reading copies.
Writable source scope: `manuscript/revision/paper_1.md`, this file, and the root
README's candidate pointer. Reading outputs remain outside tracked source.
Prohibited: changes to v1.0.0 sources/archives, Lean, arithmetic inputs/checkers,
dependency pins, licences, new research, branches, issues, PRs, tags, publication,
submission or canonical promotion.
Checks: primary-source/convention checks; original-math/result AST comparison;
unchanged-section/code comparison; citations, control characters and MathML;
cached PDF compilation and affected-page inspection; whitespace and changed files.
Stop when these pass. Report missing support or a changed mathematical claim
against the affected item.

## Source and correspondence

Source: companion main `5094ae2a06268cfc3f2eb972956b276cdbebf566`, specifically
`manuscript/candidate/paper_1_release_candidate.md`. Reference [8] still identifies
v1.0.0, not this candidate. The [frozen proof record](../../PROOF_RECORD.md) and its
historical executions retain their exact original meaning.

| Finding | Change and proof boundary |
| --- | --- |
| F3 | Related work and §6.3 credit Walker [14], equation (3), Theorems 2.2(2)–(3), 2.5 and Lemma 2.4. For odd squarefree K, property Q is K dividing the second coefficient. His product of missing primes is K/gcd(K,v), including the empty product. Negative-Pell solutions use odd powers; norm-one exponents are relative to ε². |
| F4 | §2.3 gives Sanna [15, Theorem 1.5, p. 119] with a=2A, b=1. Since w₂=2A and 2 divides the discriminant, the even clause gives v₂(wᵣ)=v₂(r)+v₂(A). The norm and doubling identities give Theorem 1.3 in both parities. A≥2 ensures nondegeneracy. The original proof and Lean endpoint remain unchanged. |
| F5 | §5.2 credits classical Dickson composition [16]. Dₘ(Dₙ(T,a),aⁿ)=Dₘₙ(T,a), with a=−1 and n odd, retains parameter −1. Equation (2.2) supplies the factors of two. The lemma's proof, domain and parity guard remain unchanged. |
| F6 | Reference [12] now cites She, Integers 25 (2025), A103. The stated literature comparison is unchanged. |
| F7 | Corollary 1.5 makes X≡2 (mod 8) a consequence; §6.2 proves it. Odd X gives v₂(X²+1)=1, impossible for powerfulness. Even X and X−1=y² make y odd, giving the residue. This is equivalent to the old hypotheses. |
| F8 | The corollary includes 17∣R; §6.3 states its implication. R∣N and gcd(N,17·41)=1 already exclude either prime dividing R or E. Equation (6.8) is explicitly illustrative and unchanged. |

Walker, Sanna and She's primary PDFs were read at the cited locators. Dickson
normalization was checked algebraically using the retained conjugate-power proof.
The monograph is a standard reference without an invented theorem/page locator;
its full text was unavailable in this pass. Mullen's [author lecture, slides 5–6](https://www.fields.utoronto.ca/programs/scientific/10-11/finitefields/GaryMullenPermutation.pdf)
supplies the defining recurrence and functional equation. No literature-wide
originality determination is asserted.

## Actual focused checks

- Pandoc 3.9.0.2 parsed without warnings. All 696 original Math AST entries remain;
  the revision has 741 including explanatory adapters. All 12 numbered result IDs
  remain; only Corollary 1.5's equivalent wording and consequence list change.
- Sections 3, 4, 7 and 8, Appendices A–C and Acknowledgements are byte-identical.
  Every parsed verifier code block is identical. All existing tracked mathematics,
  proof/arithmetic evidence, pins, notices and frozen delivery files are untouched.
- All 16 manually numbered references have unique anchors and resolve. No hidden
  control characters occur. HTML has 741 native-MathML regions, zero `merror`
  nodes or scripts, and no duplicate IDs or broken internal links. Its TeX
  annotations are source annotations within MathML, not display fallback.
- Tectonic 0.16.9 compiled a 24-page PDF using cached dependencies. The final log
  has no undefined references, missing-glyph or overfull/underfull-box diagnostics.
  Pages 3, 4, 6, 13, 14, 15, 16 and 24 were visually inspected. Cached `lineno.sty`
  emits an encoding warning; `inputenc` is ignored by the UTF-8 engine. No
  replacement character occurs in the extracted PDF.
- The adapters and corollary clarifications were re-derived against the text.
  This is implementation verification, not independent approval.

No arithmetic replay, Lean build/audit, five-operation release pipeline, archive
regeneration or submission check was run for this editorial candidate. Historical
v1.0.0 execution receipts have not been relabelled as fresh candidate checks.

## Reproduce reading copies

Run from the companion root, using a fresh ignored output directory. The template
reuses the released preamble. The filter makes manually numbered reference blocks
ordinary labelled paragraphs for LaTeX; the Markdown mathematics is untouched.

```sh
OUT=.paper1-build/attribution-20260930
mkdir -p "$OUT"
export PAPER1_READING_OUT="$OUT"
python3 - <<'PY'
import os
from pathlib import Path
from zipfile import ZipFile
out = Path(os.environ['PAPER1_READING_OUT'])
with ZipFile('papers/shifted-square-17-41/manuscript/candidate/paper_1_release_candidate_source.zip') as z:
    preamble = z.read('main.tex').decode().split(r'\title{', 1)[0]
preamble = preamble.replace('breakanywhere=false', 'breakanywhere=true')
(out/'reading-template.tex').write_text(preamble + r'''\newcounter{none}
\title{$title$}
\author{$for(author)$$author$$sep$\and $endfor$\\[3pt]{\normalsize $affiliation$}}
\date{$date$}
\begin{document}
\maketitle
$body$
\end{document}
''')
(out/'reading.lua').write_text('''function Div(el)
  if FORMAT == "latex" then
    el.identifier = el.identifier:gsub("^ref%-", "reference-")
    for i = #el.classes, 1, -1 do
      if el.classes[i] == "reference" then table.remove(el.classes, i) end
    end
  end
  return el
end
''')
(out/'reading.css').write_text('body {max-width: 76ch; margin: 2rem auto; padding: 0 1rem; line-height: 1.5; font-family: Georgia, serif;} .math.display {display:block; overflow-x:auto; padding: .6rem 0;} table {display:block; overflow-x:auto; border-collapse:collapse; font-size: .9em;} th,td {padding:.3rem .5rem; border-bottom:1px solid #ccc;} pre {overflow-x:auto; padding:.8rem; background:#f4f4f4;} .theorem {border-left:3px solid #ccc; padding-left:1rem;}')
PY
SOURCE=papers/shifted-square-17-41/manuscript/revision/paper_1.md
pandoc -f markdown+fenced_divs+tex_math_dollars --standalone --mathml \
  --embed-resources --css="$OUT/reading.css" --fail-if-warnings \
  "$SOURCE" -o "$OUT/paper1.html"
pandoc -f markdown+fenced_divs+tex_math_dollars --standalone -t latex \
  --template="$OUT/reading-template.tex" --lua-filter="$OUT/reading.lua" \
  --syntax-highlighting=none --shift-heading-level-by=-1 --fail-if-warnings \
  "$SOURCE" -o "$OUT/paper1.tex"
(cd "$OUT" && tectonic --untrusted --only-cached --reruns 2 --keep-logs paper1.tex)
pdftotext -layout "$OUT/paper1.pdf" "$OUT/paper1.txt"
```

The existing release checker deliberately binds v1.0.0 and was not modified to
accept this candidate or given a false PASS. Before a new public release, the owner
must review this revision and qualify its updated publication/evidence packaging.
No new version number or release date is chosen. Notices and rights are unchanged.
