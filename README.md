# Shifted-square obstructions at indices divisible by 17 or 41

## What this project proves

This repository contains a mathematical article, an explanatory guide, a Lean 4
formal development and reproducible finite certificates. For nonnegative integers
$A$ with $A\equiv2\pmod4$, define

$$
F_0(A)=1,\qquad F_1(A)=A,\qquad
F_{n+2}(A)=2AF_{n+1}(A)+F_n(A).
$$

The main theorem proves that **$F_N(A)-1$ is not a square whenever $N>0$ is
divisible by $17$ or $41$**. Explicit arithmetic certificates give obstructions
at the two fixed indices; recurrence composition extends them to all positive
odd multiples, while an exact valuation identity excludes every positive even
index. The result restricts one square-middle family related to Erdős Problem
364. **It does not solve Erdős 364.**

## Start here

- **Read the article:** [PDF](papers/shifted-square-17-41/manuscript/revision/paper1.pdf) | [HTML](papers/shifted-square-17-41/manuscript/revision/paper1.html) | [Markdown](papers/shifted-square-17-41/manuscript/revision/paper_1.md).
- **Understand the mathematics:** [illustrated explanation](papers/shifted-square-17-41/manuscript/explanation/paper_1_explained_illustrated.html) ([Markdown prose](papers/shifted-square-17-41/manuscript/explanation/paper_1_explained.md)).
- **See the proof architecture:** [conceptual proof map](papers/shifted-square-17-41/conceptual-proof-map.md), from the two fixed-index routes to composition and the Pell application.
- **Audit the claims:** [proof record](papers/shifted-square-17-41/PROOF_RECORD.md) and [theorem–formal crosswalk](papers/shifted-square-17-41/theorem-formal-crosswalk.md).
- **Reproduce the evidence:** [verification routes and commands](#reproduction).

The current article is **v1.0.1**; its formal and arithmetic support remains
**v1.0.0**. The illustrated guide explains the v1.0.0 article and uses that
version's numbering. Download either HTML file and open it locally to read it.

## Choose your reading path

| I want to… | Reading path |
| --- | --- |
| Read the mathematical result | Start with [article §§1.2–1.3](papers/shifted-square-17-41/manuscript/revision/paper_1.md), then follow the proofs. |
| Understand why the proof works | Read the [illustrated explanation](papers/shifted-square-17-41/manuscript/explanation/paper_1_explained_illustrated.html), then the [conceptual proof map](papers/shifted-square-17-41/conceptual-proof-map.md) and its detailed crosswalk links. |
| Inspect the formal verification | Follow the [theorem–formal crosswalk](papers/shifted-square-17-41/theorem-formal-crosswalk.md), [Lean axiom audit](papers/shifted-square-17-41/verification/PaperTheoremAxiomAudit.lean) and [recorded audit output](papers/shifted-square-17-41/verification/records/2026-09-10-core/axioms.json). |
| Reproduce the finite evidence | Use the [reproduction section](#reproduction), choosing the current article or preserved evidence payload. |
| Trace publication and provenance | Read the [release and correction history](#citation-licence-and-provenance), [v1.0.0 execution record](RELEASE-v1.0.0.md) and [v1.0.1 correction note](papers/shifted-square-17-41/manuscript/revision/README.md). |

## The proof in one paragraph

At $p=17$ and $p=41$, elementary congruences remove $A\equiv6\pmod8$.
The remaining phase $A\equiv2\pmod8$ needs more: the shifted values are
squares in the 2-adic integers, so congruences modulo powers of two alone
cannot exclude them. Explicit units in degree-$17$ and degree-$41$ number
fields provide a Hilbert-reciprocity contradiction under the square hypothesis.
The same detector data give an integer-Jacobi obstruction, formalised in Lean.
For odd $N$ divisible by $p$, recurrence composition transfers the fixed-index
obstruction to $N$ while preserving the required parameter congruence. For
even $N>0$, the identity $v_2(F_N(A)-1)=2v_2(N)+1$ already rules out a square.
See [article §1.3](papers/shifted-square-17-41/manuscript/revision/paper_1.md)
for the construction and [the structured human proof](papers/shifted-square-17-41/hilbert-obstruction-lamport.md)
for its detailed obligations.

## What is proved and what remains open

The recurrence obstruction holds for every parameter and index in the stated
domain; it is not an inference from a bounded search. In the powerful-number
application, [Corollary 1.5](papers/shifted-square-17-41/manuscript/revision/paper_1.md)
restricts the exact negative-Pell exponent for $X\ge2$ with $X-1$ a square
and $X^2+1$ powerful. An actual square-middle triple must also have $X^2-1$
powerful, a further condition not needed for that corollary.

The paper does not exclude all remaining indices or all square-middle
families. No $73/97$ result, Brauer continuation or complete resolution of
Erdős 364 is included. Continuation research is outside this release.

## Human proof, Lean and computation

| Component | What it establishes and where to inspect it |
| --- | --- |
| Human proof | The article proves the Hilbert-reciprocity, maximality and Pell arguments. These arguments are not Lean-formalised; see the [proof record](papers/shifted-square-17-41/PROOF_RECORD.md). |
| Lean 4 | The 60 local modules formalise the integer-Jacobi and recurrence exclusions and their propagation. The [theorem–formal crosswalk](papers/shifted-square-17-41/theorem-formal-crosswalk.md) identifies exact declarations and domains. |
| Finite arithmetic | The exact-arithmetic verifier and PARI/GP and Python replays check the fixed certificate data used by the proofs. See [verification](papers/shifted-square-17-41/verification/export-README.md). |

The Hilbert and Jacobi routes share detector and certificate data; they are
not independently sourced certificates. The [architecture crosswalk](papers/shifted-square-17-41/hilbert-jacobi-crosswalk.md)
explains their relationship. Three historical Magma input scripts (17-B,
41-A, 41-B) remain missing; archived responses do not supply complete Magma
replay. The required finite verifier and GP/Lean route do not depend on them.

## Repository map

| Location | Purpose |
| --- | --- |
| [Current article](papers/shifted-square-17-41/manuscript/revision/) | v1.0.1 PDF, HTML, editable Markdown, sources and correction note. |
| [Explanatory guide](papers/shifted-square-17-41/manuscript/explanation/) | Illustrated HTML and Markdown prose, explaining v1.0.0. |
| [Proof record](papers/shifted-square-17-41/PROOF_RECORD.md) | Claim-to-proof correspondence for the frozen manuscript. |
| [Structured human proof](papers/shifted-square-17-41/hilbert-obstruction-lamport.md) | Detailed Hilbert-reciprocity argument. |
| [Conceptual proof map](papers/shifted-square-17-41/conceptual-proof-map.md) | Proof dependencies, arithmetic routes, composition and the Pell application. |
| [Hilbert–Jacobi crosswalk](papers/shifted-square-17-41/hilbert-jacobi-crosswalk.md) | Exact relationship between the human and formal arithmetic routes. |
| [Theorem–formal crosswalk](papers/shifted-square-17-41/theorem-formal-crosswalk.md) | Article-facing statements, Lean declarations and scope limits. |
| [Verification](papers/shifted-square-17-41/verification/) | Replay tools, dependency pins, axiom audit and historical check records. |
| [Erdos364/](Erdos364/) | Lean 4 source. |
| [experiments/](experiments/) | Finite arithmetic certificates, checkers and replays. |

## Reproduction

Choose the payload you want to reproduce:

- **Current article (v1.0.1):** use the [article reproduction instructions](papers/shifted-square-17-41/manuscript/revision/README.md#reproduction) to build the reading files and run the unchanged finite verifier.
- **Preserved formal and arithmetic evidence (v1.0.0):** use the setup and five operations below. These reproduce the preserved article/evidence payload, not the v1.0.1 reading files. The [verification guide](papers/shifted-square-17-41/verification/export-README.md) documents the original source candidate; its pending-publication wording is historical.

<details>
<summary>v1.0.0 environment setup and five reproduction operations</summary>

The following dependencies and five operations reproduce the preserved v1.0.0
article/evidence payload. They do not build or validate the v1.0.1 reading files.
For those, use the [current article reproduction instructions](papers/shifted-square-17-41/manuscript/revision/README.md#reproduction).

#### Prepare public tools and dependencies

Use Python 3.11 or later and install the exact Python dependencies into a
separate virtual environment with:

```sh
python3 -m venv /tmp/paper1-python
/tmp/paper1-python/bin/pip install --require-hashes -r papers/shifted-square-17-41/verification/requirements.lock
```

The ancillary verifier requires SymPy 1.14.0 and mpmath 1.3.0. The supplied
HTML recipe uses Pandoc and the three pinned Beautiful Soup dependencies.
Install PARI/GP (tested 2.17.3), Pandoc, Poppler (`pdftotext`), and a normal
pdfLaTeX distribution. Tectonic 0.16.9 is the alternative TeX engine used for
the release PDF; that path requires a separately populated public TeX cache
and uses `--untrusted --only-cached`. It never silently downloads during a
check. PDF bytes need not agree across TeX engines or versions.

Install the exact Lean version in `lean-toolchain`. Prepare the nine public
Lake dependencies at the revisions in `lake-manifest.json`, including the
usual matching public Mathlib build cache. This is a setup operation, separate
from verification. Do not copy private build outputs into the extracted source
root. The exported Lean root imports only the 60 local modules in the source map.

#### Run the five v1.0.0 operations

From the source root:

```sh
make paper1-check PAPER1_PYTHON=/tmp/paper1-python/bin/python
make paper1-verify PAPER1_PYTHON=/tmp/paper1-python/bin/python
make paper1-build PAPER1_PYTHON=/tmp/paper1-python/bin/python
make paper1-stage PAPER1_PYTHON=/tmp/paper1-python/bin/python
PAPER1_PUBLIC_LAKE_PACKAGES=/path/to/prepared/public/packages make paper1-check-export PAPER1_PYTHON=/tmp/paper1-python/bin/python
```

Each operation creates a new directory under `.paper1-build/`, records its
exact source inventory and subprocess outputs, and refuses to overwrite an
earlier run. To repeat, set `PAPER1_OUT` to a fresh directory. A missing tool,
dependency mismatch or failed command is a failed operation.

`check` verifies source and manuscript identities, the mathematical freeze,
the HTML's embedded source, the printed program and dependency versions.
`verify` runs the unchanged ancillary, the original GP checks, distinct replay,
Lean build, the exact 21-declaration axiom audit, and corruption controls.
`build` compiles the actual TeX and rebuilds the supplied HTML recipe.
`stage` creates `paper1-arxiv-source.zip` and `paper1-evidence-source.tar.gz`
from explicit allowlists. `check-export` freshly stages and extracts both,
checks every payload hash, rebuilds the article and runs the exported evidence
operations and default Lean root in a temporary directory without private
Git history or inherited Python/Lean search paths. Only separately prepared,
revision-checked public Lake dependencies are copied into that directory.

The three missing historical Magma inputs (17-B, 41-A, 41-B) are an explicitly
disclosed corroboration limitation. The archived responses are not complete
Magma replay inputs. The article's required finite verifier and the GP/Lean
verification do not depend on those missing files.

Historical core records retain their historical meaning. Every new operation
reports PASS or FAIL for its actual inputs. These software checks do not
formalise the human Hilbert, maximality or Pell exposition and do not confer
mathematical acceptance. The release-gate results for the published commit
are recorded in the release notes and in the release record kept outside this
archive, so that the archive does not contain its own hash.

</details>

## Citation, licence and provenance

Chey G. A. Loveday, Overdog.ai Ltd, Colchester, England.
Current article: **version 1.0.1, 30 September 2026**, an editorial correction.
Formal and arithmetic support: **version 1.0.0, 11 September 2026**.

Read the corrected [PDF](papers/shifted-square-17-41/manuscript/revision/paper1.pdf),
[standalone MathML HTML](papers/shifted-square-17-41/manuscript/revision/paper1.html),
[editable Markdown](papers/shifted-square-17-41/manuscript/revision/paper_1.md),
and [corrections, proof correspondence and reproduction instructions](papers/shifted-square-17-41/manuscript/revision/README.md).
The [complete article source ZIP](papers/shifted-square-17-41/manuscript/revision/paper1-source.zip)
and [download checksums](papers/shifted-square-17-41/manuscript/revision/SHA256SUMS)
are also available from the [v1.0.1 release](https://github.com/CheyLoveday/erdos-364-shifted-squares/releases/tag/v1.0.1).
Download the HTML and open it locally; it needs no network access.

This correction credits Walker's Pell property-Q exponent, Sanna's Lucas valuation
theorem and classical Dickson composition, updates She's journal reference, and
clarifies Corollary 1.5. The original 696 mathematical expressions and all twelve
numbered results are retained; the explanatory adapters add expressions. No new
17/41 theorem or new formal proof is claimed.

The unchanged [v1.0.0 evidence release](https://github.com/CheyLoveday/erdos-364-shifted-squares/releases/tag/v1.0.0)
is reference [8] of the article. It contains the exact-arithmetic verifier, PARI/GP
and Python replays, 60 local Lean modules, their audit and the original reproduction
tools. The [frozen proof record](papers/shifted-square-17-41/PROOF_RECORD.md)
and [v1.0.0 execution record](RELEASE-v1.0.0.md) retain their exact source identities.
The v1.0.1 correction note adds correspondence without relabelling those receipts.

Preserved earlier views: [v1.0.0 manuscript](papers/shifted-square-17-41/manuscript/candidate/paper_1_release_candidate.md),
[PDF](papers/shifted-square-17-41/manuscript/candidate/paper_1_release_candidate.pdf),
[HTML](papers/shifted-square-17-41/manuscript/candidate/paper_1_release_candidate.html),
and [portable Markdown](papers/shifted-square-17-41/manuscript/paper_1_final_frozen_portable.md).
The separate [illustrated explanation](papers/shifted-square-17-41/manuscript/explanation/paper_1_explained_illustrated.html)
([Markdown prose](papers/shifted-square-17-41/manuscript/explanation/paper_1_explained.md))
also remains unchanged.

### Licence, citation and AI use

The article, explanatory guide, its five figures, the proof record and the
data/certificates are released under CC BY 4.0; the original code under
Apache-2.0. See [LICENSE.md](LICENSE.md) and cite via
[CITATION.cff](CITATION.cff). The embedded mathematical glyphs retain their
[MathJax attribution and licence](papers/shifted-square-17-41/verification/notices/README.md).

As stated in the article's Acknowledgements: AI assistants (Anthropic Claude
and OpenAI ChatGPT/Codex) were used for drafting and editing prose,
challenging arguments, writing and running verifiers, and repository
engineering. All mathematical statements, proofs and publication decisions
were reviewed by the author, who takes sole responsibility for them.

### Publication status and preserved artifacts

Version 1.0.1 is a self-published editorial correction. No DOI, arXiv identifier,
journal submission or peer review is asserted. Its formal and arithmetic evidence
remains the v1.0.0 source release; historical audit/build receipts are not fresh
runs for the correction or for subsequent documentation changes.

The explanatory guide is a separate artifact: its five figures are embedded in
its HTML, and its Markdown contains the prose and equations. No complete
illustrated-guide renderer is supplied.
