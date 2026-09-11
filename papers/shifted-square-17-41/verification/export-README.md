# Shifted-square obstructions at indices divisible by 17 or 41 in a family of Lucas sequences

Chey G. A. Loveday, Overdog.ai Ltd, Colchester, England.
Version 1.0.0, released 11 September 2026; mathematical content frozen
10 September 2026.

This is the public source and evidence release for the article; as a
software and data release it is named *Fixed-field certificates and
integer-Jacobi formal proofs for the 17/41 shifted-square obstruction* and
is reference [8] of the article. It contains
the article in four views, an explanatory guide, the human proof record, the
exact-arithmetic verifier, PARI/GP and Python replay checks, the Lean 4
sources with their axiom audit, and the tooling that rebuilds and re-checks
all of it from a fresh extraction.

Read the [article](../manuscript/candidate/paper_1_release_candidate.md),
[portable Markdown](../manuscript/paper_1_final_frozen_portable.md),
[PDF](../manuscript/candidate/paper_1_release_candidate.pdf),
[HTML](../manuscript/candidate/paper_1_release_candidate.html), the
[proof/source correspondence](../PROOF_RECORD.md), and the
[illustrated explanation](../manuscript/explanation/paper_1_explained_illustrated.html)
([Markdown prose](../manuscript/explanation/paper_1_explained.md)). In the
extracted archive those files are under `papers/shifted-square-17-41/`.
GitHub shows the HTML views as source; download them, or clone the
repository, and open them in a browser. They need no network access.

The portable Markdown is a presentation derivative for Markdown readers, not
a replacement input for the supplied frozen HTML rendering recipe. Its
mathematical content and verifier agree with the article. The
[metadata update record](../manuscript/METADATA_UPDATE.md) lists the exact
author, acknowledgement and reference [8] changes between the frozen
10 September manuscript and these release views, with both sets of hashes.

## Licence, citation and AI use

The article, explanatory guide, its five figures, the proof record and the
data/certificates are released under CC BY 4.0; the original code under
Apache-2.0. See [LICENSE.md](LICENSE.md) and cite via
[CITATION.cff](CITATION.cff). The embedded mathematical glyphs retain their
[MathJax attribution and licence](notices/README.md).

As stated in the article's Acknowledgements: AI assistants (Anthropic Claude
and OpenAI ChatGPT/Codex) were used for drafting and editing prose,
challenging arguments, writing and running verifiers, and repository
engineering. All mathematical statements, proofs and publication decisions
were reviewed by the author, who takes sole responsibility for them.

## Status and scope

Version 1.0.0 is a self-published source release. No DOI, arXiv identifier,
journal submission or peer review is asserted. The human Hilbert-reciprocity,
maximality and Pell arguments are not Lean-formalised; the Lean development
covers the integer-Jacobi and recurrence exclusions and their propagation, as
the proof record sets out. No 73/97 result, Brauer continuation or complete
resolution of Erdős 364 is included. The explanatory guide is a separate
artifact: its five figures are embedded in its HTML and its Markdown contains
the prose and equations; no complete illustrated-guide renderer is supplied.
Continuation research is outside this release.

## Prepare public tools and dependencies

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

## Run the five operations

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
