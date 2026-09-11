# Licences

Copyright (c) 2026 Chey G. A. Loveday (Overdog.ai Ltd, Colchester, England).

This release contains three kinds of original material, licensed by kind.

| Material | Files | Licence |
| --- | --- | --- |
| Article, explanatory guide and figures, proof record and other prose documents | `*.md`, `*.pdf`, `*.html`, `*.tex`, the article source ZIP, the five SVG diagrams embedded in the explanatory guide | [CC BY 4.0](LICENSES/CC-BY-4.0.txt) |
| Original code | `*.py`, `*.gp`, `*.lean`, `*.m`, `Makefile`, `*.mk`, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `requirements.in`, `requirements.lock` | [Apache License 2.0](LICENSES/Apache-2.0.txt) |
| Data and certificates | finite certificate tables, PARI/GP, Lean and Python outputs, `*.json` records, `*.txt` logs, `SHA256SUMS` and other hash lists | [CC BY 4.0](LICENSES/CC-BY-4.0.txt) |

The exact-arithmetic verifier printed in Appendix C of the article is part of
the CC BY 4.0 article text and is also available, as
`anc/verify_fixed_fields.py` and `experiments/` sources, under Apache-2.0.

Attribution: cite the release as given in [CITATION.cff](CITATION.cff).

## Third-party material

The HTML views embed rendered SVG glyph geometry from the MathJax TeX fonts,
Copyright (c) 2018–2022 The MathJax Consortium, Apache License 2.0; see the
[notice](notices/README.md). Lean 4, Mathlib and the other Lake dependencies,
PARI/GP, SymPy, mpmath, Beautiful Soup, Pandoc and TeX are installed
separately under their own licences and are not vendored here.

## Boundaries

These licences cover redistribution and reuse. They do not assert mathematical
acceptance, peer review, a DOI or an arXiv identifier, and they do not extend
to any private repository, branch or history outside this release.
