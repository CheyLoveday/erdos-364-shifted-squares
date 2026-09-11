# Embedded mathematical glyph attribution

The supplied HTML and `manuscript/candidate/rendering/math-cache.json` contain
rendered SVG glyph geometry from the MathJax TeX fonts. All 137 unique glyph
geometries in the supplied cache match the following tagged MathJax 3.2.2
source files (apart from the renderer's enclosing `M` and `Z` path commands):

<https://github.com/mathjax/MathJax-src/tree/3.2.2/ts/output/svg/fonts/tex>

- `normal.ts`
- `largeop.ts`
- `smallop.ts`
- `sans-serif.ts`
- `tex-calligraphic.ts`
- `tex-oldstyle.ts`
- `tex-size3.ts`

Those files carry **Copyright (c) 2018–2022 The MathJax Consortium**, under
the Apache License, Version 2.0. The accompanying
[licence text](MathJax-3.2.2-LICENSE.txt) is copied unchanged from
<https://github.com/mathjax/MathJax-src/blob/3.2.2/LICENSE>.

Version 3.2.2 identifies a verified matching source; the supplied handoff does
not establish the exact MathJax version originally used to render the baseline.
The cache wraps/scales these paths as equation SVG geometry with assistive
MathML. It does not contain a MathJax runtime or a downloadable font file.

This notice accompanies the frozen rendering without changing its bytes.
It is a third-party attribution only. Chey G. A. Loveday's article, guide,
figures and data are released under CC BY 4.0 and the original code under
Apache-2.0, as set out in [LICENSE.md](../LICENSE.md). Python, Lean/Mathlib,
PARI/GP, Pandoc and TeX dependencies are installed separately and are not
vendored in the evidence archive.

The separate supplied illustrated guide,
`manuscript/explanation/paper_1_explained_illustrated.html`, also contains
MathJax-rendered SVG glyph geometry and is distributed with this same notice
and licence. Its glyph geometry shares 109 distinct nonempty paths exactly with the
article. This is attribution of matching glyph source, not identification
of the original guide renderer version or a licence for its five diagrams.
