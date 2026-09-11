# Frozen-mathematics HTML rendering

Tested with Pandoc 3.1.11.1 and the Python package versions in requirements.txt.
These are version pins, not hash-locked distribution files.

```sh
python render_html.py ../paper_1_release_candidate.md ../paper_1_release_candidate.html
```

Run from this directory, or supply absolute manuscript/output paths.
The renderer uses template.html and math-cache.json next to the script.
It rebuilds the complete HTML from the Markdown using the existing exact SVG
and assistive MathML for the unchanged mathematics. It fails if a formula is
not in the frozen cache. No network request, external font file or browser
JavaScript is required to display the mathematics. The cache contains
rendered equation geometry, not downloadable font files.

The HTML retains the TeX view, equation-preserving selection copying, and
embedded complete Markdown. It was exercised at 320, 390, 768 and 1280 pixels,
including display with JavaScript disabled. Two wide tables scroll internally
at 320 pixels; the document and equations do not overflow.
