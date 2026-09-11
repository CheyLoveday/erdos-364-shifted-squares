# Fresh frozen-manuscript candidate checks

These are actual executions at implementation commit
`ec75fa8076bf783cb7be819c28534b7fbe813012`, following its independent repair
review. `verify/` records the ancillary, twelve failure controls and core
coordinator. `core/` contains the ten individual GP/Python/Lean records,
environment, exact source inventory and 21-declaration axiom output.
`build/` records the actual offline TeX build and supplied HTML renderer.

All recorded operations passed. These records precede their addition to the
export allowlist; they are not assertions that the subsequently assembled
archive has already passed fresh extraction. The final export run has its
own archive hashes, source inventory and external result record. No record
hashes itself or labels an earlier run as an execution of a later archive.

Python 3.13.1 used the five exact hash-locked dependency versions in the
recorded environment. `tool-versions.json` gives the observed TeX/Pandoc/
Poppler versions; the core environment separately identifies Lean/Lake/GP.

The build used Tectonic with only pre-provisioned public resources. Its
`lineno.sty:296` warning concerns a Latin-1 character in the cached package's
copyright/history comment, not article content. There are no LaTeX reference
or box diagnostics. The supplied and rebuilt PDFs both have 22 pages; their
bytes and text extraction differ between pdfLaTeX and Tectonic. No PDF byte
parity is claimed. The HTML bytes differ with Pandoc 3.9.0.2 versus the
supplied build's 3.1.11.1, while mathematical geometry, full article text and
link targets compare identically.

These are software execution records. They do not constitute independent
human review, public release, or a Lean formalisation of Hilbert reciprocity.
