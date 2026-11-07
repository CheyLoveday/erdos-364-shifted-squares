# Reproduction targets

The two Lean targets use different frozen sources and dependencies. Choose one
complete package; do not mix their toolchains or manifests.

| Target | Current evidence | Start here |
| --- | --- | --- |
| Public release at `c663b4e`, Lean 4.31.0 | Standalone reproduction passed with the explicitly declared five-checksum metadata patch. Includes selected formal checks, fixed-field certificates and the bounded core runner. | [Recipe and receipt](public-c663b4e/RECEIPT.md), [inputs and qualifications](public-c663b4e/INPUTS.md) |
| October frozen selection, Lean 4.35.0 | Original six-checker result retained; exact sources/pins recovered and offline staging checked. **Fresh Linux replay pending.** | [Recovered inputs and staging](lean435-20261025/README.md), [remaining replay work](lean435-20261025/REPLAY.md) |

The [October assurance note](../verification/LEAN-ASSURANCE-2026-10-25.md) is
historical evidence, not a new run receipt. Neither reproduction extends the
paper's 17/41 domain or newly formalises the human Hilbert/Pell arguments.
