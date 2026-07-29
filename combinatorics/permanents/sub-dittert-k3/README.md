# The Cheon–Hwang Sub-Dittert Conjecture at k = 3, for Every Dimension

D C P Revere — dcprevere@gmail.com

This directory contains the paper, the Lean 4 formalisation, and the exact
computational artifacts for the resolution of the k = 3 case of the
Cheon–Hwang sub-Dittert conjecture (Cheon & Hwang, *Linear Algebra Appl.* 165,
1992) for every dimension n ≥ 4, with its equality case and a quantitative
stability bound.

## Layout

- `sub-dittert/results/paper_b.pdf` — the paper (Typst source alongside).
- `sub-dittert/results/kit/` — abstract, submission metadata, and
  `README-reproduce.md`, the step-by-step reproduction guide. Start there.
- `leanproj/` — the Lean 4 development. Every result the paper states as a
  theorem is a Lean theorem here, cited in the paper by declaration name.
- `sub-dittert/*.py`, `sub-dittert/results/` — the exact-arithmetic
  verification scripts, certificates, and stored witnesses described in the
  kit's file manifest.

## Verifying the Lean development

Requires [elan](https://github.com/leanprover/elan); the toolchain
(`leanprover/lean4:v4.14.0`) and the Mathlib pin are recorded in
`leanproj/lean-toolchain` and `leanproj/lake-manifest.json`.

```
cd leanproj
lake exe cache get     # fetch prebuilt Mathlib
lake build             # builds all ten libraries
lake env lean SubDittertK3.lean   # prints the axiom audit for the flagship
```

Each file ends with a `#print axioms` block. Every named declaration in
`SubDittertK3.lean` (377 of them) and every declaration cited by the paper
reports exactly `[propext, Classical.choice, Quot.sound]`, with one documented
exception on the strict subset `[propext, Quot.sound]`. No file contains
`sorry` or `native_decide`. `NewtonCrosscheck.lean` is an independent second
proof of the Newton/Maclaurin material by a different route; it is deliberately
not a build target.

## Note

This is a curated extract of a larger private research repository. The working
notebooks behind the paper's §10 (computational evidence) are not included
here; the stored witnesses in `sub-dittert/results/witness/` together with the
standalone verifier `sub-dittert/results/verify_pinretest.py` are the checkable
record of every verdict cited there.
