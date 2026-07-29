# maths-pub

D C P Revere — dcprevere@gmail.com

The public portion of my mathematics work, organised as
**field / subfield / paper**. Each paper directory is self-contained: its own
README, the paper, the formalisation, and the exact computational artifacts.

## Contents

### combinatorics

- **permanents**
  - [`sub-dittert-k3/`](combinatorics/permanents/sub-dittert-k3/README.md) —
    **The Cheon–Hwang Sub-Dittert Conjecture at k = 3, for Every Dimension.**
    The k = 3 case of the 1992 Cheon–Hwang conjecture, proved for every
    n ≥ 4 with equality case and a quantitative stability bound; every stated
    theorem is machine-checked in Lean 4. Paper, full Lean development, and
    exact verification pipeline.

## Standards

Every paper directory follows the same rules: results stated as theorems are
backed by Lean proofs audited with `#print axioms` down to
`[propext, Classical.choice, Quot.sound]`; computational claims carry stored
exact-rational witnesses with standalone verifiers and mutation controls; and
each kit's `README-reproduce.md` gives commands that reproduce every number
from the artifacts alone.
