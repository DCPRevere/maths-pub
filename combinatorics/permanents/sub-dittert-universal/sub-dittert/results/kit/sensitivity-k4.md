# Insensitivity of the (k = 4) threshold to the collar constant c

**Grade: a verified sensitivity computation, not a theorem.** This file is the
displayed record that `graded_verify_k4.py` parses and recomputes, row by row,
exactly over Q. It was moved here out of the paper body; the paper cites it in
one sentence in its section on the collar assembly. Displayed and checked
cannot drift apart: the verifier reads *this* file and fails if the table is
not exactly ten rows or if any row disagrees with its own exact recomputation.

## What c is

On the doubly stochastic slice the row squared norms of the doubly centred
block obey `q_i(z) <= 1 - 1/n`. That bound needs row sums equal to 1 **and**
non-negativity. On the collar `J_n/n + z` has row sums 1 but may have negative
entries, so the bound does not transfer, and it is refuted: a permutation with
one reweighted row violates it by a factor 1.63 at (k = 4, n = 10) and 1.58 at
(k = 4, n = 11). The argument therefore carries `q_i(z) <= c (1 - 1/n)` with c
symbolic, and c is the one constant of the (k = 4) argument that is not
settled.

The admissible band is `1.58 <= c <= 2.53`: below it the constructed violation
forbids, above it the proved collar cap forbids. The lower end is the
**smallest constructed violation**, never a claimed true minimum.

## The table

Ten sampled values of c, each with the honest threshold recomputed exactly
over Q. The threshold is 10 at every sampled value inside the admissible band.

| c | honest threshold |
|---|---|
| 1.00 (slice value; refuted on the collar) | 9 |
| 1.25 | 9 |
| 1.50 | 9 |
| 1.58 (smallest constructed violation, at n = 11) | 10 |
| 1.63 (largest constructed violation, at n = 10) | 10 |
| 2.00 | 10 |
| 2.34 (collar cap, low) | 10 |
| 2.53 (collar cap, high) | 10 |
| 3.00 | 11 |
| 4.00 | 11 |

**No claim is made for unsampled c.** The grade sentence is the claim.

## The audited structure

Only three budget lines involve c: the `sigma_4` core line is *linear* in it,
and the two `Y_3` lines ride on `sqrt(c)`. Everything else — the m = 3 core,
Xi, the line tail, `X_1`, `Y_1`, `Y_2` — is independent of it. That
decomposition is not read off the derivation alone: it is asserted
mechanically, every budget line recomputed at c and 2c, at n = 10 and n = 16,
with the run aborting on any change, so a line that silently acquired a
c-dependence would kill the computation rather than skew it. At n = 10 the
linear share of the centred column is 0.379 and the total exposure 0.488; by
n = 20 these are 0.311 and 0.341.

What the computation establishes is direction: sharpening the constant cannot
improve the theorem at any sampled value, and no sampled weakening within the
cap damages it.

## Reproducing

From `sub-dittert/`:

```
GUARD_MEM=8G GUARD_CPUS=250% GUARD_THREADS=2 ../guard.sh \
    python3 -u graded_verify_k4.py
```

Section 9 of the output parses this file, asserts it has exactly ten rows,
recomputes each threshold over Q, and asserts the band is flat at 10.
`--mutate` reruns the controls alone; control M4 rescales c inside a
c-independent line and must be rejected by the sensitivity audit.
