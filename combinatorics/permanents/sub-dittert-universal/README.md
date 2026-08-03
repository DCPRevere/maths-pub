# The Cheon–Hwang Sub-Dittert Conjecture, in Full

*One capacity chain for 3 ≤ k ≤ n−1, the two endpoint lines, and the equality
case at every cell.*

D C P Revere — dcprevere@gmail.com

## What the paper proves

Cheon and Hwang conjectured in 1992 that

    E_k(r) + E_k(c) − P_k(A)  ≤  2 − k!/n^k

for every non-negative n × n matrix A of total sum n and every 1 ≤ k ≤ n, with
equality only at J_n/n. The endpoint k = n is Dittert's conjecture; on the
doubly stochastic face the statement is the Tverberg–Friedland theorem, so all
of the content sits off that face.

This directory carries a proof at every cell (k, n) with 2 ≤ k ≤ n, inequality
and equality case alike, **with every line of the assembly graded separately**,
because the lines do not have the same strength. The interior 3 ≤ k ≤ n−1 runs
on one mechanism: border A into a (2n−k) × (2n−k) matrix whose permanent is
((n−k)!)² σ_k(A), price that permanent below by its capacity, and pay the price
with an entropy witness written down in closed form from A itself. What is new
is the composition off the face — a closed form for the unrefined constant
(Theorem F), an exact arithmetic identity showing that repricing the n − k
identical border rows as one degree-(n−k) extraction pays the shortfall to the
last digit, and a strictness theorem with slope 1 − θ ≥ 0.7308.

### The honest grade of the k = n line

**Read this before quoting the plane claim.** The line k = n is Dittert's
conjecture, and the assembled all-cells statement inherits that line's grade
wherever it is quoted:

| n | source of record | grade |
|---|---|---|
| 2 | Sinkhorn 1984 | refereed |
| 3 | Hwang 1987 | refereed |
| 4, 5 | the anchor certificates in this kit | *we* checked it — nobody refereed it |
| 6 ≤ n ≤ 15 | Lu, revision 2.0 | unrefereed public source, re-derived here |
| 16 | Kafidov | unrefereed preprint, re-derived here |
| ≥ 17 | Pang | unrefereed preprint, re-derived here |

Dittert's conjecture is described in the current refereed literature as
unsettled, and nothing here changes that. The n = 4 and n = 5 certificates are
**independent confirmation, not priority**: a public July 2026 assembly already
contains an n = 4 claim, and that is the first public one. The k = n line is
also *not* formalised in Lean at any n.

## Layout

- [`paper.pdf`](paper.pdf) — **the paper.** Typst source alongside as
  `paper.typ`, and again under `sub-dittert/results/`.
- `sub-dittert/` — the verification kit: the runner, the 22 graded verifiers,
  the trusted standalone verifiers, their import closure, and `results/` with
  the stored certificates, witnesses and run logs.
- `dittert/` — the sibling directory for the k = n work. It must stay a
  sibling: several scripts put `../dittert` on `sys.path`, and
  `sub-dittert/expand.py` deliberately shadows `dittert/expand.py`. Flattening
  the two directories silently changes what is being computed.
- `leanproj/` — the Lean 4 development, as a standalone lake project.
- `guard.sh` — a resource guard. Every solve is meant to run under it; some of
  these computations are large enough to take a machine down without it.

## Running the kit

One command discovers and runs every graded verifier in sequence, and exits
non-zero if any of them fails:

```
cd sub-dittert
../guard.sh python3 verify_all.py
```

Twenty-two verifiers are discovered (21 named `graded_verify_*.py`, plus
`bern_verify.py`). The reference run reports `VERIFIERS: 22/22 pass` with
`OVERALL: ALL VERIFIERS PASS`; that run is stored as
`sub-dittert/results/verify_all.log`. Requirements: Python 3.12 or later,
`numpy`, and `sympy` (needed by `graded_verify_d15.py` alone). `scipy` and
`cvxpy` are imported only inside solver paths that no verifier takes.

Each verifier writes or redirects to a log of the same name under
`sub-dittert/results/`; the one exception is `graded_verify_d15.py`, whose log
is `results/d15_verify.log`.

### What the main files back

| file | the claim it carries |
|---|---|
| `graded_verify_capfrontier.py` | Theorem F, and the exact price of each further line — 29 checks, 10 controls |
| `graded_verify_borderrows.py` | Theorems G′/H′, the extraction bound re-derived from Newton — 20 checks, 7 controls |
| `graded_verify_thmb.py` | the entropy witness, its exactness on the face, and (C1)(C2)(C3) — 32 checks, 9 controls |
| `graded_verify_strict.py` | Theorem E, the König corner, and **Lemma T** — steps (T0)–(T5), the crossover n₁ = 10 and the 21 exact cells below it — 42 checks, 8 controls |
| `graded_verify_kn.py` | Theorems K and K′, the σ₂ threshold, the refutation of (S′) — 35 checks, 9 controls |
| `graded_verify_u5core3.py` | the core census, the four core lemmas, L-CUT — 727 checks |
| `graded_verify_canon.py` | the sweeps establishing e₀ = 12 — 2106 checks |
| `graded_verify_universal.py` | the composed Theorem U and its interface — 301 checks |
| `results/verify_subdittert.py` | the **trusted** verifier: first acceptance of any sub-Dittert certificate goes through it, and it shares no code with the producer. Run it as `python3 results/verify_subdittert.py results/<file>_certificate.json`; with no argument it checks the n = 4, k = 3 certificate. |
| `dittert/results/check_certificate_json.py` | the same role for the Dittert n = 4 and n = 5 certificates in `dittert/results/` |
| `diag_anchor.py`, `dittert_n4.py`, `dittert_n5k5_blocks.py`, `h2_anchor*.py` | the audit rebuilds behind the k = n table, driven off `results/witness/` |
| `u5_scan*.py`, `u5_sep.py`, `u5_probe3.py`, `u5_sweep1314.py` | the census sweeps behind the core section |
| `falsify_*.py` | the refuted strategy classes, each with a stored exact witness under `results/witness/` |

Every verifier carries **fault-injection controls**: deliberate corruptions
that must make it fail. A verifier with no firing control is treated here as
unverified, and the control counts above are quoted from the verifiers' own
logs. No floating-point number enters any accepted statement.

Two of the k = 3 / k = 4 certificates named in the companion paper are large
and are published there rather than duplicated here; see
[`../sub-dittert-k3/`](../sub-dittert-k3/).

## Verifying the Lean development

Requires [elan](https://github.com/leanprover/elan). The toolchain
(`leanprover/lean4:v4.14.0`) and the Mathlib pin are recorded in
`leanproj/lean-toolchain` and `leanproj/lake-manifest.json`.

```
cd leanproj
lake exe cache get     # fetch prebuilt Mathlib
lake build
lake env lean SubDittertK3.lean   # prints the axiom audit for the flagship
```

The development elaborates with no `sorry`, no declaration depends on
`sorryAx`, and `native_decide` is used nowhere. Every file ends with a
`#print axioms` block; every declaration cited by the paper reports a subset of
`[propext, Classical.choice, Quot.sound]`. Build success is not an axiom audit,
and the two are kept separate here.

`NewtonCrosscheck.lean` is an independent second proof of the Newton/Maclaurin
material by a different route; it ships as a file but is deliberately not a
build target.

**One thing an axiom audit will not tell you.** `Gurvits.lean` states Gurvits'
capacity theorem as a *named hypothesis*, at exactly the strength the chain
consumes — not as a proof and not as an `axiom`, so it does not appear in
`#print axioms` output. Anything in `LemmaU.lean` or `BorderPayment.lean` that
consumes it is conditional on it. That is the honest shape: Gurvits' theorem
needs H-stable polynomials and the full Gurvits induction, and Friedland's
equality theorem is a rock of the same size. Nothing in the capacity chapter of
the paper is kernel-checked, and the obstruction is external rather than
internal.

What *is* kernel-checked: the line k = 3 in full (inequality, equality case and
the stability bound) as `SubDittertK3.subDittert_k3_full`; the line k = 2
(`SubDittertK2.subDittert_k2`); the uniform layer identity at every k ≤ n
(`universal_identity`); confinement at every k with its Maclaurin hypothesis
discharged (`theoremM'`, `confinement'`); Newton's inequalities and Maclaurin
for every real-rooted real polynomial (`newtonAt_all`, `newton_esymF`,
`pnorm_le_two`), neither of which is in Mathlib v4.14.0; the
Tverberg–Friedland stability form at k = 2, 3, 4, 5; the padding refutation;
and the shifted-coefficient framework.

## Note

This is a curated extract of a larger private research repository: the code,
the logs, the certificates and the paper, not the working notebooks. The
stored witnesses under `sub-dittert/results/witness/` together with the trusted
standalone verifiers are the checkable record of every verdict the paper cites.

Nothing here is refereed, including the paper. Priority claims of any kind are
perishable and should be re-checked before they are relied on.
