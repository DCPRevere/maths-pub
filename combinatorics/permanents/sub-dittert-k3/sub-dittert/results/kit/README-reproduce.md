# Reproducing the verifying computations

Every command below marked **RUN LIVE** was actually executed for this
kit-readiness pass, with timings from that run, on this machine
(`Python 3.14.6`, `typst 0.15.1`, `Lean 4.14.0` via `elan`, `gh` authenticated
as `DCPRevere`). Commands marked **NOT RUN — cited from a stored log** are
explicitly not reproduced here, with the reason and the exact file that
carries the result instead. Both kinds of line matter equally: don't infer
that everything under `results/` was independently re-checked.

## 1. Fresh clone

```
git clone https://github.com/DCPRevere/maths-pub.git
cd maths-pub/combinatorics/permanents/sub-dittert-k3/sub-dittert
```

The public tree under `sub-dittert-k3/` mirrors the private layout one level
up from this directory: `leanproj/` and `dittert/` are siblings of
`sub-dittert/`, so every relative path in this kit (`../leanproj`,
`../guard.sh`, `../dittert`) resolves identically in both trees.

## 2. The uniform certificate, at n = 4, 5, 6, 7, 12 — RUN LIVE

`verify_general.py` re-derives the objective from the 1992 definition and
uses none of the closed forms, block decomposition or Sturm machinery of the
paper; it checks positive definiteness of both full $n^2\times n^2$ Gram
matrices by exact rational $LDL^T$ and the polynomial identity at random
rational points.

```
python3 verify_general.py 4 5
python3 verify_general.py 6 7
GUARD_MEM=2G GUARD_CPUS=200% GUARD_THREADS=2 ../guard.sh python3 verify_general.py 12
```

Measured: `4 5` together 0.6 s; `6 7` together 1.1 s; `12` alone, under the
guard, **13.2 s** at under 2 GB. An earlier planning note
flagged that the full $\mathbb{Q}$ run at $n=12$ "may not fit" a 5-minute/2 GB
budget — it does, comfortably; the note below explains where a run genuinely doesn't fit.

Reproduced exactly, matching the paper's §6 table:

| $n$ | $\sigma_0$ min pivot | $\sigma_{11}$ min pivot | bound $M$ | identity |
|---|---|---|---|---|
| 4 | 1.236247e-02 | 4.395670e-03 | 61/32 | exact, 2 pts |
| 5 | 3.137884e-03 | 7.137234e-04 | 244/125 | exact, 2 pts |
| 6 | 8.347413e-04 | 1.507055e-04 | 71/36 | exact, 2 pts |
| 7 | 2.850848e-04 | 4.303930e-05 | 680/343 | exact, 2 pts |
| 12 | 9.171518e-06 | 7.769494e-07 | 575/288 | exact, 2 pts |

The $n=4,5,6,7$ row of the paper's own table gives a pivot *range*
("$16$–$49$") rather than per-$n$ values; the table above is the
per-$n$ breakdown behind that range, and the $n=12$ row (9.17e-6, 7.77e-7)
matches the paper's stated figures to the three significant figures quoted
there.

## 3. n = 25 — identity RUN LIVE via F_p; definiteness NOT RUN, cited

At $n=25$ the exact-$\mathbb{Q}$ identity check alone needs about $2.4\times
10^8$ `Fraction` multiplications per point (the paper's and `verify_modp.py`'s
own estimate); `verify_modp.py` instead checks the identity modulo three
large primes, which is exact arithmetic and fast:

```
GUARD_MEM=2G GUARD_CPUS=200% GUARD_THREADS=2 ../guard.sh python3 verify_modp.py 25
```

**RUN LIVE: 19.5 s, under 2 GB.** All three primes, both random points: `True`
in every case, matching the paper's "$F_p$, 3 primes, 2 points" cell exactly.

The *positive-definiteness* half of the $n=25$ row (the paper's quoted
"PD, $1.45\times10^{-7}$" and "PD, $5.80\times10^{-9}$") is **not**
reproduced here. We attempted it — assembling the $625\times625$ exact
rational Gram via `certificate_at(25)` and running `exactsd.ldl_pivots` on it
directly, bypassing the expensive identity step — and it did not complete
within a 2-minute bound (no output at all, so we cannot even say whether
assembly or the $LDL^T$ itself was the slow part). Given `verify_modp.py`'s
own docstring warns the exact-$\mathbb{Q}$ route is "hours" at this $n$, we
did not push further under this pass's 5-minute budget. **The $n=25$
definiteness figures in the paper are therefore cited from the paper's own
§6 table (which matches the equivalent table already recorded in
`../NOTES.md` §6a.8c) and were not independently reverified in this pass** —
flagged explicitly rather than silently assumed checked.

## 4. The four smaller fixed-dimension anchors — RUN LIVE

`verify_subdittert.py` is the standalone verifier for Theorem C: standard
library only, shares no code with the pipeline, checks $\sigma_k$ by two
structurally different algorithms, the bound, the polynomial identity by full
coefficient comparison, positive definiteness by exact $LDL^T$, four mutation
tests, and equality at $J_n/n$.

```
cd results
python3 verify_subdittert.py subdittert_n3k3d2_certificate.json
python3 verify_subdittert.py subdittert_n4k3d1_certificate.json
python3 verify_subdittert.py subdittert_n5k3d1_certificate.json
python3 verify_subdittert.py subdittert_n6k3d1_certificate.json
```

**RUN LIVE, all four, all six checks PASS, exit 0.** Timings: $(3,3)$ 1.2 s,
$(4,3)$ 0.1 s, $(5,3)$ 0.4 s, $(6,3)$ 1.5 s. Bounds reproduced exactly:
$16/9$, $61/32$, $244/125$, $71/36$. Re-run on 2026-07-29 against the same
certificates: all six checks pass in all four cases again (timings not
re-measured).

The verifier prints two minimum pivots per case: the $\sigma_0$ Gram, and the
minimum over **all** $n^2$ multiplier Grams. The paper's §6.1 quotes these.
They are not the same as the pipeline's figures for the same certificate, which
factor the multiplier Gram at the corner $p=(0,0)$ only: the $n^2$ multiplier
Grams are permutation conjugates, so an $LDL^T$ pivot depends on the index
order. Measured, at $(4,3)$: corner $7.318706\times10^{-3}$, minimum over the
sixteen $6.647809\times10^{-3}$. At $(6,3)$: corner $7.112170\times10^{-4}$,
minimum over the thirty-six $6.484085\times10^{-4}$. The paper now names which
matrix each number measures.

## 5. The (5,4) anchor — NOT RUN, cited from a stored log

```
python3 verify_subdittert.py subdittert_n5k4d2_certificate.json   # DO NOT RUN casually
```

This certificate's JSON is 61 MB (`subdittert_n5k4d2_certificate.json`) and
the verifier runs 26 exact rational $LDL^T$ factorisations of size $350$
because the export deliberately avoids trusting or re-deriving the
permutation conjugacy between them (see the paper's own §6.1 for why that
shortcut is refused). The paper states a wall time of 54 minutes; this is
far outside a 5-minute budget and was **not re-run** for this pass.

Instead, cite: `results/verify_n5k4d2.log` (the original run, 2026-07-28
17:28) and `results/verify_n5k4d2_rerun.log` (an independent full re-run to
completion, 2026-07-28 21:13, wall time recorded as `WALL_SECONDS 3245`). We
did read both logs in full for this pass and confirmed they agree, including
to the seventh digit on both minimum pivots ($5.827857\times10^{-4}$ for
$\sigma_0$, $5.874542\times10^{-4}$ across the 25 multiplier Grams) — the
second of which corrects a transcription slip in the paper itself (see the
fact-check report; the paper previously read $5.92\times10^{-4}$ in one of
two places it quotes this number, and now reads $5.87\times10^{-4}$ in both).

## 6. The Lean development

The development has grown from two files to eight. The paper now cites Lean
support for Theorems A and C–F, so the file list below supersedes the earlier
two-file list; the re-elaboration procedure is unchanged.

**The eight files, and the paper's theorem each one carries.** Counts are of
`#print axioms` commands in the Lean sources as committed at `32c811e`, the
commit at which they were last changed — a source count, checked for this pass,
not a re-elaboration:

| file | audits | paper's result |
|---|---|---|
| `SubDittertK3.lean` | 377 | Theorem A (`subDittert_k3_full`) |
| `RookSum.lean` | 7 | Theorem A, combinatorial half |
| `SubDittertUniversal.lean` | 21 | Theorem C (`universal_identity`) |
| `SubDittertLinear.lean` | 37 | the `e_k` coefficient rule under Theorem C |
| `SubDittertK2.lean` | 17 | Theorem D (`subDittert_k2`, `E_two_eq`) |
| `SubDittertM.lean` | 13 | Theorem E (`theoremM`, `confinement`) |
| `SubDittertMaclaurin.lean` | 6 | Theorem E unconditional (`theoremM'`, `confinement'`) |
| `NewtonInequalities.lean` | 33 | Theorem F (`newtonAt_all`, `newton_esymF`, `pnorm_le_two`) |

Total 511. In `SubDittertK3.lean` the 377 audit lines are in one-to-one
correspondence with the file's 377 named declarations — checked by matching the
two lists, not by trusting the count — so nothing in the file carrying Theorem A
is unaudited. The other seven files audit the theorems the paper cites and their
supporting lemmas, but not every private definition; the one declaration the
paper names without an audit line is `choose_subset_of_subset`, mentioned only as
a Mathlib PR candidate and backing no stated result. Per-file coverage
(audited / named declarations): K3 377/377, Maclaurin 6/6, K2 17/18, M 13/14,
Universal 21/25, Linear 37/46, Newton 33/39, RookSum 7/37. (The RookSum
denominator previously read 38: a docstring line beginning "theorem there
is `rfl`..." was counted as a declaration named `there` by a
column-anchored regex. True declaration count at `32c811e`: 37. The
current tree audits all 37 — see `LEAN-COVERAGE.md`.)

Partial coverage is not a gap, and the reason is worth stating because a count
invites the wrong inference: `#print axioms` reports the axioms of the
*transitive closure* of a proof term, so auditing a theorem audits every
definition and lemma that theorem rests on. No file contains a `sorry`, so
nothing in any of them can acquire `sorryAx` from within. What a per-file count
would add is coverage of declarations on which no stated result depends, and
those cannot affect a stated result.

`NewtonCrosscheck.lean` adds 12 more and is deliberately **outside**
the lakefile: it is a second, independent proof of Theorem F, stored as
evidence, and elaborates with `lake env lean NewtonCrosscheck.lean`.

**Theorem G's files** are additional to the eight above:
`StabilityK3.lean` (33 audited; `stabilityAt_two`, `stabilityAt_three`,
`three_threshold_not_slack`), `TverbergStability.lean` (21 audited;
`StabilityAt`, `cVal`, `witness33`, `not_stabilityAt_three_three`, the
`phiPoly` threshold layer), `LayerIdentity.lean` (28 audited;
`layer_identity` at every k under the weak hypothesis), `SigmaFour.lean`
(46 audited; `sigma_four_centred`, the (4.3) core expansion at every centred
B) and `StabilityK4.lean` (14 audited; `stabilityAt_four`, the
kernel-checked $(k=4, n\ge8)$ cell). The paper cites them at their own
commits — `1507013` for the first two, `27bda3f`, `365e44e` and `944b517`
respectively for the rest — and `graded_verify_stability.py`'s V12 (§7a)
checks the paper's scope claims against exactly those commits, with the
orphan diff and the sorry scan. `StabilityK5Atoms.lean` (15 audited, commit
`f2bdc7f`) is partial atom coverage at k = 5 — the paper cites it as
exactly that, and the (k = 5, n ≥ 14) cell stays at written-proof +
exact-verifier grade. Re-elaboration follows the same procedure as above;
per-file counts are in `LEAN-COVERAGE.md`.

One declaration, `NewtonIneq.choose_mul_sub`, returns the strict subset
`[propext, Quot.sound]`; every other audited declaration returns exactly
`[propext, Classical.choice, Quot.sound]`. See
`problems/permanents/LEAN-COVERAGE.md` for the whole-tree audit record.

### Re-elaboration — RUN LIVE for `SubDittertK3` and `RookSum`

The run below was executed for an earlier kit-readiness pass, against the two
files that carry Theorem A; the counts it reports are of that earlier state
(52 + 7 = 59 audits) and the audit block has since been extended to every named
declaration, 377 + 7 = 384. The *procedure* is what this section is for, and it
is unchanged. Budget more time for the larger block.

```
cd ../../leanproj
lake build SubDittertK3
lake build RookSum
```

A cached `lake build` returns in under a second on a warm Mathlib cache but
does **not** replay the `#print axioms` output, so it cannot be used to check
the axiom claims. Elaborate the files instead:

```
lake env lean SubDittertK3.lean 2>&1 | grep "depends on axioms"
lake env lean RookSum.lean      2>&1 | grep "depends on axioms"
```

**RUN LIVE, both files, exit 0.** Result: **59 declarations carry a
`#print axioms` command — 52 in `SubDittertK3.lean`, 7 in `RookSum.lean` — and
every one of the 59 returns exactly `[propext, Classical.choice, Quot.sound]`**,
`subDittert_k3` included. No declaration depends on `sorryAx`; the string
`sorryAx` does not appear in either transcript. `native_decide` is not used
anywhere. Neither elaboration emits a `declaration uses 'sorry'` warning; what
they do emit is three harmless linter warnings (two unused variables in
`SubDittertK3.lean`, one tactic-combinator style note in `RookSum.lean`).

This is a full re-elaboration, not a replay of a stored log, and it is the
check that matters: a file with no `sorry` in its source can still rest on
`sorryAx` through an import.

Budget it: a cold whole-file elaboration peaks near 5.7 GB of elaborator memory
and takes about three and a half minutes. Under a 2 GB guard it will not
complete.

**Scope note.** The 59 are the declarations with an explicit `#print axioms`
command written into the source — the ones the paper cites. Neither file
contains any `sorry`, so no declaration in either can depend on `sorryAx`
whatever the wider tally; but the 59 are what was checked one by one.

**The other six files.** Same procedure, in dependency order. They are far
cheaper than `SubDittertK3.lean`; none needs a multi-gigabyte guard.

```
lake env lean SubDittertLinear.lean      2>&1 | grep "depends on axioms"
lake env lean SubDittertUniversal.lean   2>&1 | grep "depends on axioms"
lake env lean SubDittertK2.lean          2>&1 | grep "depends on axioms"
lake env lean SubDittertM.lean           2>&1 | grep "depends on axioms"
lake env lean NewtonInequalities.lean    2>&1 | grep "depends on axioms"
lake env lean SubDittertMaclaurin.lean   2>&1 | grep "depends on axioms"
lake env lean NewtonCrosscheck.lean      2>&1 | grep "depends on axioms"
```

Expect 37, 21, 17, 13, 33, 6 and 12 lines. **Hazard: the stale olean.**
Elaborating a downstream file against a `.lake/build` olean that predates its
source reports `unknown identifier` and *false* `sorryAx` on correct theorems.
Rebuild the dependency first. If you compile a private olean into a scratch
directory instead, **prepend** it to `LEAN_PATH`, never append — once anyone has
run `lake build`, an appended scratch directory loses to the stale build-tree
copy.

### 6a. The two verifiers behind the new Lean proof — RUN LIVE

```
python3 verify_H_identity.py
python3 verify_H_decomp.py
```

Both need `sympy` (project venv, not the system `python3`). **RUN LIVE, both
`all checks passed: True`.** `verify_H_identity.py` checks the local-to-global
dictionary against the assembled Gram at n = 4, 5, 6 at three corners, then the
whole certificate identity as an identity of rational functions of n by full
coefficient comparison — no sampling in that part. `verify_H_decomp.py` checks
the centred decomposition exactly over Q at n = 4, 5, 6, then the seven bridge
constants: `pivotA1..pivotD` equal the corresponding block minors times
1, 2, 4, 2, 1, 4, 1, each confirmed as an identity of rational functions, with a
mutation control (constant 5 for `pivotA3`) correctly rejected.

## 7. `verify_objPoly.py` — cross-validating the new Lean `objPoly` — RUN LIVE

```
cd ../leanproj
python3 verify_objPoly.py
```

**RUN LIVE, 0.2 s.** Checks the Lean definition of `objPoly` (transcribed
into Python by hand in the script, so this is a hand-transcription check, not
an automated Lean-to-Python bridge) against `verify_general.py`'s
from-the-1992-definition objective, at three random rational points for each
of $n=4,5,6,7$ (12 checks), at $J_n/n$ where the value must vanish (4
checks), and one mutation control. All 17 checks: `True`. `ALL OK: True`.

## 7a. The two graded verifiers — Theorems G, H and I — RUN LIVE

The 2026-07-30 merge made `paper_b.typ` the single sub-Dittert paper: it now
also carries Theorem G (the Tverberg–Friedland stability theorem), Theorem H
($k = 4$, every $n \ge 10$) and Theorem I (threshold insensitivity), each
graded by support layer. Two further exact verifiers came with them. **Both
parse the merged paper itself** — the k = 4 sensitivity table, and the
stability part's displayed audit counts — so they must run from a tree that
has `results/paper_b.typ`, with `sub-dittert/` as the working directory.

**Theorem G.** `graded_verify_stability.py` is standalone: standard library
only, no imports from the directory. V1–V11 verify the layer identity, the
core expansions, the four slice facts, every one-sided estimate with its
slack ratio, the per-layer bounds, the closed forms and thresholds, the
theorem end to end at every covered cell, the (3,3) counterexample and the
sharpness proposition — all over exact rationals. V12 verifies the paper's
formalisation-scope claims against the Lean sources **at the pinned
commits** (`git show`, never the working tree): `StabilityK3.lean` and
`TverbergStability.lean` at `1507013`, `LayerIdentity.lean` at `27bda3f`,
`StabilityK4.lean` at `944b517` (the kernel-checked $(k=4, n\ge8)$ cell,
`stabilityAt_four`) and `SigmaFour.lean` at `365e44e`
(`sigma_four_centred`). It parses the paper's displayed audit counts — the
four "N of N declarations" pairs and the 121 total — back out of
`results/paper_b.typ` so displayed and measured cannot drift.

```
GUARD_MEM=6G GUARD_CPUS=200% GUARD_THREADS=2 ../guard.sh \
    python3 -u graded_verify_stability.py
```

**RUN LIVE 2026-07-30: 5.9 s, TOTAL FAILURES: 0, ALL CHECKS PASS**, against
the merged paper with the k = 4 cell upgraded. `--mutate` reruns the
mutation controls alone — **RUN LIVE: ALL CONTROLS FIRE**. Logs:
`results/graded_verify_stability.log`, `results/graded_verify_mutate.log`.

V12 needs a repository history containing the four pinned commits. From a
tree without them (a public extract's history differs), run with
`--no-lean`: the log then **records** that the formalisation-scope claims
went unchecked in that run instead of passing them quietly — the verifier's
own designed behaviour, stated in the paper.

**Theorems H and I.** `graded_verify_k4.py` recomputes every displayed
quantity of the paper's k = 4 part over $\mathbb{Q}$ — the expansion and the
exactly-zero d = 2 cross part, the end-to-end identity against the 1992
functional, the five cross-term reductions against brute force, the merge on
both signs of $\sum z^3$, the four collar facts, every budget line — and
parses the ten-row sensitivity table out of `results/paper_b.typ`,
recomputing every row and the flat-at-10 band. Four mutation controls, each
with a separating witness. Unlike the stability script it imports the
instrument modules it declares: `graded_assembly_k4.py`, `graded_layers.py`,
`graded_lemmaB.py`, `graded_y_bounds.py`, `pincer_line.py`,
`pincer_onesided.py` — that list is the whole transitive closure, and those
six files must ship wherever the verifier does.

```
GUARD_MEM=8G GUARD_CPUS=250% GUARD_THREADS=2 ../guard.sh \
    python3 -u graded_verify_k4.py
```

**RUN LIVE 2026-07-30: 4.9 s, TOTAL FAILURES: 0, ALL CHECKS PASS**, log
line "parsed 10 rows" confirming the paper coupling. Log:
`results/graded_verify_k4.log`.

**Superseded drafts.** The stand-alone drafts `graded_k4_paper.md` and
`graded_stability_lemma.md` are superseded by the merged paper and carry
headers saying so; the verifiers no longer read them. Whether the superseded
drafts ship publicly is a manifest decision — nothing in this kit depends on
them.

## 8. Compiling the paper itself

```
cd ../sub-dittert/results
typst compile paper_b.typ
```

Tested with `typst 0.15.1`. Produces `paper_b.pdf`, **38 pages**, compiles
clean. (Earlier notes here said 15, 16, then 20. The paper grew to 20 on
2026-07-29 when Theorems C–F were added and the fixed-dimension anchors were
demoted out of theorem status to match `LEAN-COVERAGE.md`; it grew to 38 on
2026-07-30 when the stability part (Theorem G), the k = 4 part (Theorems H
and I) and the per-cell anchor records at $(k=4, 5 \le n \le 9)$ were merged
in, making it the single sub-Dittert paper. The title changed in the same
pass.)

## 9. Search record

Not a verifying computation — a literature/priority check — but recorded here
because the paper's §2 rests on it and the paper itself no longer narrates how
the checks were made.

**Citation indexes.** Cheon–Hwang 1992 (the paper's [1]) shows three
references in Crossref and five citing papers in Semantic Scholar. The paper
quotes the larger figure, five, and enumerates all five; the Crossref
undercount is an indexing artefact, not a disagreement about the literature.
The five are Cheon–Wanless 2012 [6], Cheon–Wanless 2007 [7], the Cheon–Wanless
survey [5], Cheon–Yoon 2006 and Cheon 1993 (both [12]).

**Code hosts.** For a computer-assisted proof the code host is effectively the
venue, so a literature-only sweep can return an empty result confidently and
wrongly: three of the repositories in the paper's §2.1 table have no arXiv
entry at all. Queries run for the generalisation itself: `subdittert`,
`sub-dittert`, `subpermanent` and `cheon-hwang` on GitHub — no repositories;
GitLab, Zenodo, OSF and arXiv likewise returned nothing on the topic. Run once
at the start of this work and re-run immediately before write-up.

**Repository state.** See `kit/metadata.md`'s "Interim competitor probe"
section for the exact `gh` commands, the last-push timestamps, and the
verbatim re-fetch of the `pedromnasc` scope disclaimer that the paper quotes
in §2.2.

## 9a. Ship-day checklist

- [ ] Re-run the code-host sweep above. The paper's §2 records that the $k=n$
      endpoint moved three times in one week in July 2026, so the "first
      resolved case with $2<k<n$" claim is the most perishable statement in
      the paper. It attaches to Theorem A; Theorem H's extension of the
      resolved range is explicitly subordinate to its written-proof +
      exact-verifier grade, and the $(5,4)$ anchor is not stated as a
      theorem. `metadata.md`'s interim probe is a same-day sanity check,
      not this sweep.
- [ ] Re-check the four repositories of the paper's [11] for new commits and
      for scope changes to their READMEs; update the access date in [11] if
      the sweep is re-run.
- [ ] Re-check whether arXiv:2606.01531 (Pang) or arXiv:2607.19439 (Kafidov)
      has acquired a DOI or a published version; the paper describes both as
      unrefereed preprints.
- [ ] Confirm the §2.1 table caption date still matches the date of the last
      sweep.
- [ ] Run the Theorem G sweep alongside the Cheon–Hwang one: the paper
      claims the first stability form of the Tverberg–Friedland theorem
      (machine-checked half scoped to k = 2, 3, 4). Terms: "Tverberg",
      "Friedland", "stability", "subpermanent", "permanent stability",
      across the literature indexes AND the code hosts.
- [ ] Re-check the per-cell anchor table at (k = 4, 5 <= n <= 9): any cell
      upgraded after the paper's date must be re-graded in the table, and
      the k = 4 claim restated if all five reach exact-verifier grade.

## 10. What none of the above establishes

- That the certificates were correctly *produced* by the design pipeline —
  only that the certificates as given satisfy the stated identities and
  positivity requirements.
- Anything about $n=25$'s positive-definiteness specifically (§3 above), or
  the $(5,4)$ anchor's live re-verification (§5 above) — both cited from
  stored artefacts rather than reproduced in this pass.
- That the block-diagonalisation of the paper's §6.2 (Bose–Mesner algebra,
  $S_{n-1}$ representation theory) is correct as an *equivalence*. Lean proves
  semidefiniteness of both Gram families by an explicit change of coordinates
  and completions of squares, which is the direction the theorem needs; the
  spectral statements of §6.2 — the eigenvalues with their multiplicities, and
  the converse direction — are not formalised. The paper's §9.5 says so.
- That the priority/competitor landscape is unchanged beyond what the §9
  search record and `metadata.md`'s interim probe cover. The binding
  pre-submission sweep is outstanding and is item 1 of §9a. The paper's §11
  states the priority claim and calls it perishable; it does not carry the
  re-run instruction, which lives here.

## 11. File manifest

Paths are relative to `problems/permanents/sub-dittert/` unless marked
otherwise. This is the list the paper's "Data availability" section points to.

### The uniform certificate (Theorem A)

| file | contents |
|---|---|
| `results/general_k3_certificate.txt` | the nineteen certificate variables as exact rational functions of $n$ |
| `general_k3.py` | the closed-form constraint system in $n$; solve over $\mathbb{Q}(n)$ |
| `certificate.py` | builds the certificate and re-runs the full Sturm verdict |
| `blocks.py` | closed-form block-diagonalisation of both Grams, any $n$ |
| `recession.py` | recession cone and lineality space, derived over $\mathbb{Q}(n)$ |
| `essential.py` | the four-dimensional essential slice and the gauge |
| `adapted.py` | the sliver-adapted coordinates; $z$ solved exactly over $\mathbb{Q}(n)$ |
| `sturm.py` | exact Sturm decision of positivity on $n \ge 4$ |
| `expand.py`, `hessian.py` | exact objective, gradient, Hessian, exact characteristic polynomial |
| `validate.py` | five correctness tests on the objective, including the $k = n$ control |

### Verification

| file | contents |
|---|---|
| `verify_general.py` | independent verification over $\mathbb{Q}$; positive and negative controls |
| `verify_modp.py` | the identity in $\mathbb{F}_p$ at large $n$ |
| `stability_check.py` | both sides of the stability bound exactly over $\mathbb{Q}$ at $n = 4, 5, 6$; standard library only |
| `results/verify_subdittert.py` | standalone verifier for the fixed-dimension certificates, standard library only, no shared code |
| `results/*.json` | the fixed-dimension certificates as exact rational data |

### The design pipeline, and the branches that failed

| file | contents |
|---|---|
| `sos.py`, `exactsd.py`, `run.py`, `export.py` | reduced SDP, exact rebuild and rounding, driver, JSON export |
| `design_lp.py`, `design_sdp.py`, `search_free.py`, `curve.py`, `fit_curve.py`, `exact_design.py` | the failed design branches; the paper's §6.5 is only checkable against them |

### The uniform decomposition and band two (Theorems C–D, and §10)

| file | contents |
|---|---|
| `allk_universal.py` | the universal identity and its coefficient rule, checked exactly over $\mathbb{Q}$ outside Lean; the even-$k$ mixed-degree witnesses |
| `allk_band.py`, `allk_reduction.py`, `allk_blockmap.py` | the band law and the per-band reduction |
| `allk_loci.py`, `allk_scaling.py`, `allk_routes.py` | the route kills, each with an exact rational witness |
| `k4_pincert.py`, `k4_pinrank.py`, `k4_pinretest.py` | the $k = 4$ pin sweep decided over $\mathbb{Q}$ at $n = 5, 6, 7$ |
| `results/witness/` | one JSON per (dimension, configuration): Farkas generators and their value, or the rational point and its least $LDL$ pivot |
| `results/verify_pinretest.py` | standalone verifier for those witnesses; own elimination, own $LDL^\mathsf{T}$, own rank check, `--mutate` controls |
| `NOTES-ALLK.md` §10, `NOTES.md` §6b.37–6b.43 | the working record behind §10 of the paper (private tree only; the `NOTES*.md` files are not part of the public extract) |

### The stability and k = 4 parts (Theorems G, H, I)

| file | contents |
|---|---|
| `graded_verify_stability.py` | standalone verifier for Theorem G (standard library only); V12 reads the Lean sources at the pinned commits and the paper's own displayed counts |
| `graded_verify_k4.py` | verifier for Theorems H and I; parses the paper's sensitivity table out of `results/paper_b.typ` |
| `graded_assembly_k4.py`, `graded_layers.py`, `graded_lemmaB.py`, `graded_y_bounds.py`, `pincer_line.py`, `pincer_onesided.py` | the instrument modules `graded_verify_k4.py` imports — its whole transitive closure |
| `results/graded_verify_stability.log`, `results/graded_verify_mutate.log`, `results/graded_verify_k4.log` | the stored runs behind §7a |

### Lean (`problems/permanents/leanproj/`)

The eight files and their audit counts are in §6 above. Alongside them:

| file | contents |
|---|---|
| `verify_objPoly.py` | the Lean objective against the from-the-1992-definition objective, exactly over $\mathbb{Q}$ |
| `verify_H_identity.py` | the coefficients of the Positivstellensatz identity, as rational functions of $n$, by full coefficient comparison |
| `verify_H_decomp.py` | the centred decomposition and the seven bridge constants |
| `problems/permanents/LEAN-COVERAGE.md` | the whole-tree audit record and the support-layer ledger |
