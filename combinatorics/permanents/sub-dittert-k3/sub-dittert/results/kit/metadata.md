# Submission metadata

> **Updated 2026-07-30 for the 12-page rewrite.** The paper was rewritten from
> 38 pages to 12 around a single thesis (deg F = k, not n) and renumbered.
> Section references in this file and in `README-reproduce.md` point at the NEW
> numbering: §1 the conjecture, the decomposition and the map of methods; §2 the
> certificate route at k = 3; §3 the local method (3.1 confinement, 3.2 the
> Tverberg–Friedland stability theorem, 3.3 the collar assembly at k = 4); §4
> the small cells at k = 4 and the gap; §5 what is machine-checked and what is
> not; §6 data availability. Theorem letters A–H, Corollary B, Lemmas S1–S3,
> Propositions S4–S6 and every Lean declaration name are unchanged. The k = 4
> sensitivity table moved to `sensitivity-k4.md` and `graded_verify_k4.py` was
> re-pointed at it in lockstep.

## Title

The Cheon–Hwang Sub-Dittert Conjecture at k = 3 and k = 4

Subtitle: with a stability form of the Tverberg–Friedland theorem and a
decomposition of the deficit uniform in n and k

## Author

D C P Revere, dcprevere@gmail.com. Unaffiliated; no institution line.

## MSC 2020 classification codes

- **15A15** (primary) — Determinants, permanents, other special matrix
  functions. Dittert's conjecture and its Cheon–Hwang generalisation are
  15A15 subject matter throughout, and the endpoint case (Dittert itself) is
  the field's standard reference point.
- **90C22** (primary) — Semidefinite programming. The proof method is
  genuinely an SDP pipeline: a symmetry-reduced Positivstellensatz ansatz,
  solved once symbolically over $\mathbb{Q}(n)$ after a numerical design
  stage, with the tight direction eliminated exactly rather than fitted. This
  is as central to the paper's contribution as the permanent-theory result
  itself — see the paper's §2.3, which diagnoses the feasible set's
  geometry (a four-dimensional lineality space, then a sliver of width
  $O(n^{-2})$) and state the transferable design rule: identify the tight
  direction and eliminate it symbolically, fit only the slack ones.
- **20C30** (secondary) — Representations of finite symmetric groups.
  Positive definiteness of the two Gram matrices is reduced in closed form to
  ten rational functions of $n$ via the Bose–Mesner algebra of the rook's
  graph and the representation theory of $S_{n-1}$; this block-diagonalisation
  is not a side computation but the mechanism that makes a single symbolic
  solve valid at every $n$ at once.
- **68W30** (secondary) — Symbolic and algebraic computation. Covers the
  Sturm-sequence positivity decisions and the exact rational rounding and
  verification pipeline.
- **68V20** (secondary) — Formalisation of mathematics in connection with
  theorem provers. The k = 3 line and the k = 2, 3, 4 stability cells are
  proved in Lean 4 and cited by declaration name at pinned commits, and two results
  (Newton's inequalities and Maclaurin's inequality, absent from Mathlib
  v4.14.0) are contributed as formalisations of classical mathematics rather
  than as new results. The paper grades every claim by support layer
  (kernel-checked / exact-verifier / verified computation), and two of its
  exact verifiers parse the paper's own displayed numbers so displayed and
  checked cannot drift.
- **15B51** (secondary) — Stochastic matrices. The Tverberg–Friedland
  stability theorem (Theorem G) lives on the doubly stochastic polytope, and
  the k = 4 argument runs on a collar around it.

## Keywords

permanent, subpermanent sum, Dittert's conjecture, Cheon–Hwang conjecture,
doubly stochastic matrix, Tverberg–Friedland theorem, stability inequality,
Positivstellensatz certificate, semidefinite programming, symmetry reduction,
Bose–Mesner algebra, Sturm sequence, elementary symmetric function, Newton's
inequalities, Maclaurin's inequality, computer-assisted proof, Lean 4,
formalised mathematics, exact rational verification

## Suggested venues

1. **Linear Algebra and its Applications (LAA).** This is the exact journal
   that carries the Cheon–Hwang paper itself (LAA 165, 1992) — the source of
   the conjecture this paper settles at $k=3$ — as well as Hwang's 1987
   theorem at $n=3$ that this paper reproves by certificate and the
   Cheon–Wanless survey that reports the $k=n$ endpoint's history. A paper
   settling a named conjecture is a natural submission to the journal that
   posed it, and three of the paper's own bibliography entries are LAA
   papers.
2. **SIAM Journal on Applied Algebra and Geometry (SIAGA).** The paper's most
   exportable contribution is arguably methodological rather than
   permanent-theoretic: a general principle for designing a symmetry-reduced
   Positivstellensatz certificate that is valid at every dimension $n$ at
   once, including the specific diagnosis that unboundedness alone does not
   explain a numerical design failure and that the real obstruction can be a
   sliver of width $O(n^{-2})$ requiring exact elimination rather than curve
   fitting. SIAGA is a venue built for exactly this kind of exact
   algebraic-geometry-meets-optimisation result, and would put the paper in
   front of readers who would use the technique on a different family of
   certificates, not only readers tracking the Cheon–Wanless survey.

## arXiv category

- **Primary: math.CO** (Combinatorics) — permanents and Dittert-type
  inequalities are standard math.CO subject matter, matching where the
  Cheon–Wanless survey and the endpoint literature sit.
- **Cross-list: math.OC** (Optimization and Control) — appropriate given the
  proof method is fundamentally a semidefinite program with a
  symmetry-reduction and exact-elimination design step; this is at least as
  load-bearing here as in the minc-permanents paper's SDP cross-list.
- **Cross-list: math.LO** (Logic) or **cs.LO** — optional, and only if the
  formalisation is to be surfaced. Every stated theorem is Lean-checked, and
  the Newton/Maclaurin file is a Mathlib PR candidate in its own right.

## Timing note — the priority claims are the most perishable in this series

The paper's own §1.4 records that the $k=n$ (Dittert) endpoint moved
publicly and repeatedly within a single week in July 2026, three of the
claims in public repositories with no corresponding preprint — and, taken
with the two preprints, one repository (`pedromnasc`) now presents an
unrefereed assembly claiming Dittert in full. The paper takes no view on its
correctness and keeps its own priority claims narrowed to what the Lean
development and the exact verifiers carry, at each part's stated grade.

Since the 2026-07-30 merge the paper carries two priority claims and one
subordinate one: (1) Theorem A is the first resolved case of Cheon–Hwang
with $2<k<n$ — attaches to the kernel-checked $k=3$ line, so the sweep needs
to clear $k = 3$ for $n \ge 4$; (2) Theorem G is claimed as the first
stability form of the Tverberg–Friedland theorem, with the machine-checked
half of that claim scoped to the $k = 2, 3, 4$ cells (the paper's stability
addendum states the scope; sweep terms should include "Tverberg",
"Friedland", "stability", "subpermanent"); (3) Theorem H extends the
resolved range at written-proof + exact-verifier grade, and its claim is
explicitly subordinate to its grade. The searches behind all of these must
be re-run before the draft is submitted anywhere; the instruction and the
query list live in `README-reproduce.md` §9 and §9a, not in the paper. This
kit's own interim competitor check (below) is not a substitute for that
re-run; it is a narrower, same-day sanity check.

### Interim competitor probe, run for this kit-readiness pass — NOT the ship-day check

Run via authenticated `gh` (rate limit healthy throughout: core API
4998/5000 remaining before, no throttling observed). `gh search repos` full-
text search under-indexes recently created repositories — it missed
`pedromnasc/dittert-conjecture-proof` entirely for the query `pedromnasc`, so
results below use the `gh api users/<user>/repos` and `gh api repos/<owner>/
<name>` endpoints directly, which do not depend on search indexing.

- `pedromnasc/dittert-conjecture-proof`: last push 2026-07-26T13:41:47Z, no
  update since. Its `subdittert/README.md` still contains, verbatim, the
  scope disclaimer the paper quotes in §1.4 ("The endpoint `k=n` is
  Dittert's problem. The cases `k<=2` are historically known. This package
  does **not** claim the unresolved intermediate cases.") — fetched fresh
  and diffed against the paper's quotation; unchanged.
- `123ljh0bot/Dittert_Conjecture_in_Dimension_4`: last push
  2026-07-26T09:53:43Z, no update since.
- `lueluelue2006/dittert-conjecture-draft` and `.../dittert-n7-extension`
  (the account the paper's bibliography attributes to "Hongyuan Lu"): both
  last pushed 2026-07-25T03:40Z, no update since.
- A broad `gh search repos "dittert"` sorted by most-recently-updated
  surfaces no repository beyond these three accounts and one unrelated hit
  (`HelenaDittert.github.io`, a personal page, last touched 2021).
- No rate-limiting was encountered at any point (`gh api rate_limit`
  checked before and after); nothing here should be read as "checked and
  clear" beyond what a healthy, unthrottled query set actually covers —
  GitHub code search (as opposed to repository search) was not attempted,
  matching the same residual hole in the sweep recorded in
  `README-reproduce.md` §9.

**Verdict: no new public activity on this line since the paper's own dates.**
This is good news for the priority claim but is explicitly an interim,
same-day check, not the binding pre-submission sweep.
