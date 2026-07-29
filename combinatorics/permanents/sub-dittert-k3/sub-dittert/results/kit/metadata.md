# Submission metadata

## Title

The Cheon–Hwang Sub-Dittert Conjecture at k = 3, for Every Dimension

Subtitle: with a decomposition of the deficit uniform in n and k

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
  itself — see the paper's §6.3 and §6.4, which diagnose the feasible set's
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
  theorem provers. Every result the paper states as a theorem is proved in
  Lean 4 and cited by declaration name, and two of them (Newton's inequalities
  and Maclaurin's inequality, absent from Mathlib v4.14.0) are contributed as
  formalisations of classical mathematics rather than as new results.

## Keywords

permanent, Dittert's conjecture, Cheon–Hwang conjecture, doubly stochastic
matrix, Positivstellensatz certificate, semidefinite programming, symmetry
reduction, Bose–Mesner algebra, Sturm sequence, elementary symmetric function,
Newton's inequalities, Maclaurin's inequality, computer-assisted proof, Lean 4,
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

## Timing note — the priority claim is the most perishable in this series

The paper's own §2.1 records that the $k=n$ (Dittert) endpoint moved
publicly and repeatedly within a single week in July 2026, three of the
claims in public repositories with no corresponding preprint, and its §11
calls the "first resolved case with $2<k<n$" claim perishable. Since the
2026-07-29 rewrite that claim attaches to Theorem A alone — the five
fixed-dimension anchors, including $(5,4)$, are no longer stated as theorems,
because they have no Lean support — so the sweep needs to clear the line
$k = 3$ for $n \ge 4$, not the single pair $(5,4)$ as well. The search
behind that claim must be re-run before the draft is submitted anywhere; the
instruction and the query list live in `README-reproduce.md` §9 and §9a, not
in the paper. This kit's own interim competitor check (below) is not a
substitute for that re-run; it is a narrower, same-day sanity check.

### Interim competitor probe, run for this kit-readiness pass — NOT the ship-day check

Run via authenticated `gh` (rate limit healthy throughout: core API
4998/5000 remaining before, no throttling observed). `gh search repos` full-
text search under-indexes recently created repositories — it missed
`pedromnasc/dittert-conjecture-proof` entirely for the query `pedromnasc`, so
results below use the `gh api users/<user>/repos` and `gh api repos/<owner>/
<name>` endpoints directly, which do not depend on search indexing.

- `pedromnasc/dittert-conjecture-proof`: last push 2026-07-26T13:41:47Z, no
  update since. Its `subdittert/README.md` still contains, verbatim, the
  scope disclaimer the paper quotes in §2.2 ("The endpoint `k=n` is
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
