#set page(paper: "a4", margin: (x: 2.0cm, y: 2.05cm), numbering: "1")
#set text(font: "New Computer Modern", size: 9.6pt)
#set par(justify: true, leading: 0.58em)
#set heading(numbering: "1.1")
#show heading.where(level: 1): it => block(above: 1.4em, below: 0.6em)[
  #text(11pt, weight: "bold")[#it]
]
#show heading.where(level: 2): it => block(above: 1.15em, below: 0.5em)[
  #text(10pt, style: "italic", weight: "regular")[#it]
]

// Inline declaration names sit flush with the prose: RELATIVE sizing, so a
// name scales with whatever context it sits in (body, a grade line, a table
// cell), in a mono whose x-height matches the serif face, and no tinted box.
#show raw: set text(font: "Nimbus Mono PS")
#show raw.where(block: false): it => text(size: 0.88em, it)
#show raw.where(block: true): it => block(
  width: 100%, inset: 6pt, stroke: 0.4pt + luma(180), text(size: 8.2pt, it)
)

#set math.equation(numbering: "(1)")
#show math.equation.where(block: true): set block(above: 0.7em, below: 0.7em)
#let per = math.op("per")
#let directsum = math.class("binary", "⊕")
#let kron = math.class("binary", "⊗")

#show ref: it => {
  let el = it.element
  if el != none and el.func() == heading {
    link(el.location(),
      [§#numbering(el.numbering, ..counter(heading).at(el.location()))])
  } else if el != none and el.func() == math.equation {
    // The equation numbering already carries its own parentheses.
    link(el.location(),
      numbering(el.numbering, ..counter(math.equation).at(el.location())))
  } else { it }
}

// One statement style throughout, distinguished only by the weight of the
// rule: a heavier one for the named theorems, a hairline for everything else.
// No fills, no rounded corners.
#let stmt(rule, body) = block(
  width: 100%, above: 1.0em, below: 1.0em,
  stroke: (left: rule), inset: (left: 9pt, top: 3pt, bottom: 3pt),
)[#body]
#let keybox(body) = stmt(1.4pt + luma(70), body)
#let claimbox(body) = stmt(0.5pt + luma(160), body)

// The support-layer line under a statement: small, ragged, and set in grey so
// that grading metadata never competes with the mathematics.
#let leanline(body) = block(width: 100%, above: 0.5em)[
  #set par(justify: false)
  #text(8.2pt, fill: luma(75))[#body]
]

// Booktabs: horizontal rules only, none of the enclosing grid.
#let tstroke = (x, y) => (
  top: if y == 0 { 0.7pt + luma(40) } else if y == 1 { 0.4pt + luma(130) }
       else { none },
  bottom: none, left: none, right: none,
)

#align(center)[
  #v(0.2em)
  #text(15pt)[The Cheon–Hwang Sub-Dittert Conjecture at $k = 3$ and $k = 4$]
  #v(0.55em)
  #text(10pt, style: "italic")[
    with a stability form of the Tverberg–Friedland theorem\
    and a decomposition of the deficit uniform in $n$ and $k$
  ]
  #v(1.1em)
  #text(10.5pt)[D C P Revere]
  #v(0.25em)
  #text(9pt)[dcprevere\@gmail.com]
  #v(0.25em)
  #text(8.5pt, style: "italic")[Draft — 30 July 2026]
  #v(0.9em)
  #line(length: 38%, stroke: 0.4pt + luma(140))
]

#v(0.5em)

#block(inset: (x: 1.0cm))[
  #text(9pt)[
    *Abstract.* Cheon and Hwang conjectured in 1992 that
    $E_k (r) + E_k (c) - P_k (A) lt.eq 2 - k!\/n^k$ for every non-negative
    $n times n$ matrix of total sum $n$ and every $1 lt.eq k lt.eq n$, with
    equality only at $J_n\/n$; the endpoint $k = n$ is Dittert's conjecture,
    and the intermediate range $2 < k < n$ appears to have gone untouched.
    One structural fact organises what follows: the deficit has degree $k$,
    not $n$. Where $k$ is small enough that a fixed-degree Positivstellensatz
    ansatz still matches it, the symmetry-reduced programme has the _same_
    $12 times 19$ shape at every dimension and is solved once over $QQ(n)$;
    where it is not, only inequalities uniform in $n$ reach, and a local
    method takes over.

    On the first route we settle the line $k = 3$ for every $n gt.eq 4$ —
    the inequality, the equality case, and a quantitative strengthening
    $(2 - 6\/n^3) - Phi_3 (A) gt.eq theta_2 (n) norm(A - J_n\/n)_F^2$ with
    $theta_2$ an explicit rational function — by a single certificate whose
    nineteen coefficients are rational functions of $n$, its two
    $n^2 times n^2$ Gram matrices reduced in closed form to ten rational
    functions decided by Sturm sequences. This is machine-checked end to end
    (`subDittert_k3_full`).

    The second route is local: confinement traps any violator in a collar of
    the Birkhoff polytope, a collar matrix splits orthogonally into a
    line-sum block and a doubly centred block, the centred block is governed
    by a _stability form of the Tverberg–Friedland theorem_ proved here, and
    the five cross terms between the blocks have exact reductions. That
    yields the Cheon–Hwang inequality at $k = 4$ for every $n gt.eq 10$ with
    its equality case. The stability theorem — that $sigma_k$ on the doubly
    stochastic polytope exceeds its minimum by at least
    $binom(n,k)^2 c(n,k) norm(A - J_n\/n)_F^2$, with $c$ optimal to within a
    factor two — is kernel-checked at $k = 2$, $k = 3$ and $k = 4$ over the
    whole range it states for each, and is of independent interest.
    Fixed-dimension certificates settle $(k=4, n=5,6,7)$, so on the line
    $k = 4$ exactly two cells remain open, $n = 8$ and $n = 9$. Every result
    is stated with the layer it rests on — kernel-checked in Lean 4 at a
    pinned commit, exact rational verifier, or verified computation — and the
    grading is part of the claim.
  ]
]

#v(0.5em)

= The conjecture, and the shape of the problem

Let $K_n = { A in RR^(n times n) : A_(i j) gt.eq 0, sum_(i,j) A_(i j) = n }$,
and for $A in K_n$ let $r$ and $c$ be its vectors of row and column sums.
Write $sigma_k (A)$ for the sum of the permanents of all $k times k$
submatrices of $A$ — rows chosen from one $k$-subset, columns from another,
independently — and put
$ E_k (v) = frac(e_k (v), binom(n,k)), quad
  P_k (A) = frac(sigma_k (A), binom(n,k)^2), quad
  gamma(n,k) = frac(k!, n^k), quad
  Phi_k (A) = E_k (r) + E_k (c) - P_k (A), $
with $e_k$ the elementary symmetric function.

#block(fill: luma(250), inset: 8pt, radius: 3pt, width: 100%)[
  *The conjecture (Cheon and Hwang [1], 1992).* For every $A in K_n$ and every
  $1 lt.eq k lt.eq n$, $Phi_k (A) lt.eq 2 - gamma(n,k)$, with equality only
  at $A = J_n\/n$.
]

At $k = n$ one has $sigma_n = per$ and $E_n (v) = product_i v_i$, so the
statement is $product_i r_i + product_j c_j - per(A) lt.eq 2 - n!\/n^n$:
_Dittert's conjecture_ verbatim, Conjecture 28 of the Cheon–Wanless survey
[5]. At $k = 1$ the inequality is an identity _on $K_n$_ — not on all of
$RR^(n times n)$ — since the difference is a constant multiple of
$sum_(i j) A_(i j) - n$; a test that treats it as a formal identity fails.
The cases $k lt.eq 2$ for every $n$, and every $k$ at $n lt.eq 3$, are known.
The interesting range is $2 < k < n$, and it is that range which appears to
have gone untouched (@sec-prior).

== One decomposition, exact and uniform in $n$ and $k$

Everything below is read off a single identity.

#keybox[
  *Theorem C (the deficit, decomposed uniformly in $n$ and $k$).* Write
  $A = J_n\/n + b$, let $R$ and $C$ be the row and column sums of $b$, and put
  $ s_d = frac([k]_d, [n]_d), quad t_d = s_d^2 dot.c frac((k-d)!, n^(k-d)) $
  with $[x]_d$ the falling factorial. Then for every $1 lt.eq k lt.eq n$,
  identically in $b$,
  $ (2 - gamma(n,k)) - Phi_k (A)
    = sum_(d=1)^k [ t_d dot.c sigma_d (b) - s_d dot.c (e_d (R) + e_d (C)) ]. $ <eq-universal>
  #leanline[Kernel-checked: `SubDittertUniversal.universal_identity`.]
]

@eq-universal is elementary and no novelty is claimed for it: it is the
$sigma_k$ analogue of $per(A + x J_n) = sum_j x^(n-j) (n-j)! thin sigma_j (A)$
combined with $e_k (bold(1) + R) = sum_d binom(n-d, k-d) e_d (R)$. Its role is
to make every $k$-dependence explicit and finite, so that facts looking
separate at separate $k$ become one identity read at one degree; the absence
of a $d = 0$ term is why the constant $2 - gamma(n,k)$ is exactly right at
every $n$ and $k$ at once. One reading is used throughout: the coefficient of
a degree-$d$ monomial takes one of three values — $-2 s_d + t_d$ if the cells
form a partial permutation, $-s_d$ if they have distinct rows or distinct
columns but not both, and $0$ otherwise.

== The organising fact, and the map of the paper <sec-map>

Write $F(b) = (2 - gamma(n,k)) - Phi_k (A)$ in the centred coordinates
$b = A - J_n\/n$. Then $deg F = k$, _not_ $n$, and that is the fact deciding
which method reaches where. A Positivstellensatz ansatz with a Gram basis of
degree $e$ produces terms of degree $2e + 1$, so it matches $F$ exactly when
$e = ceil((k-1)\/2)$, and the symmetry-reduced programme then has a shape
depending on $k$ alone. At $k = 3$ that shape is $12$ equations in $19$
unknowns at _every_ dimension. At $k = 4$ the basis degree steps to $e = 2$,
the programme grows to $440$ unknowns, and no family in $n$ is known for it.

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, left),
    stroke: tstroke,
    inset: 5pt,
    table.header([*region*], [*method, and why it is the one that reaches*],
      [*what it yields*]),
    [$k = 3$, every $n gt.eq 4$],
    [one certificate over $QQ(n)$: at $e = 1$ the reduced programme is
     $12 times 19$ at every dimension, so a single symbolic solve covers all
     $n$],
    [Theorem A — inequality, equality case _and_ a stability bound;
     kernel-checked],
    [$k = 4$, every $n gt.eq 10$],
    [the local method: confine, split, apply stability on the slice,
     assemble on the collar. At $k = 4$ no certificate family in $n$ exists,
     and only $n$-uniform inequalities reach],
    [Theorem H — inequality and equality case; exact-verifier grade],
    [$k = 4$, $n = 5, 6, 7$],
    [exact per-cell certificates: at small $n$ an exact solve finishes, and
     it gives the sharpest statement available per cell],
    [anchor grade; the cells $(k=4, n=8)$ and $(k=4, n=9)$ remain open],
    table.hline(stroke: 0.7pt + luma(40)),
  ),
  caption: [Which method is used where, and why. The stability theorem
    (Theorem G) is the shared engine of the middle row.]
)

The three rows are not three papers. Both methods run on @eq-universal — the
certificate is a Positivstellensatz for the whole of $F$, the local method
bounds @eq-universal layer by layer — and Theorem G, the middle row's engine,
is a statement about the same $sigma_k$ on the doubly stochastic slice.

== Results <sec-results>

#keybox[
  *Theorem A ($k = 3$, every $n gt.eq 4$).* For every $n gt.eq 4$ and every
  $A in K_n$,
  $ E_3 (r) + E_3 (c) - P_3 (A) lt.eq 2 - 6/n^3, $ <eq-thmA>
  with equality if and only if $A = J_n\/n$. More precisely, with
  $norm(dot.c)_F$ the Frobenius norm,
  $ (2 - 6/n^3) - [E_3 (r) + E_3 (c) - P_3 (A)]
      gt.eq theta_2 (n) dot.c norm(A - J_n\/n)_F^2, quad
    theta_2 (n) = frac(n^4 + 40 n^2 - 84 n + 40, n^5 (n-1)^3 (n-2)), $ <eq-thmA-stab>
  and $theta_2 (n) > 0$ for every $n gt.eq 4$.
  #leanline[Kernel-checked: `SubDittertK3.subDittert_k3_full`, all three
  parts in one theorem.]
]

The three statements are one: @eq-thmA-stab implies both the others, since
$theta_2 (n) > 0$ and $norm(A - J_n\/n)_F$ vanishes only at $J_n\/n$, while
$Phi_3 (J_n\/n) = 2 - 6\/n^3$ exactly. We state all three because the
quantitative form is what the certificate produces, and it is stronger than
the conjecture asks: the functional falls away from its maximum at least
quadratically in the distance to the maximiser, at an explicit rate not
claimed optimal (@sec-machine).

#claimbox[
  *Corollary B (two layers, stated as such).* With Hwang's theorem for
  Dittert at $n = 3$ [3], the case $k = 3$ holds with its equality case for
  every $n gt.eq 3$, and since $k = 3$ requires $n gt.eq 3$ no dimension is
  left open on that line.
  #leanline[_Not a single-layer result; do not cite it as one._ The range
  $n gt.eq 4$ is Theorem A and is kernel-checked; the case $n = 3$ is Hwang's
  refereed theorem of 1987 [3], which we do not reprove. The corollary's
  support is Lean _plus_ the published literature.]
]

#claimbox[
  *Theorem D ($k = 2$, every $n gt.eq 2$).* $Phi_2 (A) lt.eq 2 - 2\/n^2$ for
  every $A in K_n$. With $kappa = 2\/(n(n-1))$ the deficit is a manifest sum
  of squares on the hyperplane $sum_(i j) b_(i j) = 0$:
  $ (2 - 2\/n^2) - Phi_2 (A)
    = 1/2 [ kappa^2 norm(b)^2 + kappa (1 - kappa) (norm(R)^2 + norm(C)^2) ]. $ <eq-k2sos>
  #leanline[Kernel-checked: `SubDittertK2.subDittert_k2`. _The statement is
  classical_ (@sec-prior); the contributions are the derivation from
  @eq-universal and the machine-checked proof.]
]

Theorem D needs no Cauchy–Schwarz, no Gram matrix and no Maclaurin
inequality: @eq-k2sos falls out of @eq-universal at $k = 2$, both
coefficients being non-negative for $n gt.eq 2$ because $kappa lt.eq 1$
there. Its interest is as a control on the uniform machinery — the one case
where that machinery runs end to end against an independently known answer.
The same route does not reach $k = 3$, where the deficit is not a sum of
squares on the hyperplane.

The next two results are recalled rather than claimed; it is the
formalisation, not the mathematics, that is ours.

#claimbox[
  *Theorem E (confinement; Cheon and Wanless [6], Theorem 2.1, at $k = n$;
  transferred to all $k$).* Let $2 lt.eq k lt.eq n$ and $A in K_n$. Then
  $ frac(norm(r - bold(1))^2 + norm(c - bold(1))^2, n(n-1)) - gamma(n,k)
    lt.eq (2 - gamma(n,k)) - Phi_k (A), $
  so any $A$ violating the Cheon–Hwang bound satisfies
  $norm(r - bold(1))^2 + norm(c - bold(1))^2 lt.eq (n-1) k! \/ n^(k-1)$.
  #leanline[Kernel-checked: `SubDittertMaclaurin.theoremM'`, `confinement'`.]
]

#claimbox[
  *Theorem F (Newton; Maclaurin).* For every real-rooted real polynomial and
  every admissible index Newton's inequality holds; in vector form, for
  $v in RR^n$ and $1 lt.eq j lt.eq n-1$,
  $e_(j-1)(v) thin e_(j+1)(v) binom(n,j)^2
   lt.eq e_j (v)^2 binom(n,j-1) binom(n,j+1)$, with no positivity hypothesis.
  Consequently, for $v gt.eq 0$ with $sum_i v_i = n$ and $2 lt.eq k lt.eq n$,
  $E_k (v) lt.eq E_2 (v)$.
  #leanline[Kernel-checked: `NewtonIneq.newtonAt_all`, `newton_esymF`,
  `pnorm_le_two`. _Classical mathematics_; the contribution is the
  formalisation. Neither inequality is in Mathlib v4.14.0, whose
  `NewtonIdentities` carries Newton's _identities_ only.]
]

The remaining two results are the engine and the conclusion of the local
route. The first lives on the doubly stochastic polytope $Omega_n$ and is a
quantitative form of a theorem conjectured by Tverberg [17] and proved by
Friedland [18]: $sigma_k$ on $Omega_n$ attains its minimum only at the
barycentre, the case $k = n$ being the van der Waerden conjecture settled by
Egorychev [20] and Falikman [21]. Those theorems give strictness but no rate.

#keybox[
  *Theorem G (stability of the Tverberg–Friedland minimum).* Let
  $2 lt.eq k lt.eq 5$ and let $n$ satisfy
  $ n gt.eq 2 " at " k=2, quad n gt.eq 4 " at " k=3, quad
    n gt.eq 8 " at " k=4, quad n gt.eq 14 " at " k=5. $
  Then for every doubly stochastic $n times n$ matrix $A$,
  $ sigma_k (A) - binom(n,k)^2 frac(k!, n^k)
    gt.eq binom(n,k)^2 thin c(n,k) thin norm(A - J_n\/n)_F^2,
    quad c(n,k) = frac(k(k-1) thin k!, 4 n^k (n-1)^2). $ <eq-thmG>
  The constant is optimal to within a factor two (Proposition S5), and the
  cell $(k,n) = (3,3)$ is a genuine exception with an explicit witness.
  #leanline[_Kernel-checked_ at $(k=2$, every $n gt.eq 2)$ and $(k=3$, every
  $n gt.eq 4)$ — `stabilityAt_two`, `stabilityAt_three` in
  `StabilityK3.lean` at commit `1507013` — and at $(k=4$, every
  $n gt.eq 8)$ — `stabilityAt_four` in `StabilityK4.lean` at commit
  `944b517` — in each case over the whole range the theorem states for that
  $k$. _Written proofs plus the exact verifier `graded_verify_stability.py`_
  at $(k=5, n gt.eq 14)$: no `stabilityAt_five` exists. @sec-machine states
  the division and its two limits.]
]

#keybox[
  *Theorem H ($k = 4$, every $n gt.eq 10$).* For $k = 4$ and every
  $n gt.eq 10$, $Phi_4 (A) lt.eq 2 - 24\/n^4$ for every $A in K_n$, with
  equality only at $A = J_n\/n$.
  #leanline[_Not formalised._ Support: the written proofs of @sec-k4 plus the
  exact verifier `graded_verify_k4.py`, which recomputes every displayed
  quantity of that part over $QQ$ with no floating-point arithmetic in any
  decision.]
]

Between Theorem A's line and Theorem H's range sit the cells
$(k = 4, 5 lt.eq n lt.eq 9)$. Three are settled by fixed-dimension
certificates at anchor grade — $(k=4, n=5)$, $(k=4, n=6)$ and $(k=4, n=7)$ —
so the open cells on the line $k = 4$ are exactly $n = 8$ and $n = 9$.
@sec-cells records all five at the grade each has reached and states that gap
once.

== Support layers, and prior work <sec-prior>

Every result above is stated with the layer it rests on, because in this
corner of the literature the distinction has recently been expensive.
Theorems A and C–F are proved in Lean 4; Theorem G splits by cell as its
statement records; Theorem H is not formalised; the fixed-dimension
certificates of @sec-cells are exact rational data accepted by an independent
standalone verifier, and no theorem here depends on them. Nothing here is
refereed, including this paper — exact verification and machine checking are
different things from refereeing, and weaker ones. @sec-machine is the
precise record.

_The intermediate range has attracted almost nothing._ The Cheon–Hwang paper
[1] has five citing papers — [5], [6], [7] and the two of [12] — none of
which works on the generalisation, and to our knowledge neither the
literature nor any public code repository carries a result on the
intermediate range: the one adjacent package, inside a repository of [11],
explicitly disclaims the unresolved intermediate cases, and that disclaimer
is also the clearest available statement of the prior status of Theorem D.
The endpoint $k = n$ is not attacked here and its status is not this paper's
subject — one public unrefereed repository of [11] claims Dittert in full, on
which we take no view — and every priority claim made here is narrowed to
what the Lean development and the exact verifiers actually carry. Reference
[7] is paywalled and was not obtained; it is reported to settle
$n lt.eq 3$ for all $k$, and nothing here depends on it.

= The certificate route: $k = 3$, uniformly in $n$ <sec-cert>

== The objective, and the ansatz

A certificate for the wrong polynomial is worthless and looks identical to a
certificate for the right one, so $F$ is checked before anything else:
$sigma_k$ by two structurally different algorithms (enumeration of the
$binom(n,k)^2$ index pairs, against
$per(A + x J_n) = sum_j x^(n-j)(n-j)! sigma_j (A)$ in $QQ[x]$ with the
order-$n$ permanent by Ryser), and the polynomial built at $(n,k) = (4,4)$
compared coefficient by coefficient — 1040 monomials, zero differences —
against an independent pipeline for the $k = n$ case that already underlies
a verified certificate. One trap deserves naming, since the obvious check falls into it:
$2 - gamma(4,3) = 2 - gamma(4,4) = 61\/32$ and
$2 - gamma(5,4) = 2 - gamma(5,5) = 1226\/625$, so seeing the right _bound_ is
no evidence at all that the $k = 3$ code does what it claims. Whole
polynomials separate the cases; at $n = 4$ the two objectives disagree at
every one of their 1040 monomials.

In centred coordinates the ansatz is
$ F(b) = sigma_0 (b) + sum_p (1/n + b_p) thin sigma_p (b)
  + lambda(b) dot (sum_q b_q), $ <eq-ansatz>
where $sigma_0$ and every $sigma_p$ is a sum of squares and $lambda$ is free.
On $K_n$ the last term vanishes and every $1\/n + b_p = A_p gt.eq 0$, so the
right side is a sum of non-negative terms and $F gt.eq 0$ there, which is the
theorem. The shape is Putinar's [2], truncated at a fixed degree, but no
existence theorem is invoked and none applies: Putinar's needs strict
positivity, and $F$ vanishes at $J_n\/n$ in the relative interior of $K_n$ —
the representation is exhibited, not deduced. Sum-of-squares relaxations are
Lasserre's hierarchy [13] and block-diagonalising by a symmetry group is
Gatermann–Parrilo [14], both used in their plain forms; what is not taken
from that line is the coefficient field, since the programme is posed and
solved over $QQ(n)$, one symbolic solve whose output is a certificate for
every $n$ at once. Optimisation uniform in the dimension is itself an active
area [15].

_Why the degree closes._ At $k = 3$ a Gram basis of degree $1$ gives
$deg sigma lt.eq 2$ and $deg(sigma_p b_p) lt.eq 3 = deg F$, with no surplus
top band to cancel; the Gram matrices are $n^2 times n^2$. _Why rounding
works._ The standing obstruction to exact rational rounding is that a tight
bound forces a singular optimal Gram. Here the Hessian of $F$ at $J_n\/n$
restricted to $\{sum X = 0\}$ is positive definite — at $(n,k) = (4,3)$ its
characteristic polynomial there is $x (x - 1\/16)^9 (x - 29\/16)^6$ over
$QQ$, the multiplicities $(n-1)^2$ and $2(n-1)$ forced by Schur's lemma — so
centring at the extremiser and excluding the constant monomial removes the
only degenerate direction.

== The programme's shape is fixed in $n$

The problem is invariant under $(S_n times S_n) : ZZ_2$ acting by row
permutations, column permutations and transposition. Reducing @eq-ansatz by
that group leaves, at every $n$ alike, $12$ orbit constraint rows of rank
$11$ over $QQ(n)$, and $3 + 11 + 5 = 19$ unknowns ($sigma_0$, $sigma_11$ and
$lambda$); only the cone size $n^2$ grows. Nineteen unknowns and twelve
equations, at $n = 4$, $n = 5$, $n = 6$ and beyond. This is representation
stability, and here — unlike at $k = n$, where the same stability is undercut
by the growing degree — nothing counteracts it.

Both halves of the $12 times 19$ system are _derived_ as functions of $n$,
not interpolated; "no fit is used anywhere" is a stronger statement than "the
fit was validated". The coefficient in $F$ of an arbitrary monomial is the
$k = 3$ case of the three-value rule of @eq-universal, and the orbit sizes
come from orbit–stabiliser, every one a polynomial in $n$ of degree at most
$6$ because a multiset of at most three cells meets at most three rows and
three columns. Both were checked against the fully expanded objective at
$n = 4, 5, 6$ over the _whole_ coefficient vector, absent monomials included
— 969, 3276 and 9139 monomials, no mismatches — and the assembled system was
compared entry by entry with the one built by the original code path, which
shares no logic with it and which produced the already-verified fixed-$n$
certificates. Row-reducing over $QQ(n)$ gives rank $11$, one dependent row,
_consistent_, with an $8$-dimensional affine family of solutions: the linear
half of the certificate exists at every $n$ at once.

== Definiteness, and the design problem <sec-design>

What remains is to choose within that family so that both Gram matrices are
positive definite for every $n gt.eq 4$. Both are block-diagonalised _in
closed form_ — a numerical basis at one $n$ could not settle all $n$. The
$sigma_0$ Gram lies in the Bose–Mesner algebra of the rook's graph
$K_n square K_n$, so it has exactly three eigenvalues
$theta_0, theta_1, theta_2$, of multiplicities $1$, $2(n-1)$, $(n-1)^2$. For
$sigma_11$, with $V'$ the standard $(n-2)$-dimensional representation of
$S_(n-1)$, $RR^(n^2) = 4(1|1) directsum 2(V'|1) directsum 2(1|V')
directsum (V'|V')$; transposition fuses $(V'|1)$ with $(1|V')$ and splits the
trivial multiplicity space as $3 + 1$, leaving a $3 times 3$ block $A$, a
sign block $B$, a $2 times 2$ block $C$ of multiplicity $2(n-2)$ and a
$1 times 1$ block $D$ of multiplicity $(n-2)^2$. Both consistency checks
pass: $6 + 1 + 3 + 1 = 11$ orbit parameters, and
$3 + 1 + 4(n-2) + (n-2)^2 = n^2$. The decomposition was verified against a
direct eigendecomposition of the assembled matrix on _random_ orbit
coefficients at $n = 4, dots, 8$; a check run on the real certificate could
pass by accident on a matrix carrying extra structure.

#claimbox[
  _Consequence._ Positive definiteness of both Grams for all $n gt.eq 4$ is
  exactly the positivity of _ten_ explicit rational functions of $n$: the
  three $sigma_0$ eigenvalues, the three leading principal minors of $A$, the
  block $B$, the two leading minors of $C$, and the block $D$. One is not
  independent: $D = theta_2 \/ n$ _exactly_, an identity of rational
  functions and not a coincidence at sampled $n$, so the certificate rests on
  _nine_ independent positivity facts. We certify all ten regardless, since
  Sylvester's criterion asks for all ten directly.
]

Choosing the eight free variables as functions of $n$ is the whole
difficulty, and its shape is not the obvious one. The feasible set is
_unbounded_; worse, the quantities that must be controlled need the two Grams
positive semidefinite only on $bold(1)^perp$, which leaves a four-dimensional
_lineality space_ — exactly the $lambda$ reparametrisation — along which
optima drift so violently that no curve in $n$ can follow them. Quotienting
it out by a transversal slice makes the set compact and leaves an essential
design problem in four unknowns, and that is necessary but not sufficient,
because _the compact set that remains is a sliver_: in scaled coordinates
$beta = f dot n^3$, four of the ten quantities are differences of terms of
size $n^2$ or $n^3$ that must cancel to $O(1)$, which forces
$beta_6 - 2 beta_9 = O(n^(-2))$, $beta_12 - (2 beta_9 - 1) = O(n^(-1))$ and
$beta_11 - 2 beta_12 - 2 = O(n^(-1))$, the last pinned to $O(n^(-3))$. A
least-squares fit whose residual is small against the diameter of that set is
still far outside it.

The fix is to write the cancellations into the coordinates so that they
happen symbolically rather than numerically —
$beta_9 = b$, $beta_6 = 2b + x\/n^2$, $beta_12 = 2b - 1 + y\/n$,
$beta_11 = 2 beta_12 + 2 + z\/n$ — and then _solve for $z$ exactly over
$QQ(n)$ from the equation $theta_2 = D$_ rather than fitting it. That is the
step which makes the difference: the two quantities are affine in $z$ with
opposite-sign coefficients of size $n^2$ and the window between them has
width $O(n^(-2))$, so at $n = 10^6$ a numerical fit would need twelve correct
digits merely to stay inside. With $z$ eliminated the remaining parameters
carry $Theta(1)$ coefficients and an ordinary semidefinite program over a
grid of $n$ finds them:

#keybox[
  $ b = 1, quad x = 8 + 20/n, quad y = -2 - 10/n, quad
    z = frac(6n^7 - 28n^6 + 41n^5 - 28n^4 + 48n^3 - 164n^2 + 208n - 80,
            n^7 - 7n^6 + 19n^5 - 25n^4 + 16n^3 - 4n^2). $
]

The transferable form of the step is short: _in a family of certificates
indexed by a parameter, identify the tight direction and eliminate it
symbolically; fit only the slack ones._ The nineteen resulting certificate
variables are exact rational functions of $n$, recorded in the accompanying
material; the largest has numerator of degree 9 over denominator of degree
12, and $theta_2$ decays like $n^(-5)$, so the endpoint costs margin, not
sign. Four routes a reader would otherwise try are closed by exact rational
witnesses, recorded with those witnesses in the kit: linear programming for
the design step, which is bilinear rather than linear once one sees that the
rescaling it needs must be read off the certificate it is trying to choose;
least squares through analytic centres, which fails off-grid at $n = 17$,
$71$ and $811$; pinning four entries to constant targets, which fails for all
210 four-subsets; and restricting $lambda$ to a sum of squares, which removes
the recession cone but not the lineality space.

== Positivity decided, and verified <sec-sturm>

Substituting $n = m + 4$ turns each of the ten quantities into a ratio of
polynomials in $m$ on the range $m gt.eq 0$. The sign of each denominator
there is _checked_, not assumed, and the numerator's positivity on
$[0, infinity)$ is then _decided_ by a Sturm chain on the squarefree part,
comparing sign variations at $0$ and at $+infinity$. There is no sufficiency
gap in that step, which is why the tempting shortcut "all coefficients
non-negative in $m$" is only a heuristic: $m^2 - m + 1$ is positive
everywhere and has a negative coefficient.

#figure(
  table(
    columns: (auto, auto, auto, auto, auto, auto, auto, auto, auto, auto, auto),
    align: center,
    stroke: tstroke,
    inset: 4pt,
    table.header([], [`theta0`], [`theta1`], [`theta2`], [`A_1`], [`A_2`],
      [`A_3`], [`B`], [`C_1`], [`C_2`], [`D`]),
    [sqfree deg], [$0$], [$6$], [$4$], [$0$], [$5$], [$13$], [$5$], [$5$],
      [$12$], [$4$],
    [$V(0) = V(infinity)$], [—], [$1$], [$1$], [—], [$1$], [$3$], [$2$],
      [$1$], [$2$], [$1$],
    [roots in $(0,infinity)$], [$0$], [$0$], [$0$], [$0$], [$0$], [$0$],
      [$0$], [$0$], [$0$], [$0$],
    table.hline(stroke: 0.7pt + luma(40)),
  ),
  caption: [All ten quantities, positive for every $n gt.eq 4$. Each column
    is a complete decision, not a sample. `D` and `theta2` share a numerator
    — visible in the matching squarefree degree — because $D = theta_2\/n$
    exactly. All ten denominators are sign-definite on $n gt.eq 4$, as are
    those of all nineteen certificate variables, so nothing blows up at any
    dimension.]
)

A certificate is worth what its checking is worth. The independent verifier
_re-derives the objective from the 1992 definition_, using none of the closed
forms, none of the block decomposition and none of the Sturm machinery, and
checks at each $n$ that both Grams are _positive definite_ by exact rational
$L D L^T$ on the _full_ $n^2 times n^2$ matrices rather than through the
blocks — so it confirms the block theory of @sec-design as well as the
numbers — that @eq-ansatz holds at random rational points, and that the
constant is $2 - k!\/n^k$. It accepts at $n = 4, 5, 6, 7$ and $n = 12$
exactly over $QQ$, and at $n = 25$ with the identity in $FF_p$ at three
primes near $2^20$. It also accepts the independently produced stored
certificates at $n = 4, 5$ as a positive control, and rejects four
single-variable perturbations; a verifier that never rejects proves
nothing.

= The local method: confinement, stability, and the collar <sec-local>

Where the certificate route stops, the following chain takes over. It has
three links and one assembly: confinement traps a violator near the Birkhoff
polytope; on the polytope itself the centred core is controlled by
Theorem G; and the collar between them is paid for by exact reductions of the
cross terms.

== Confinement, for every $k$

Theorem E is recalled from [6] and transferred to all $k$; nothing here is
claimed as new mathematics. It is included because it is uniform in $k$ where
the certificate is not, and short enough to formalise once for the whole
family. The proof needs no expansion of the objective. Split the deficit as
$(2 - gamma(n,k)) - Phi_k (A) = [1 - E_k (r)] + [1 - E_k (c)]
+ [P_k (A) - gamma(n,k)]$, where the third bracket is at least
$-gamma(n,k)$ because $P_k$ of a non-negative matrix is non-negative. For the
first two, Maclaurin in the telescoped form of Theorem F gives
$E_k (r) lt.eq E_2 (r)$ on the simplex, and $E_2$ is exactly computable,
$E_2 (r) = 1 - sum_i (r_i - 1)^2 \/ (n(n-1))$ whenever $sum_i r_i = n$
(`SubDittertK2.E_two_eq`, needing no positivity). The contrapositive is the
confinement statement: a violator has its line sums within
$(n-1) k! \/ n^(k-1)$ of $bold(1)$ in squared $ell^2$ distance, a
neighbourhood of the _Birkhoff polytope_ — not of $J_n\/n$; the doubly
centred directions are not confined — that shrinks in $n$ for every fixed
$k gt.eq 2$.

The telescoped form $E_k lt.eq E_2$ carries no fractional powers, unlike the
usual $E_k^(1\/k) lt.eq E_2^(1\/2)$, and that is what makes it the statement
to formalise; its Lean proof, and a second independent one by a different
route kept deliberately outside the build, are described in @sec-machine.

== Stability on the doubly stochastic polytope <sec-stability>

Everything in this subsection is confined to $Omega_n$: the estimates use
four a-priori facts that hold there and fail on the larger set $K_n$, and
nothing here should be read as a statement about $K_n$. The transfer to the
collar, and the degradation it costs, is @sec-k4.

Fix $n gt.eq 2$, let $A in Omega_n$ and put $B = A - J_n\/n$,
$Q = norm(B)_F^2$. Every row and column of $B$ sums to zero; we call this the
_centred slice_. Write $q_i = sum_j b_(i j)^2$, $q'_j = sum_i b_(i j)^2$,
$M = max(max_i q_i, max_j q'_j)$, $beta = 1 - 1\/n$,
$p_r = sum_(i,j) b_(i j)^r$, and
$Y_R = sum_i q_i^2$, $Y_C = sum_j q'^2_j$, $Z = norm(B^T B)_F^2$. Four
invariants appear at degree five: with $f_3 (i) = sum_j b_(i j)^3$,
$g_3 (j) = sum_i b_(i j)^3$ and $q, q'$ read as vectors,
$Gamma_a = q^T B q'$, $Gamma_b = sum_(i,j) b_(i j)^2 (B B^T B)_(i j)$,
$Gamma_c = sum_i q_i f_3 (i)$ and $Gamma'_c = sum_j q'_j g_3 (j)$. Finally
$s_m, t_m$ are the coefficients of Theorem C in the index letter $m$ of the
layer they weight; two facts about them are used repeatedly,
$ t_2 = frac(k(k-1) thin k!, n^k (n-1)^2) " so " c(n,k) = t_2\/4,
  quad "and" quad frac(t_(m+1), t_m) = frac(n(k-m), (n-m)^2). $ <eq-stab-ratio>

#claimbox[
  *Lemma S1 (the layer identity).* For every $A in Omega_n$ and every
  $1 lt.eq k lt.eq n$, with $B = A - J_n\/n$,
  $ frac(sigma_k (A), binom(n,k)^2) - frac(k!, n^k)
    = sum_(m=2)^k t_m thin sigma_m (B). $ <eq-stab-layer>
  #leanline[Kernel-checked at _every_ $k$: `layer_identity` in
  `LayerIdentity.lean` (commit `27bda3f`), under hypotheses weaker than this
  part needs — see @sec-machine.]
]

Lemma S1 is the $P_k$ half of @eq-universal read on the centred slice, where
the $e_d$ half vanishes. _Proof._ Expanding a permanent of a sum, for index
sets $alpha, beta$ of size $k$,
$per((X+Y)[alpha|beta]) = sum per(X[S|T]) per(Y[alpha without S | beta
without T])$ over $S subset.eq alpha$, $T subset.eq beta$ with $|S| = |T|$.
Take $X = J_n\/n$, $Y = B$, so $per(X[S|T]) = d!\/n^d$ for $|S| = |T| = d$.
Summing over all $alpha, beta$ and writing $m = k - d$, each pair $(U,V)$
with $|U| = |V| = m$ is completed to $(alpha, beta)$ in $binom(n-m,k-m)^2$
ways, so
$sigma_k (A) = sum_m binom(n-m,k-m)^2 ((k-m)!\/n^(k-m)) sigma_m (B)$;
dividing by $binom(n,k)^2$ turns the coefficient into $t_m$. The $m = 0$ term
is $t_0 = k!\/n^k$ and the $m = 1$ term vanishes because
$sigma_1 (B) = sum_(i,j) b_(i j) = 0$. $qed$

Since $t_m > 0$ and $sigma_2 (B) = Q\/2$ on the slice, Theorem G is
equivalent to
$ sum_(m=3)^k t_m thin sigma_m (B) gt.eq -1/4 t_2 thin Q, $ <eq-stab-goal>
the two halves of $1\/2 t_2 Q$ splitting between the claimed bound and the
allowance. It is @eq-stab-goal that we prove.

_The core expansions._ On the slice each $sigma_m (B)$ collapses onto a small
set of invariants: expanding by Möbius inversion over ordered pairs of set
partitions of $[m]$, a partition with a singleton block contributes a row or
column sum of $B$ and dies, so only those orbit invariants survive whose
bipartite multigraph has minimum degree at least two. This expansion, and the
reductions at degrees two, three and four, are due to McCullagh [19, §3]; the
degree-five reduction specialises his general formula. For $B$ with vanishing
line sums,
$ sigma_2 (B) = 1/2 Q, quad sigma_3 (B) = 2/3 p_3, quad
  sigma_4 (B) = 3/2 p_4 + 1/8 Q^2 + 1/4 Z - 3/4 Y_R - 3/4 Y_C, $ <eq-stab-core4>
$ sigma_5 (B) = 24/5 p_5 + 1/3 Q thin p_3 + Gamma_a + 2 Gamma_b
  - 4 Gamma_c - 4 Gamma'_c, $ <eq-stab-core5>
the coefficient of $p_m$ being $(m-1)!\/m$, the only contributing partition
pair being the maximal one in each coordinate.

#leanline[Kernel-checked: the $sigma_4$ expansion in @eq-stab-core4 holds at
_every_ centred $B$ — `sigma_four_centred` in `SigmaFour.lean` (commit
`365e44e`), stated with both marginal hypotheses and consuming both, so it
holds wherever the row and column sums vanish and not only on
$Omega_n - J_n\/n$.]

#claimbox[
  *Lemma S2 (four a-priori facts).* Let $A in Omega_n$, $B = A - J_n\/n$.
  Then _(F1)_ $-1\/n lt.eq b_(i j) lt.eq 1 - 1\/n$; _(F2)_
  $M lt.eq 1 - 1\/n$; _(F3)_ $Q lt.eq n - 1$; _(F4)_
  $norm(B)_"op" lt.eq 1$, and consequently $Z lt.eq Q$.
]

_Proof._ (F1) Each entry of $A$ lies in $[0,1]$, being non-negative and at
most its row sum; subtract $1\/n$. (F2)
$q_i = sum_j A_(i j)^2 - 1\/n$ and
$sum_j A_(i j)^2 lt.eq (max_j A_(i j)) sum_j A_(i j) lt.eq 1$ by (F1);
columns likewise. (F3) Sum (F2) over $i$; equality at every permutation
matrix. (F4) With $u = n^(-1\/2) bold(1)$ we have $B u = 0$, and for
$x perp u$, $(J_n\/n)x = 0$ so $B x = A x$; by Birkhoff's theorem $A$ is a
convex combination of permutation matrices, each an isometry, so
$norm(A x) lt.eq norm(x)$, and decomposing an arbitrary $x$ gives
$norm(B x) lt.eq norm(x)$. Then
$Z lt.eq norm(B^T)_"op"^2 norm(B)_F^2 lt.eq Q$. $qed$

All four are attained at the permutation matrices, so none can be improved by
a constant factor. Birkhoff's theorem is where double stochasticity is
consumed, and (F4) is the fact that fails first off the slice.

The estimates below are one-sided by design: each invariant is bounded only
on the side the sign of its coefficient requires, and the asymmetry of the
range in (F1) makes the required side the cheap one. This is where the entry
bound earns its keep — for $b in [-1\/n, 1 - 1\/n]$,
$ b^3 gt.eq -1/n b^2 quad "and" quad b^3 lt.eq (1 - 1/n) b^2, $ <eq-stab-entry>
the first because $b^3 gt.eq 0$ when $b gt.eq 0$ and
$b^3 = b dot.c b^2 gt.eq -b^2\/n$ when $b < 0$, the second symmetrically.
Summing the first gives $p_3 gt.eq -Q\/n$, a factor $n$ stronger than the
two-sided $|p_3| lt.eq beta Q$, which would be too weak for what follows.

#claimbox[
  *Lemma S3 (per-invariant estimates).* On the centred slice: _(a)_
  $p_3 gt.eq -Q\/n$; _(b)_ $p_5 gt.eq -Q\/n^3$; _(c)_
  $p_4 lt.eq beta^2 Q$; _(d)_ $Y_R lt.eq M Q$ and $Y_C lt.eq M Q$
  (_attained_); _(e)_ $Gamma_c, Gamma'_c lt.eq beta M Q$; _(f)_
  $|Gamma_a| lt.eq M Q$; _(g)_ $|Gamma_b| lt.eq beta Q$; _(h)_
  $Q p_3 gt.eq -beta Q$; _(i)_ $Z lt.eq Q$ (_attained_); _(j)_
  $p_4, Q^2, Z gt.eq 0$.
]

_Proof._ (a) is @eq-stab-entry summed, and (b), (c) are the same argument at
the other powers, using $b^3 gt.eq -n^(-3)$ and $b^2 lt.eq beta^2$ from (F1).
(d) $Y_R lt.eq (max_i q_i) sum_i q_i lt.eq M Q$, with equality when all $q_i$
agree, in particular at every permutation matrix. (e) By @eq-stab-entry,
$f_3 (i) lt.eq beta q_i$ with $q_i gt.eq 0$, so
$Gamma_c lt.eq beta Y_R lt.eq beta M Q$. (f)
$|q^T B q'| lt.eq norm(q) norm(B)_"op" norm(q') lt.eq M Q$ by (F4) and (d).
(g) By Cauchy–Schwarz and (F4),
$|Gamma_b| lt.eq sqrt(p_4) norm(B)_"op" norm(B^T B)_F lt.eq
sqrt(p_4) sqrt(Z) lt.eq beta Q$ using (c) and (i). (h) Multiply (a) by
$Q gt.eq 0$ and apply (F3). (i) is (F4); (j) is clear. $qed$

_Proof of Theorem G._ Combining the core expansions with Lemma S3 term by
term — discarding the non-negative invariants that carry a plus sign, by (j)
— gives $sigma_m (B) gt.eq -C_m (n) Q$ with
$ C_3 (n) = frac(2, 3n), quad C_4 (n) = 3/2 beta, quad
  C_5 (n) = frac(24, 5 n^3) + 10/3 beta + 8 beta^2. $ <eq-stab-C>
For $C_4$ the only negative terms of @eq-stab-core4 are $-3/4(Y_R + Y_C)$,
bounded by $3/2 M Q lt.eq 3/2 beta Q$ by (d) and (F2); for $C_5$ the six
terms of @eq-stab-core5 contribute $24\/(5n^3)$, $beta\/3$, $M lt.eq beta$,
$2 beta$, $4 beta M lt.eq 4 beta^2$ and $4 beta M lt.eq 4 beta^2$ by (b),
(h), (f), (g) and (e). By @eq-stab-goal it therefore suffices that
$Phi(n,k) := (4\/t_2) sum_(m=3)^k t_m C_m (n) < 1$, and by the ratio law
@eq-stab-ratio this is an explicit rational function of $n$ for each $k$:
$ Phi(n,3) = frac(8, 3(n-2)^2), quad
  Phi(n,4) = frac(16, 3(n-2)^2) + frac(12 n(n-1), (n-2)^2 (n-3)^2), $ <eq-stab-phi4>
and $Phi(dot.c,5)$ likewise, its third term
$24 n^3 C_5 (n) \/ (n-2)^2 (n-3)^2 (n-4)^2$. At $k = 2$ the sum is empty, so
$Phi(n,2) = 0$ and the conclusion holds for every $n gt.eq 2$. Writing each
$Phi(dot.c,k)$ in lowest terms as a ratio of integer polynomials, the
denominators $3(n-2)^2$, $3(n-2)^2 (n-3)^2$ and
$5(n-2)^2 (n-3)^2 (n-4)^2$ are positive for $n > 4$, so $Phi(n,k) < 1$ is
equivalent to $P_k (n) > 0$ with $P_k$ the denominator minus the numerator:
$ P_3 = 3n^2 - 12n + 4, quad P_4 = 3n^4 - 30n^3 + 59n^2 - 48n - 36, $
$ P_5 = 5n^6 - 90n^5 + 445n^4 - 1760n^3 + 620n^2 + 2400n - 3456. $
Substituting $n = m + n_k$ with $n_k$ the threshold makes every coefficient
non-negative with the constant term positive —
$P_3 (m+4) = 3m^2 + 12m + 4$,
$P_4 (m+8) = 3m^4 + 66m^3 + 491m^2 + 1280m + 284$, and
$P_5 (m+14) = 5m^6 + 330m^5 + 8845m^4 + 121160m^3 + 861620m^2 + 2716720m
+ 1660864$ — which settles every $n gt.eq n_k$ at once, with no appeal to
numerics. The thresholds are sharp _for this argument_: $P_3 (3) = -5$,
$P_4 (7) = -568$ and $P_5 (13) = -306876$. $qed$

The binding term throughout is $Y_R$ (with $Y_C$), whose estimate (d) is
attained at the permutation matrices, so the thresholds cannot be lowered by
sharpening (d) — only by retaining the three non-negative terms of
@eq-stab-core4 that the proof discards, and that route is bounded.
_Proposition S6_, verified with its witness stored, is that $sigma_4$ on the
slice is _indefinite_: an explicit rank-two matrix at $n = 4$ gives
$sigma_4 (B)\/Q = -1\/32$. So $sigma_4 gt.eq 0$ is false, and the route can
at best replace $C_4$ by some $epsilon gt.eq 1\/32$, worth three steps at
$k = 4$ and two at $k = 5$. Proving any such $epsilon$ is a separate problem,
parked here.

#claimbox[
  *Proposition S4.* For $n = k = 3$ the conclusion of Theorem G is false.
  #leanline[Kernel-checked: `not_stabilityAt_three_three` in
  `TverbergStability.lean` (commit `1507013`), with the witness stored as
  `witness33` rather than cited.]
]

_Proof._ Take $A = 1/2 (J_3 - P)$ for a permutation matrix $P$ of order 3,
the doubly stochastic matrix uniform off a permutation. Then
$per(J_3 - P) = 2$, so $sigma_3 (A) = per(A) = 1\/4$, while
$binom(3,3)^2 3!\/3^3 = 2\/9$; hence $F = 1\/36$. Also $Q = 1\/2$, so
$F\/Q = 1\/18$, whereas $c(3,3) = t_2\/4 = 1\/12 > 1\/18$. $qed$

This is the only excluded cell known to be a counterexample. For
$(k = 4, 4 lt.eq n lt.eq 7)$ and $(k = 5, 5 lt.eq n lt.eq 13)$ the inequality
is not decided here, and no claim is made either way.

#claimbox[
  *Proposition S5 (sharpness).* Let $k gt.eq 3$ and let $c_"opt" (n,k)$ be
  the largest constant for which the conclusion of Theorem G holds. Then in
  the range covered by Theorem G,
  $1/4 t_2 lt.eq c_"opt" (n,k) < 1/2 t_2$.
]

_Proof._ The lower bound is Theorem G. For the upper bound take
$B = J_n\/n - P$ and $A_s = J_n\/n + s B$, doubly stochastic for
$0 lt.eq s lt.eq 1\/(n-1)$. The entries of $B$ are $-beta$ at the $n$ cells
of $P$ and $1\/n$ elsewhere, so
$p_3 (B) = ((n-1)\/n^2)(1 - (n-1)^2) < 0$ for $n gt.eq 3$, and by Lemma S1
and the core expansions
$F(s B)\/norm(s B)_F^2 = 1/2 t_2 + s t_3 (2/3 p_3 (B))\/Q_B + O(s^2)$,
strictly less than $1/2 t_2$ for all small $s > 0$. $qed$

So the constant of Theorem G is optimal to within a factor two, and that
factor cannot be closed: no constant as large as $1/2 t_2$ works for any
$k gt.eq 3$. A verified computation, not a theorem, corroborates the picture
at $k = 4$: the largest admissible constant, measured against the claimed
$c(n,4)$, is $1.88$, $1.91$, $1.93$ at $n = 8, 9, 10$ — rising toward the
ceiling of Proposition S5 and never reaching it.

_Verification._ Every displayed identity and estimate of this subsection is
checked over $QQ$, with no floating-point arithmetic in any decision, by the
standalone script `graded_verify_stability.py`, which imports nothing beyond
the standard library: Lemma S1 and the core expansions against brute-force
subpermanent sums; the four facts of Lemma S2; each estimate of Lemma S3 in
the one direction the proof uses, reporting its slack ratio so the two
tightness claims are checkable; the per-layer bounds @eq-stab-C; the closed
forms for $Phi$, the thresholds and the exceptional sets; the polynomial
argument term by term, including the sign pattern of $P_k (m + n_k)$ and the
sharpness values $P_k (n_k - 1) lt.eq 0$; Theorem G end to end at every
covered cell; Propositions S4 and S5; and the formalisation scope of
@sec-machine against the Lean sources at the commits cited there, read with
`git show` so the working tree cannot flatter the claim. That last check is
the one exception to the script being self-contained, and run with
`--no-lean` it skips it and _records in its log that the scope claims went
unchecked_. The test matrices are the configurations at which Lemma S3 is
attained or nearly attained. Four mutation controls fire — the constant
doubled, a sign flip in @eq-stab-core4, each threshold lowered by one so that
an excluded cell is claimed as covered, and Lemma S3(a) over-tightened — and
with no fault injected those same four checks raise nothing, so each
rejection is attributable to its fault.

== The collar assembly at $k = 4$ <sec-k4>

Let $A in K_n$ and $B = A - J_n\/n$ with row sums $R$ and column sums $C$.
Set $x_i = R_i\/n$, $y_j = C_j\/n$, $L_(i j) = x_i + y_j$ and $z = B - L$, so
$sum_i x_i = sum_j y_j = 0$, $z$ is doubly centred, and
$norm(L)_F^2 = n(mu + nu)$ with $mu = norm(x)^2$, $nu = norm(y)^2$. The
invariants $Q, q_i, q'_j, f_3, g_3$ are as in @sec-stability but now taken of
$z$, and $N = z z^T$, $N' = z^T z$. Confinement bounds the line block only:
$mu + nu lt.eq u_max (n,k) = (n-1)k!\/n^(k+1)$.

_What couples._ @eq-universal gives
$F = sum_d [t_d sigma_d (B) - s_d (e_d (R) + e_d (C))]$, whose $e_d$ half
never couples, since $z$ has vanishing line sums and so the line sums of
$L + z$ are those of $L$ alone. For the $sigma_d$ half, expansion by the
number of $z$ factors,
$ sigma_d (X + Y) = sum_(j=0)^d sum_(|S| = |T| = j)
  per(X[S|T]) thin sigma_(d-j) (Y^((S,T))), $ <eq-k4-expand>
with $Y^((S,T))$ being $Y$ with rows $S$ and columns $T$ deleted, taken at
$X = z$, $Y = L$, gives
$F(L + z) = F_"line" (x,y) + F_"centred" (z) + sum_d t_d dot.c
("cross parts of " sigma_d)$. At $d = 2$ the cross part vanishes
_identically_, not merely to leading order.

_The five cross terms._ All are exact, and all are verified against brute
force. At $d = 3$,
$ X_1 = (n-2)^2 thin x^T z thin y, quad X_2 = (2 - n) Xi, quad
  Xi := sum_i x_i q_i + sum_j y_j q'_j; $
at $d = 4$,
$ Y_1 = -(n-2)(n-3)^2 [thin x^T z (y compose y)
  + (x compose x)^T z thin y thin], $
$ Y_2 = (n-2)(n-3) [ -sum_(s_1 < s_2) N_(s_1 s_2) e_2 (x_I)
  - sum_(t_1 < t_2) N'_(t_1 t_2) e_2 (y_J) ]
  + 2(n-3)^2 sum_(i,j) z_(i j)^2 x_i y_j, $
$ Y_3 = -(n-3)[2 A_1 - A_2 + 2 A_3 - A_4], quad
  A_1 = sum_a x_a f_3 (a), quad A_2 = x^T z thin q', $
$A_3 = sum_b y_b g_3 (b)$, $A_4 = q^T z thin y$, where $compose$ is the
entrywise product and $I = [n] without S$, $J = [n] without T$ for the
deleted index pairs. One principle produces all three of the $d = 4$ terms:
_anything separable in the deleted indices is annihilated by
$sum_a z_(a b) = sum_b z_(a b) = 0$._ For $Y_1$ what survives is that the
restricted $e_1$ is _not_ zero — on $I = [n] without {a}$ one has
$e_1 (x_I) = -x_a$ and $e_2 (y_J) = e_2 (y) + y_b^2$ — so the terms depending
on one deleted index alone die and the rest leave $x_a y_b^2$ and
$x_a^2 y_b$. For $Y_2$ it is a vanishing lift: the $e_2$ pieces depend on $S$
alone and $T$ alone, with $sum_T per(z[S|T]) = -N_(s_1 s_2)$, while for the
$x_S y_T$ piece the lift of the restricted sum to the unrestricted one is
_identically zero_, every expanded piece carrying a lone $sum_s z_(s t)$ or
$sum_t z_(s t)$, so the restricted sum is a pure diagonal correction — and an
absolute-value bound, discarding exactly that cancellation, overshoots by
four orders of magnitude. For $Y_3$ it is subpermanents through a row:
$sigma_1 (L^((S,T))) = -(n-3)(x_S + y_T)$ and
$sum_(S,T) per(z[S|T]) x_S = sum_a x_a (2 f_3 (a) - (z q')_a)$.

_The merge, and why $k = 4$ inherits the clean form._ On the collar
$A gt.eq 0$ gives the _per-entry_ bound $z_(i j) gt.eq -(1\/n + x_i + y_j)$,
not $z_(i j) gt.eq -1\/n$; cubing and summing gives
$sum_(i j) z_(i j)^3 gt.eq -Q\/n - Xi$, whose perturbation is _exactly_ the
invariant of the cross term $X_2$. The two effects are therefore one
quantity, to be charged once — but _at its full summed coefficient_: the
$m = 3$ layer contributes $2/3 Xi$ and the cross term $(n-2) Xi$, so the
coefficient is $(3n-4)\/3$, not $(n-2)$. Counting once deletes the double
count, not a coefficient. At $k = 4$ the layers are
$m = 2, 3, 4$ and the only odd-power one-sided step is at $m = 3$: the
centred core of $sigma_4$ is @eq-stab-core4, every term of even degree, so no
second perturbation can arise and the merge keeps its single-coefficient
form. This is special to $k lt.eq 4$: at $m = 5$ the perturbation enters as
$(1\/n + x_i + y_j)^3$, which is four cross invariants rather than one.

_The collar facts._ Write $rho^2 = (n-1)k!\/n^(k-1)$ for the confinement
radius on line sums and $beta_c = 1 + rho - 1\/n$. The four facts below are
the collar forms of (F1)–(F4), in the same order, with the degradation the
collar costs. _(K1)_ $-1\/n lt.eq b_(i j) lt.eq beta_c$; the lower side needs
only $A gt.eq 0$ and so does _not_ degrade off the slice, and that asymmetry
is what makes the $m = 3$ step cheap. _(K2)_
$max_i q_i (B) lt.eq (1 + rho)^2 - 1\/n + 2 rho\/n$. _(K3)_
$Q lt.eq n - 1 + rho^2$. _(K4)_
$norm(B)_"op" lt.eq sqrt((1 + rho)^2 + rho^2\/n)$, since a non-negative
matrix with all line sums at most $1 + rho$ has operator norm at most
$1 + rho$: Birkhoff is lost off the slice, but the bound is not.
Consequently $norm(z)_"op" lt.eq norm(B)_"op" + sqrt(2 n thin u_max)$.

_The one unsettled constant._ The slice bound $q_i (z) lt.eq 1 - 1\/n$
requires row sums equal to $1$ _and_ non-negativity; on the collar
$J_n\/n + z$ has row sums $1$ but may have negative entries, so the bound
does not transfer, and it is refuted — a permutation with one reweighted row
violates it by a factor $1.63$ at $(k=4, n=10)$. We therefore write
$q_i (z) lt.eq c thin (1 - 1\/n)$ and carry $c$ symbolically. A verified
sensitivity computation, graded as exactly that and recorded with its ten
sampled values in the reproduction kit, recomputes the honest threshold
exactly over $QQ$ at each and finds it equal to $10$ at every sampled value
inside the admissible band $1.58 lt.eq c lt.eq 2.53$, whose ends are the
smallest constructed violation and the proved collar cap; no claim is made
for unsampled $c$.

_The budget._ Layer two is the budget: on the centred block
$t_2 sigma_2 (z) = 1/2 t_2 Q$, and on the line block
$F_"line" gt.eq 1/2 lambda_"line" (mu + nu)$. Every other contribution is
bounded below and charged to whichever budget it scales with — $X_1$ and
$Y_1, Y_2$ carry $(mu + nu)$ or $(mu + nu)^(3\/2)$ and go to the line side;
$Xi$ and $Y_3$ carry $Q$ or $sqrt(mu + nu) sqrt(M Q)$ and go to the centred
side, $Y_3$ split between the two by the arithmetic–geometric mean. Both
totals below $1$ is the conclusion, and that is Theorem H.

_Verification._ `graded_verify_k4.py` recomputes every displayed quantity of
this subsection over $QQ$ with no floating-point arithmetic in any decision:
@eq-k4-expand at $d = 2, 3, 4$ against brute force, including that the
$d = 2$ cross part is exactly zero; the end-to-end split identity with every
$t_d$ in place, against $F$ computed from the 1992 functional; all five
cross-term reductions against brute force; the per-entry bound and the merge,
on configurations of _both_ signs of $sum z^3$; the four collar facts; every
budget line recomputed from the layer identity; and the sensitivity table row
by row, parsed from its committed source rather than restated, so displayed
and checked cannot drift apart. Four mutation controls fire, each with a
_separating_ witness asserted in the same line: a $t_d$ factor dropped from a
cross term, caught by the end-to-end identity; the merge coefficient
$(3n-4)\/3$ replaced by $(n-2)$, caught by the budget-line check; the $d = 2$
cross part assumed non-zero, caught by the expansion check; and $c$ rescaled
in a $c$-independent line, caught by the sensitivity audit. Two of the four
encode errors made and corrected while the argument was being assembled — a
dropped $t_4$, and the merge coefficient. They are controls because they
happened.

= The small cells at $k = 4$, and the gap <sec-cells>

Theorem H begins at $n = 10$. The five cells below it are each a fixed-$n$
question, recorded at the grade each has actually reached; no cell inherits
the grade of a neighbour. _Anchor grade_ means an exact rational certificate
accepted in full by six checks of the standalone verifier — the bound;
$sigma_k$ by two structurally different algorithms; the identity by _full_
coefficient comparison; definiteness of the assembled Grams by exact
$L D L^T$ over $QQ$; equality only at $J_n\/n$; mutation tests rejected —
and anything less is stated as what it is.

#figure(
  table(
    columns: (auto, auto, auto),
    align: (center, left, left),
    stroke: tstroke,
    inset: 4.5pt,
    table.header([*cell*], [*status*], [*support, and what is missing*]),
    [$(k=4, n=5)$], [settled: $Phi_4 lt.eq 1226\/625$ on $K_5$],
      [anchor grade; 26 exact $L D L^T$ factorisations of size 350, two
       independent full runs logged],
    [$(k=4, n=6)$], [settled: $Phi_4 lt.eq 107\/54$ on $K_6$],
      [anchor grade on a stored exact witness: identity over all 40,386
       coefficients, both assembled Grams (cone size 702) definite over $QQ$,
       conjugacy proved exactly],
    [$(k=4, n=7)$], [settled: $Phi_4 lt.eq 4778\/2401$ on $K_7$],
      [anchor grade on a stored exact witness: identity over all 156,555
       coefficients, conjugacy exact, assembled positivity by the congruence
       route below],
    [$(k=4, n=8)$], [_not settled_; one check short],
      [five of the six checks hold on a stored exact witness — identity over
       all 496,448 coefficients, the bound $1021\/512$, equality only at
       $J_8\/8$, conjugacy exact, and positivity _block-wise_ for all 21
       canonical blocks. The assembled $2144 times 2144$ factorisation has
       not run, and block definiteness is not assembled definiteness],
    [$(k=4, n=9)$], [_not settled_],
      [no witness exists: the exact solve exceeded available memory at this
       size. Nothing is stored, and nothing is claimed],
    table.hline(stroke: 0.7pt + luma(40)),
  ),
  caption: [The five cells between Theorem A's line and Theorem H's range, as
    of 30 July 2026. In every settled cell equality holds only at $J_n\/n$.]
) <k4-anchor-table>

At $(k=4, n=7)$ both assembled Grams are positive definite over $QQ$ by
_congruence_ rather than by a single direct factorisation: the 21 isotypic
components are exactly $H$-orthogonal over $QQ$ and their translates span; on
each component the congruence block is a Kronecker product $C_b kron h_b$,
and all 21 of each factor are positive definite under exact $L D L^T$; the
Kronecker argument then makes each component block definite,
orthogonality-with-spanning assembles the components, and the conjugacy
extends the verdict to all 49 multiplier Grams. Every link is a stored
artefact, verified exactly over $QQ$ with rejection controls that fire. The
two component computations use different bases of the same components, and
the check reconciling them is a _consistency check between stored artefacts,
not an independent verification_.

_The gap, stated once._ Unconditionally, the line $k = 4$ is settled for
$n = 5, 6, 7$ at anchor grade and for every $n gt.eq 10$ by Theorem H, and is
_not settled at $n = 8$ and $n = 9$_. It becomes settled for every
$n gt.eq 5$ exactly when those two cells reach at least anchor grade, and not
before. No theorem of this paper depends on any cell of @k4-anchor-table.

Two routes could close it: fixed-$n$ certificates at the two open cells, or a
certificate family in $QQ(n)$ at $k = 4$, which would need no anchors and
would besides supersede the local route and inherit the $k = 3$ formalisation
pattern. The groundwork for the second is a decided sweep rather than a
certificate, recorded in the kit with its witnesses; two of its facts bear on
the method's reach. Mixed Gram degrees are ruled out for even $k$, since they
would force the top form $F_k$ to be a sum of squares on the hyperplane, and
@eq-universal gives $F_k (b) = s_k [s_k sigma_k (b) - e_k (R) - e_k (C)]$,
negative at explicit doubly centred integer matrices; so the programme's
counts are constant on the bands $\{2,3\}$, $\{4,5\}$, $\{6,7\}$, and grow
from 19 unknowns at $e = 1$ to 440 at $e = 2$, which is why the route reaches
every _fixed_ $k$ at all large $n$ and cannot reach $k = n$. And for band two
the pinning programme is decided over $QQ$ at $n = 5, 6, 7$, with no verdict
resting on a solver's reported sign. There is still no certificate family in
$n$ for band two, so there is nothing yet to formalise.

= What is machine-checked, and what is not <sec-machine>

#keybox[
  The development elaborates with no `sorry`, and no declaration in it
  depends on `sorryAx`. `native_decide` is used nowhere. Every declaration
  cited above in support of a stated result carries a `#print axioms`
  command, and each returns exactly
  `[propext, Classical.choice, Quot.sound]` — with one exception,
  `NewtonIneq.choose_mul_sub`, a statement about binomial coefficients, which
  returns the strict subset `[propext, Quot.sound]`. Build success is not an
  axiom audit, and the two are kept separate here.
]

_The $k = 3$ chain._ On the Lean sources as committed at `32c811e`, the eight
files carrying Theorems A and C–F carry `#print axioms` on 511 declarations:
`SubDittertK3.lean` and `RookSum.lean` (Theorem A),
`SubDittertUniversal.lean` (C), `SubDittertK2.lean` (D),
`SubDittertLinear.lean`, `SubDittertM.lean` and `SubDittertMaclaurin.lean`
(E), and `NewtonInequalities.lean` (F), built against Lean 4.14.0 and Mathlib
`v4.14.0` [16]. In `SubDittertK3.lean` the 377 are _every_ named declaration
in the file, private ones included. Elsewhere the audits cover the results
and their supporting lemmas rather than every private definition, which is
not a gap: `#print axioms` reports the axioms of the _transitive closure_ of
a proof term, so auditing a theorem audits everything it rests on, and no
file contains a `sorry`, so nothing can acquire `sorryAx` from within.

`subDittert_k3_full` is Theorem A in all three parts, with `Kn`, `esym`,
`subPerm`, `sigmaK`, `E`, `P` and `Phi` built from scratch inside Lean and
the final statement written in the 1992 notation. Two declarations _validate_
those definitions, and they matter more than they look: `Phi_uniform` proves
$Phi_k (J_n\/n) = 2 - k!\/n^k$ for every $k lt.eq n$, so the functional as
formalised is tight at the conjectured maximiser exactly where the conjecture
says it is; and `sigmaK_rankOne` proves
$sigma_k (x y^T) = k! e_k (x) e_k (y)$, the check that rows are read from $S$
and columns from $T$ — a definition reading both indices off the same subset
satisfies a different identity, and a symmetric test matrix cannot detect
that error. From there, `RookSum.lean` and `obj_eq_objPoly` close the
combinatorial half for all $n$ at once, eliminating `Matrix.permanent`,
`sigmaK`, `esym` and every `Finset.powersetCard` sum from everything
downstream; `certPositive_of_four_le` proves the ten positivity facts for
every _real_ $n gt.eq 4$; `G0_posSemidef` and `Hm_posSemidef` give both Gram
families with no spectral theorem, and `G0_posDef` the definiteness the
equality case needs; `certificate_identity` is the Positivstellensatz
identity itself; and `subDittert_k3_stability` with
`eq_uniform_of_Phi_eq_of_stability` give the stability bound and the equality
case, which stands on two independent Lean proofs.

_Theorem G's cells._ These rest on further files, counted at their own
commits and held to the same standard: `StabilityK3.lean` (33 audit lines)
and `TverbergStability.lean` (21) at `1507013`, `LayerIdentity.lean` (28) at
`27bda3f`, `SigmaFour.lean` (46) at `365e44e`, `StabilityK4.lean` (14) at
`944b517`, and the partial `StabilityK5Atoms.lean` (15) at `f2bdc7f`.
Theorem G is kernel-checked at $k = 2$ for every $n gt.eq 2$, at $k = 3$ for
every $n gt.eq 4$, and at $k = 4$ for every $n gt.eq 8$ — in each case the
whole range the statement covers for that $k$, with no arithmetic gap between
the formalised and the written range. All three discharge
`TverbergStability.StabilityAt k n`, the displayed inequality of Theorem G
with `cVal` equal to $c(n,k)$; the $k = 4$ proof follows this paper's route
step for step, its threshold arithmetic consumed as `Phi4_lt_one` with the
bridge `layer_ratio_lt` checking that $Phi$ rebuilt from the Lean
coefficients is exactly @eq-stab-phi4. Lemma S1 is kernel-checked at _every_
$k$, under hypotheses weaker than this paper's — only $1 lt.eq k lt.eq n$ and
the single scalar constraint $sum_(i j) B_(i j) = 0$, where Lemma S1 as
stated here assumes $A$ doubly stochastic — so the identity underneath the
whole argument holds formally on a strictly larger set than the theorem
needs. Proposition S4 is kernel-checked with its witness stored rather than
cited, as is the threshold layer at $k = 3, 4, 5$; and
`three_threshold_not_slack` gives the sharpness of the $k = 3$ threshold in
the strong form that assuming stability at every $n gt.eq 3$ is
contradictory.

_Two limits of the $k = 4$ formalisation must not be over-read._ First, the
threshold $8$ is _a limit of the argument, not known sharp_: the cells
$(k = 4, 4 lt.eq n lt.eq 7)$ are undecided, and there is no $k = 4$ analogue
of `three_threshold_not_slack` — nothing here should be read as implying one.
Second, the binding atom is $Y_R$ (with $Y_C$), attained at the permutation
matrices, so the threshold cannot move by sharpening anything in the
formalised file.

_What is not machine-checked._ Theorem H, and with it everything the collar
costs on top of the slice — the collar facts, the cross-term reductions, the
merge and the budget — rests on written proofs plus the exact verifier. At
$k = 5$ neither the estimates feeding the budget nor Theorem G itself is
formalised: there is no `stabilityAt_five`, and while five of the $k = 5$
per-invariant atoms _are_ kernel-checked, the degree-five expansion,
estimates (f) and (g), fact (F4) and the assembly are not, so the cell is not
closed — partial atom coverage is not cell coverage, and we do not average
the two. The fixed-dimension certificates of @sec-cells are unformalised, as
is the block-diagonalisation of @sec-design _as an equivalence_: Lean proves
the implication the theorem needs, by explicit algebra rather than by that
route, so the reduction is corroborated by the Lean development without being
verified by it. The constant $theta_2 (n)$ is not claimed optimal — measured
slack ratios of $2.88$, $4.34$, $5.70$ at $n = 4, 5, 6$ put it within a
factor of three to six of the best constant where it is closest to tight.
Finally, what the kernel cannot check anywhere is that the Lean definitions
say what the 1992 paper says; the validation step above is the argument that
they do, and it is the only place left where a human error would survive the
machine.

_How the division is checked, not asserted._ The stability verifier reads
each Lean file at the commit cited for it and confirms both halves: that
`cVal` _is_ $c(n,k)$, compared as exact rationals over a grid rather than as
text; that the hypotheses of `stabilityAt_two`, `stabilityAt_three` and
`stabilityAt_four` are the thresholds claimed above; that
`sigma_four_centred` carries both marginal hypotheses; that Lean's
$P_3, P_4, P_5$, an independent derivation, agree at every point with the
polynomials the verifier builds; and, on the negative side, that no
`stabilityAt_five` exists — with a non-vacuity check that the same search
does find the three theorems that are there, since an absence found by a
broken search is not an absence. It also runs the orphan diff on the four
files carrying audit blocks, empty in both directions: 33 of 33 declarations
in `StabilityK3.lean` carry `#print axioms` lines, as do 14 of 14
declarations in `StabilityK4.lean`, 46 of 46 declarations in `SigmaFour.lean`
and 28 of 28 declarations in `LayerIdentity.lean`, and no source contains
`sorry` or `native_decide` outside its comments. All four counts are parsed
back out of this section, so a number stated here and a number measured there
cannot drift apart. One limit is worth stating: the axiom sets themselves —
that each of the 121 audited declarations reports a subset of `propext`,
`Classical.choice`, `Quot.sound` with no `sorryAx` — come from elaborating
the files, which only Lean can do and which the verifier does not repeat.

_What is not claimed, and where the methods stop._ At $k = 4$: nothing beyond
$n gt.eq 10$ and the settled cells $n = 5, 6, 7$. At $k = 5$: nothing beyond
the stability cell $(k = 5, n gt.eq 14)$ at written-proof plus
exact-verifier grade — the Cheon–Hwang inequality itself is not claimed at
any $(k=5, n)$. No statement about general $k$ beyond Theorems C and E, and
no novelty for the identity of Theorem C, the statement of Theorem D, or
Theorems E and F. Nothing refereed. No floating-point number enters any
decision above: the numerics find candidates, and every accepted statement is
re-established over $QQ$ or $FF_p$. As for reach, $deg F = k$, so the Gram
basis degree must grow with $k$ and the degree-counting obstruction that
blocks the $k = n$ line reappears in $k$; the line $k = 3$ is tractable
exactly because its degree budget is fixed while the dimension grows. The
local route stops where its merge does — at $m = 5$ the one-sided step
splinters into four cross invariants, so $k = 5$ needs new ideas on the
centred block rather than more of the same. Two problems are parked with
their obstructions priced: a lower bound
$sigma_4 gt.eq -epsilon norm(z)_F^2$ on the doubly centred slice for some
$epsilon lt.eq 1\/16$, which would carry Theorem H down to
$(k = 4, n gt.eq 8)$ and is known false at $epsilon = 0$; and a certificate
family in $QQ(n)$ at $k = 4$. To our knowledge Theorem A is the first
resolved case of the Cheon–Hwang conjecture with $2 < k < n$ and Theorem G
the first stability form of the Tverberg–Friedland theorem; both claims cover
public code repositories as well as the indexed literature, both are priority
claims rather than claims of difficulty, and both are perishable, so they
should be re-checked before this paper is submitted anywhere.

= Data availability <sec-data>

The certificates as exact rational data, the objective builders, the
block-diagonalisation, the Sturm decision, the independent verifiers with
their controls, the sensitivity record of @sec-k4, the stored exact witnesses
behind @k4-anchor-table with the artefacts of the congruence route, the
band-two sweep, and the Lean development are supplied as a reproduction kit,
whose README names the claim each file backs and the procedure for re-running
each check. The failed design branches are retained there, because the four
closed routes of @sec-design are only checkable against them.

#v(0.6em)
#line(length: 100%, stroke: 0.4pt + luma(180))
#v(0.4em)

#text(8pt)[
  _Bibliography_

  [1] G.-S. Cheon and S.-G. Hwang, _Maximization of a matrix function related
  to the Dittert conjecture_, Linear Algebra Appl. _165_ (1992), 153–165.
  #h(1em) [2] M. Putinar, _Positive polynomials on compact semi-algebraic
  sets_, Indiana Univ. Math. J. _42_ (1993), 969–984.
  #h(1em) [3] S.-G. Hwang, _On a conjecture of E. Dittert_, Linear Algebra
  Appl. _95_ (1987), 161–169. (Dittert at $n = 3$.)
  #h(1em) [4] R. Sinkhorn, _A problem related to the van der Waerden
  permanent theorem_, Linear Multilinear Algebra _16_ (1984), 167–173.
  (Dittert at $n = 2$.)
  #h(1em) [5] G.-S. Cheon and I. M. Wanless, _An update on Minc's survey of
  open problems involving permanents_, Linear Algebra Appl. _403_ (2005),
  314–342.
  #h(1em) [6] G.-S. Cheon and I. M. Wanless, _Some results towards the
  Dittert conjecture on permanents_, Linear Algebra Appl. _436_ (2012),
  791–801. (Theorem 2.1 is Theorem E at $k = n$.)
  #h(1em) [7] G.-S. Cheon and I. M. Wanless, _An interpretation of the
  Dittert conjecture in terms of semi-matchings_, Discrete Math. _307_ (2007).
  (Not consulted; no result here depends on it.)
  #h(1em) [8] Divya K. U. and K. Somasundaram, _Lih Wang's and Dittert's
  conjectures on permanents_, Special Matrices _12_ (2024), 20240006;
  cf. arXiv:2312.00464v1, whose abstract claims Dittert at $n = 4$ where the
  published version makes no such claim.
  #h(1em) [9] Z. Pang, _Proof of Dittert's conjecture for dimensions
  $n gt.eq 17$_, arXiv:2606.01531 (2026). Preprint, not refereed.
  #h(1em) [10] B. Kafidov, _Dittert's conjecture in dimension 16 via a
  joint-deficit scaling lemma_, arXiv:2607.19439 (21 July 2026). Preprint,
  no DOI, not refereed.
  #h(1em) [11] Public repositories claiming Dittert cases, created
  21–25 July 2026, none refereed, all accessed 28 July 2026, each at
  `https://github.com/` followed by the name shown:
  `123ljh0bot/Dittert_Conjecture_in_Dimension_4`;
  `pedromnasc/dittert-conjecture-proof` (and the `subdittert/` package quoted
  in @sec-prior); `lueluelue2006/dittert-conjecture-draft` and
  `lueluelue2006/dittert-n7-extension`.
  #h(1em) [12] G.-S. Cheon and S. Yoon, _A note on the Dittert conjecture for
  permanents_ (2006); G.-S. Cheon, _On the monotonicity of the Dittert
  function_ (1993).
  #h(1em) [13] J. B. Lasserre, _Global optimization with polynomials and the
  problem of moments_, SIAM J. Optim. _11_ (2001), 796–817.
  #h(1em) [14] K. Gatermann and P. A. Parrilo, _Symmetry groups, semidefinite
  programs, and sums of squares_, J. Pure Appl. Algebra _192_ (2004), 95–128.
  #h(1em) [15] E. Levin and V. Chandrasekaran, _Any-dimensional polynomial
  optimization via de Finetti theorems_, arXiv:2507.15632 (2025).
  #h(1em) [16] The mathlib Community, _The Lean mathematical library_,
  CPP 2020.
  #h(1em) [17] H. Tverberg, _On the permanent of a bistochastic matrix_,
  Math. Scand. _12_ (1963), 25–35.
  #h(1em) [18] S. Friedland, _A proof of a generalized van der Waerden
  conjecture on permanents_, Linear Multilinear Algebra _11_ (1982), 107–120.
  Zbl 0482.15003.
  #h(1em) [19] P. McCullagh, _An asymptotic approximation for the permanent
  of a doubly stochastic matrix_, arXiv:1205.5723 (2012). The centred-core
  expansions in @sec-stability are his; the degree-five reduction specialises
  his general formula.
  #h(1em) [20] G. P. Egorychev, _The solution of van der Waerden's problem
  for permanents_, Adv. Math. _42_ (1981), 299–305.
  #h(1em) [21] D. I. Falikman, _A proof of van der Waerden's conjecture on
  the permanent of a doubly stochastic matrix_, Mat. Zametki _29_ (1981),
  931–938.
]
