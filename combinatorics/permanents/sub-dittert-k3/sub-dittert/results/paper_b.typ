#set page(paper: "a4", margin: (x: 2.4cm, y: 2.6cm), numbering: "1")
#set text(font: "New Computer Modern", size: 10.5pt)
#set par(justify: true, leading: 0.62em)
#set heading(numbering: "1.1")
#show heading: it => block(above: 1.3em, below: 0.7em)[#it]
#show raw.where(block: true): it => block(
  fill: luma(247), inset: 8pt, radius: 3pt, width: 100%,
  text(size: 8.5pt, it)
)
#show raw.where(block: false): it => box(
  fill: luma(243), inset: (x: 2pt), outset: (y: 2pt), radius: 2pt, text(size: 9.5pt, it)
)
#set math.equation(numbering: "(1)")
#let per = math.op("per")
#let directsum = math.class("binary", "⊕")

#show ref: it => {
  let el = it.element
  if el != none and el.func() == heading {
    link(el.location(),
      [§#numbering(el.numbering, ..counter(heading).at(el.location()))])
  } else { it }
}

#let leanline(body) = block(width: 100%)[
  #set par(justify: false)
  #text(9pt)[#body]
]

#let claimbox(body) = block(fill: rgb("#f4f8ff"), inset: 10pt, radius: 3pt, width: 100%)[#body]
#let keybox(body) = block(fill: rgb("#fff8f0"), inset: 10pt, radius: 3pt, width: 100%)[#body]
#let warnbox(body) = block(fill: rgb("#fff4f4"), inset: 10pt, radius: 3pt, width: 100%)[#body]

#align(center)[
  #text(15.5pt, weight: "bold")[
    The Cheon–Hwang Sub-Dittert Conjecture\
    at $k = 3$ and $k = 4$
  ]
  #v(0.4em)
  #text(11pt)[with a stability form of the Tverberg–Friedland theorem\
  and a decomposition of the deficit uniform in $n$ and $k$]
  #v(0.8em)
  #text(11pt)[D C P Revere]
  #v(0.15em)
  #text(9pt)[dcprevere\@gmail.com]
  #v(0.4em)
  #text(9pt, style: "italic")[Draft — 30 July 2026]
]

#v(1em)

#block(inset: (x: 1.2cm))[
  #text(9.5pt)[
    *Abstract.* Cheon and Hwang conjectured in 1992 that
    $E_k (r) + E_k (c) - P_k (A) lt.eq 2 - k!\/n^k$ for every non-negative
    $n times n$ matrix of total sum $n$ and every $1 lt.eq k lt.eq n$, with
    equality only at $J_n\/n$; the endpoint $k = n$ is Dittert's conjecture.
    This paper works the intermediate range $2 < k < n$ on two lines, and
    proves a stability theorem that the second line consumes. The results rest
    on different support layers — kernel-checked in Lean 4, or written proofs
    with an exact rational verifier — and each claim below is graded
    explicitly; the grading is part of the claim.

    *The line $k = 3$, every $n gt.eq 4$*: the inequality, the equality case,
    and the quantitative strengthening
    #set math.equation(numbering: none)
    $ (2 - 6\/n^3) - [E_3 (r) + E_3 (c) - P_3 (A)] gt.eq theta_2 (n) dot.c
      norm(A - J_n\/n)_F^2, quad
      theta_2 (n) = frac(n^4 + 40 n^2 - 84 n + 40, n^5 (n-1)^3 (n-2)), $
    by a single Positivstellensatz certificate whose nineteen symmetry-reduced
    coefficients are explicit rational functions of $n$: the governing degree
    is $k$, not $n$, so the reduced program has the same $12 times 19$ shape at
    every dimension and is solved once over $QQ(n)$, with definiteness of the
    two $n^2 times n^2$ Grams reduced in closed form to ten rational functions
    of $n$ decided by Sturm sequences. This part is machine-checked end to end
    (`subDittert_k3_full`): no `sorry`, Lean's standard axioms. With Hwang's
    1987 theorem at $n = 3$, the line $k = 3$ is settled in every dimension.

    *A stability form of the Tverberg–Friedland theorem.* On the doubly
    stochastic polytope the excess of $sigma_k$ over its minimum at $J_n\/n$
    is at least $binom(n,k)^2 thin c(n,k) thin norm(A - J_n\/n)_F^2$ with
    $c(n,k) = k(k-1) thin k! \/ (4 n^k (n-1)^2)$, for $k = 2$ (every
    $n gt.eq 2$), $k = 3$ (every $n gt.eq 4$), $k = 4$ (every $n gt.eq 8$) and
    $k = 5$ (every $n gt.eq 14$); the constant is optimal to within a factor
    two, and the cell $(k,n) = (3,3)$ is a genuine exception. Kernel-checked
    at $k = 2$, $k = 3$ and $k = 4$, in each case over the whole range the
    statement covers for that $k$; written proofs plus an exact verifier at
    $k = 5$.

    *The line $k = 4$*: the Cheon–Hwang inequality holds for every
    $n gt.eq 10$, with equality only at $J_n\/n$, by a local route —
    confinement traps any violator in a collar of the Birkhoff polytope, a
    collar matrix splits orthogonally into a line-sum block and a doubly
    centred block, and the five cross terms between the blocks have exact
    reductions. A companion sensitivity computation, graded as exactly that,
    finds the threshold unmoved at every sampled admissible value of the one
    constant in the argument that is not settled, with the shape of the
    $c$-dependence asserted mechanically. The theorem is not formalised; its
    support is written proofs plus an exact verifier that re-reads the
    displayed numbers out of this document. Fixed-dimension certificates
    settle the cells $(5,4)$, $(6,4)$ and $(7,4)$ besides, so on the line
    $k = 4$ exactly two cells remain open — $n = 8$ and $n = 9$ — and each
    is recorded at the grade it has actually reached.

    These results sit inside an exact decomposition of the deficit uniform in
    $n$ and $k$, from which the classical case $k = 2$ follows in a few lines
    with a machine-checked proof. We also formalise, for every
    $2 lt.eq k lt.eq n$, the confinement of any violator to a shrinking
    neighbourhood of the Birkhoff polytope, together with the Newton and
    Maclaurin inequalities that the confinement consumes, neither of which is
    in Mathlib. Kernel-checked results are cited by Lean declaration name at a
    pinned commit.
  ]
]

#v(0.8em)

= Introduction

Let
$ K_n = { A in RR^(n times n) : A_(i j) gt.eq 0, sum_(i,j) A_(i j) = n }, $
and for $A in K_n$ let $r$ and $c$ be its vectors of row and column sums. Write
$sigma_k (A)$ for the sum of the permanents of all $k times k$ submatrices of
$A$ — rows chosen from one $k$-subset, columns from another, independently — and
put
$ E_k (v) = frac(e_k (v), binom(n,k)), quad
  P_k (A) = frac(sigma_k (A), binom(n,k)^2), quad
  gamma(n,k) = frac(k!, n^k), $
with $e_k$ the elementary symmetric function. Write
$Phi_k (A) = E_k (r) + E_k (c) - P_k (A)$.

#block(fill: luma(250), inset: 10pt, radius: 3pt, width: 100%)[
  *The conjecture (Cheon and Hwang [1], 1992).* For every $A in K_n$ and every
  $1 lt.eq k lt.eq n$,
  $ Phi_k (A) lt.eq 2 - gamma(n,k), $
  with equality only at $A = J_n\/n$.
]

The endpoints are familiar. At $k = n$ one has $sigma_n = per$ and
$E_n (v) = product_i v_i$, so the statement is
$product_i r_i + product_j c_j - per(A) lt.eq 2 - n!\/n^n$: this is *Dittert's
conjecture* verbatim, Conjecture 28 of the Cheon–Wanless survey [5]. At $k = 1$
the inequality is an identity *on $K_n$* — not on all of $RR^(n times n)$ — since
the difference is a constant multiple of $sum_(i j) A_(i j) - n$; we note the
distinction because a test that treats it as a formal identity fails. The cases
$k lt.eq 2$ for every $n$, and every $k$ at $n lt.eq 3$, are known.

The interesting range is therefore $2 < k < n$, and it is that range which
appears to have gone untouched. This paper settles the whole line $k = 3$.

== Results

#keybox[
  *Theorem A ($k = 3$, every dimension).* For every $n gt.eq 4$ and every
  $A in K_n$,
  $ E_3 (r) + E_3 (c) - P_3 (A) lt.eq 2 - 6/n^3, $ <eq-thmA>
  with equality if and only if $A = J_n\/n$. More precisely, writing
  $norm(dot.c)_F$ for the Frobenius norm,
  $ (2 - 6/n^3) - [E_3 (r) + E_3 (c) - P_3 (A)]
      gt.eq theta_2 (n) dot.c norm(A - J_n\/n)_F^2, \
    "where" quad
    theta_2 (n) = frac(n^4 + 40 n^2 - 84 n + 40, n^5 (n-1)^3 (n-2)), $ <eq-thmA-stab>
  and $theta_2 (n) > 0$ for every $n gt.eq 4$.
  #v(0.4em)
  #leanline[Lean: `SubDittertK3.subDittert_k3_full`.]
]

The three statements are one statement. @eq-thmA-stab implies @eq-thmA because
$theta_2 (n) > 0$, and it implies the equality case because
$norm(A - J_n\/n)_F = 0$ only at $J_n\/n$; conversely $Phi_3 (J_n\/n) = 2 - 6\/n^3$
exactly. We state all three because the quantitative form is what the certificate
actually produces, and it is stronger than what the conjecture asks for: the
functional falls away from its maximum at least quadratically in the distance to
the maximiser, at an explicit rate. The constant $theta_2 (n)$ is not claimed
optimal; see @sec-uniqueness.

#claimbox[
  *Corollary B (two layers, stated as such).* With Hwang's theorem for Dittert at
  $n = 3$ [3], the case $k = 3$ of the Cheon–Hwang conjecture holds, with its
  equality case, for every $n gt.eq 3$. Since $k = 3$ requires $n gt.eq 3$, no
  dimension is left open on this line.
  #v(0.4em)
  #leanline[*This corollary is not a single-layer result and should not be cited
  as one.* The range $n gt.eq 4$ is Theorem A and is machine-checked
  (`SubDittertK3.subDittert_k3_full`). The remaining case $n = 3$ is Hwang's
  refereed theorem of 1987 [3], which we do not reprove in Lean. The corollary's
  support is therefore Lean *plus* the published literature, and it inherits
  whatever reliance one places on [3].]
]

Since $2 < 3 < n$ for every $n gt.eq 4$, Theorem A lies inside the intermediate
range. On the evidence of @sec-priority it is the first resolved case of the
Cheon–Hwang conjecture with $2 < k < n$. That is a priority claim rather than a
claim of difficulty, and @sec-priority records why it is perishable.

The certificate is a construction special to $k = 3$, but it sits inside a
decomposition that is not.

#keybox[
  *Theorem C (the deficit, decomposed uniformly in $n$ and $k$).* Write
  $A = J_n\/n + b$, let $R$ and $C$ be the row and column sums of $b$, and put
  $ s_d = frac([k]_d, [n]_d), quad t_d = s_d^2 dot.c frac((k-d)!, n^(k-d)) $
  with $[x]_d$ the falling factorial. Then for every $1 lt.eq k lt.eq n$,
  identically in $b$,
  $ (2 - gamma(n,k)) - Phi_k (A)
    = sum_(d=1)^k [ t_d dot.c sigma_d (b) - s_d dot.c (e_d (R) + e_d (C)) ]. $ <eq-universal>
  #v(0.4em)
  #leanline[Lean: `SubDittertUniversal.universal_identity`.]
]

@eq-universal is elementary, and no novelty is claimed for it: it is the
$sigma_k$ analogue of the classical expansion
$per(A + x J_n) = sum_j x^(n-j) (n-j)! thin sigma_j (A)$, combined with
$e_k (bold(1) + R) = sum_d binom(n-d, k-d) e_d (R)$. Its role here is that it
makes every $k$-dependence explicit and finite, so that statements which look
like separate facts at separate $k$ become instances of one identity. The
absence of a $d = 0$ term is the reason the constant $2 - gamma(n,k)$ is exactly
right, at every $n$ and $k$ at once.

#claimbox[
  *Theorem D ($k = 2$, every dimension).* For every $n gt.eq 2$ and every
  $A in K_n$, $ Phi_2 (A) lt.eq 2 - 2\/n^2. $
  With $kappa = 2\/(n(n-1))$ the deficit is a manifest sum of squares on the
  hyperplane $sum_(i j) b_(i j) = 0$:
  $ (2 - 2\/n^2) - Phi_2 (A)
    = 1/2 [ kappa^2 norm(b)^2 + kappa (1 - kappa) (norm(R)^2 + norm(C)^2) ]. $ <eq-k2sos>
  #v(0.4em)
  #leanline[Lean: `SubDittertK2.subDittert_k2`. *The statement is classical*
  (@sec-intermediate); the contributions are the derivation from @eq-universal
  and the machine-checked proof.]
]

Theorem D needs no Cauchy–Schwarz, no Gram matrix and no Maclaurin inequality:
@eq-k2sos falls out of @eq-universal at $k = 2$, and both coefficients are
non-negative for $n gt.eq 2$ because $kappa lt.eq 1$ there. Its interest is as a
control on the uniform machinery — it is the one case where that machinery can be
run end to end against an answer that is independently known — and, with
Theorem A, it makes the band $k in {2,3}$ complete.

Two further results are recalled rather than claimed. Both are formalised here,
and it is the formalisation, not the mathematics, that is ours.

#claimbox[
  *Theorem E (confinement; Cheon and Wanless [6], Theorem 2.1, at $k = n$;
  transferred to all $k$).* Let $2 lt.eq k lt.eq n$ and $A in K_n$. Then
  $ frac(norm(r - bold(1))^2 + norm(c - bold(1))^2, n(n-1)) - gamma(n,k)
    lt.eq (2 - gamma(n,k)) - Phi_k (A), $
  so any $A$ violating the Cheon–Hwang bound satisfies
  $ norm(r - bold(1))^2 + norm(c - bold(1))^2 lt.eq frac((n-1) k!, n^(k-1)). $
  #v(0.4em)
  #leanline[Lean: `SubDittertMaclaurin.theoremM'`, `SubDittertMaclaurin.confinement'`.]
]

At $k = n$ this is Theorem 2.1 of [6] in contrapositive form, with subset sums in
place of the $ell^2$ norm and a threshold of the same scale; that paper describes
its own result as significantly extending a result of Hwang, so the idea is older
still. Pang [9] runs the same argument at $k = n$ and refines the quantitative
step without changing its shape; that item is an unrefereed preprint. The only
part not found in the literature we checked is the transfer from the Dittert
functional to the whole Cheon–Hwang family uniformly in $k$, *and that is a
routine transfer of a known method*. It is formalised here for two reasons that
have nothing to do with novelty: it is elementary enough to check, and it is
uniform in $k$, so one Lean proof covers the whole family.

#claimbox[
  *Theorem F (Newton; Maclaurin).* For every real-rooted real polynomial and every
  admissible index, Newton's inequality holds; in vector form, for
  $v in RR^n$ and $1 lt.eq j lt.eq n-1$,
  $ e_(j-1)(v) thin e_(j+1)(v) binom(n,j)^2
    lt.eq e_j (v)^2 binom(n,j-1) binom(n,j+1), $
  with no positivity hypothesis. Consequently, for $v gt.eq 0$ with
  $sum_i v_i = n$ and $2 lt.eq k lt.eq n$, $E_k (v) lt.eq E_2 (v)$.
  #v(0.4em)
  #leanline[Lean: `NewtonIneq.newtonAt_all`, `NewtonIneq.newton_esymF`,
  `NewtonIneq.pnorm_le_two`. *Classical mathematics*; the contribution is the
  formalisation.]
]

The telescoped form $E_k lt.eq E_2$ carries no fractional powers, unlike the
usual $E_k^(1\/k) lt.eq E_2^(1\/2)$; that is what makes it the statement to
formalise, and it is exactly what Theorem E consumes. Neither Newton's
inequalities nor Maclaurin's inequality is in Mathlib v4.14.0, whose
`NewtonIdentities` file carries Newton's *identities* only.

The remaining results move off the line $k = 3$. The first lives on the doubly
stochastic polytope and is a quantitative form of a theorem conjectured by
Tverberg [17] and proved by Friedland [18]: $sigma_k$ on $Omega_n$ attains its
minimum only at the barycentre. The second consumes it.

#keybox[
  *Theorem G (stability of the Tverberg–Friedland minimum).* Let
  $2 lt.eq k lt.eq 5$ and let $n$ satisfy
  $ n gt.eq 2 " at " k=2, quad n gt.eq 4 " at " k=3, quad
    n gt.eq 8 " at " k=4, quad n gt.eq 14 " at " k=5. $
  Then for every doubly stochastic $n times n$ matrix $A$,
  $ sigma_k (A) - binom(n,k)^2 frac(k!, n^k)
    gt.eq binom(n,k)^2 thin c(n,k) thin norm(A - J_n\/n)_F^2,
    quad c(n,k) = frac(k(k-1) thin k!, 4 n^k (n-1)^2). $ <eq-thmG>
  The constant is optimal to within a factor two (@sec-stab-sharp), and the
  cell $(k,n) = (3,3)$ is a genuine exception with an explicit witness
  (@sec-stab-exception).
  #v(0.4em)
  #leanline[Support, split by cell. *Kernel-checked* at $(k=2,$ every
  $n gt.eq 2)$ and $(k=3,$ every $n gt.eq 4)$ — Lean: `stabilityAt_two` and
  `stabilityAt_three` in `StabilityK3.lean` at commit `1507013` — and at
  $(k=4,$ every $n gt.eq 8)$ — Lean: `stabilityAt_four` in
  `StabilityK4.lean` at commit `944b517` — in each case the whole range
  Theorem G states for that $k$, with no arithmetic gap. *Written proofs
  plus the exact verifier of @sec-stab-verify* at $(k=5, n gt.eq 14)$: no
  `stabilityAt_five` exists. @sec-stab-lean states the division precisely,
  with the checks that keep it honest, and states two limits of the $k = 4$
  formalisation that must not be over-read.]
]

#keybox[
  *Theorem H ($k = 4$, every $n gt.eq 10$).* For $k = 4$ and every
  $n gt.eq 10$, $Phi_4 (A) lt.eq 2 - 24\/n^4$ for every $A in K_n$, with
  equality only at $A = J_n\/n$.
  #v(0.4em)
  #leanline[Support: written proofs (@sec-k4) plus the exact verifier
  `graded_verify_k4.py`, which recomputes every displayed quantity of that
  part over $QQ$ with no floating-point arithmetic in any decision, and parses
  the sensitivity table of @sec-k4-insens out of this document so that
  displayed and checked cannot drift apart. *Not formalised*;
  @sec-k4-statement states the scope exactly.]
]

#claimbox[
  *Insensitivity of the threshold (a verified sensitivity computation, not a
  theorem).* Write $q_i (z) lt.eq c thin (1 - 1\/n)$ for the collar bound on
  the row squared norms of the doubly centred block, $c gt.eq 1$ the one
  unsettled constant of the $k = 4$ argument. At each of the ten values
  $c in {1.00, 1.25, 1.50, 1.58, 1.63, 2.00, 2.34, 2.53, 3.00, 4.00}$ the
  honest threshold is recomputed exactly over $QQ$, and it equals $10$ at
  every sampled value inside the admissible band
  $1.58 lt.eq c lt.eq 2.53$, whose ends are the smallest constructed
  violation and the proved collar cap. A mechanical audit — every budget
  line recomputed at $c$ and $2c$, at $n = 10$ and $n = 16$, the run
  aborting on any change — asserts that exactly three budget lines depend on
  $c$, one linearly and two through $sqrt(c)$, and that no other line moves.
  #v(0.4em)
  #leanline[Support: the named $c$-set plus that structural audit, both under
  the verifier of @sec-k4-verify; no claim is made for unsampled $c$, and
  the grade sentence is the claim. This computation is why we regard
  Theorem H's threshold as stable: no sampled admissible value moves it, and
  the audited structure names the only places $c$ can act.]
]

Between Theorem A's line and Theorem H's range sit the five cells
$(k = 4, 5 lt.eq n lt.eq 9)$, covered by neither theorem. Three of them are
settled by fixed-dimension certificates at full anchor grade — $(5,4)$,
$(6,4)$ with $Phi_4 lt.eq 107\/54$ on $K_6$, and $(7,4)$ with
$Phi_4 lt.eq 4778\/2401$ on $K_7$ — so the open cells on the line $k = 4$
are exactly $n = 8$ and $n = 9$. @sec-k4-anchors records all five cell by
cell, each at the grade it has actually reached; @sec-k4-statement states
the honest gap rather than leaving it to be inferred.

== Support layers <sec-layers>

Every result above is stated with the layer it rests on, because in this corner
of the literature the distinction has recently been expensive.

- *Theorems A and C–F are proved in Lean 4*, on Lean's standard axioms, with no
  `sorry` anywhere in the development and no use of `native_decide`. @sec-lean
  states the verification standard precisely and pins it to a commit. Theorem A
  is Lean-proved in all three parts, equality case and stability bound included.
- *Theorem G splits by cell*: kernel-checked at $k = 2, 3$
  (`StabilityK3.lean`, commit `1507013`) and at $k = 4$ (`StabilityK4.lean`,
  commit `944b517`), in each case over the whole stated range; written proofs
  plus the exact verifier `graded_verify_stability.py` at $k = 5$.
  @sec-stab-lean is the precise statement, and the verifier checks that
  statement itself against the Lean sources at the pinned commits.
- *Theorem H is not formalised.* Its support is written proofs plus the
  exact verifier `graded_verify_k4.py`; every quantity displayed in @sec-k4
  is recomputed over $QQ$, and the sensitivity table is parsed out of this
  document rather than restated. The insensitivity claim beside it is a
  verified sensitivity computation, graded in its own statement.
- *Corollary B* rests on Theorem A for $n gt.eq 4$ and on the published
  literature at $n = 3$.
- *The fixed-dimension certificates of @sec-anchors are not Lean-checked.* They
  are exact rational data accepted by an independent standalone verifier. They
  are recorded as anchors; no theorem above depends on them, and the cell
  $(5,4)$ among them is one of the per-cell records of @sec-k4-anchors.
- *@sec-computational is computational evidence, not a theorem of this paper*,
  and is not Lean-checked. Its verdicts are exact rational computations with
  stored witnesses.
- *Nothing here is refereed*, including this paper. Exact verification and
  machine checking are different things from refereeing, and weaker ones.

= The state of the line, and of the neighbouring endpoint <sec-priority>

== The $k = n$ endpoint moved in one week, publicly and unrefereed

Dittert's conjecture is the endpoint of the same family, and its status changed
sharply in July 2026. Only two dimensions rest on refereed work: $n = 2$
(Sinkhorn [4]) and $n = 3$ (Hwang [3]). Everything else that is currently
claimed is either an unrefereed preprint or a public code repository:

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, left),
    stroke: 0.4pt + luma(180),
    table.header([*dimensions*], [*claimed by*], [*status*]),
    [$n = 2$], [Sinkhorn [4], 1984], [refereed],
    [$n = 3$], [Hwang [3], 1987], [refereed],
    [$n = 4$], [Divya K. U. and Somasundaram, arXiv:2312.00464],
      [*claim withdrawn in the published version* [8]],
    [$n = 4$], [public repository [11], 21 Jul 2026], [public, dated, unrefereed],
    [$n = 4, 5, 8$–$16$], [public repository [11], 23 Jul 2026],
      [public, dated, unrefereed],
    [$n = 6$–$15$], [public repositories [11], 24–25 Jul 2026],
      [public, dated, unrefereed],
    [$n = 16$], [Kafidov [10], arXiv:2607.19439, 21 Jul 2026], [preprint, no DOI],
    [$n gt.eq 17$], [Pang [9], arXiv:2606.01531, 1 Jun 2026], [preprint, no DOI],
  ),
  caption: [Public dated claims on Dittert's conjecture ($k = n$), as of
    28 July 2026. Refereed status is stated as it is, not as one would like it.]
)

Two features of the table bear on how the present paper should be read. At the
28 July 2026 sweep none of the repositories listed [11] had a corresponding
preprint or journal article, so the indexed literature does not on its own
record the state of this conjecture. And the record moves in both directions: the v1 abstract of
arXiv:2312.00464 claims Dittert at $n = 4$, while the published version in
_Special Matrices_ *12* (2024) [8] contains no such claim; the preprint record
still shows v1.

None of the unrefereed items is asserted here to be wrong. They are public and
dated, which is what matters for priority, and none of them is refereed, which
is what matters for reliance.

One of them warrants a sentence of positioning. Taken together, the
repository claims of [11] and the two preprints [9, 10] assemble a claim on
Dittert's conjecture *itself*, in full — the `pedromnasc` repository presents
exactly such an assembly — and no part of that assembly has been refereed,
nor has the assembly as a whole. This paper takes no view on its correctness.
The contrast in scope discipline is deliberate: every priority claim made here
is narrowed to what the Lean development and the exact verifiers actually
carry, at the grade each part actually has, and the grades are stated claim by
claim rather than inherited from the strongest part.

== The intermediate range $2 < k < n$ <sec-intermediate>

The generalisation itself has attracted almost nothing. The Cheon–Hwang paper [1]
has five citing papers — Cheon and Wanless 2012 [6], Cheon and Wanless 2007 [7],
the Cheon–Wanless survey [5], and Cheon and Yoon 2006 and Cheon 1993 (both
[12]) — and none of them works on the generalisation. Reference [6] says only that
Cheon and Hwang "posed a problem generalising the Dittert conjecture"; its own
results concern partly decomposable matrices and asymptotics. To our knowledge
neither the literature nor any public code repository carries a result on the
intermediate range; the closest item is the one described next.

The one adjacent effort is a `subdittert/` package inside one of the repositories
of [11]. Its README is explicit about scope, and we quote it verbatim:

#block(fill: luma(250), inset: 10pt, radius: 3pt, width: 100%)[
  "The endpoint `k=n` is Dittert's problem. The cases `k<=2` are historically
  known. This package does *not* claim the unresolved intermediate cases."
]

That quotation is also the clearest available statement of the prior status of
Theorem D: $k lt.eq 2$ is historically known, for every $n$, and we claim no
novelty for the statement. Its results are $k = n-1$ for $18 lt.eq n lt.eq 80$,
$k = n-2$ for $18 lt.eq n lt.eq 40$, and a table over 425 pairs with
$17 lt.eq n lt.eq 40$ — and all three are conditional on the package's own
"positive Li-scaling structural hypothesis": its README states the $k = n-1$
Hall-cut exclusion "with" that hypothesis, the $k = n-2$ exclusion "subject to
the same structural hypothesis", and the 425-pair table conditional on both it
and the package's other intermediate cases. What is unconditional there is a
Sturm-certified floor on the one-zero Birkhoff face at each order. Note that
$(n,k) = (4,3)$ *is* a $k = n-1$ case, so that package works the same diagonal —
but from $n = 18$ upward, by a large-$n$ scaling argument that cannot reach
$n = 4$, and conditionally throughout. It does not intersect the line $k = 3$
except at $n = 4$, which it excludes.

One item is flagged rather than paraphrased: Cheon and Wanless 2007 [7] is
paywalled and was not obtained, and is reported to settle $n lt.eq 3$ for all
$k$. Nothing in this paper depends on it: Corollary B takes $n = 3$ from Hwang
[3], and @sec-anchors reproves it by certificate.

= The decomposition, and the case $k = 2$ <sec-universal>

Theorem C is proved by reading the two definitions and dividing. Since
$A = J_n\/n + b$ has row sums $bold(1) + R$,
$e_k (bold(1) + R) = sum_d binom(n-d, k-d) e_d (R)$; and since a term of a
permanent is a bijection,
$sigma_k (J_n\/n + b) = sum_d binom(n-d, k-d)^2 (k-d)! thin n^(-(k-d)) sigma_d (b)$.
Dividing by $binom(n,k)$ and $binom(n,k)^2$ turns $binom(n-d,k-d)\/binom(n,k)$
into $[k]_d\/[n]_d = s_d$. The $d = 0$ terms are $1$, $1$ and $gamma(n,k)$, which
cancel the constant $2 - gamma(n,k)$ exactly; that cancellation is why the sum
in @eq-universal starts at $d = 1$.

Three consequences are worth naming, because each has been observed separately in
this family and each is the same identity read at one degree. At $d = 1$ the
gradient of the deficit at $J_n\/n$ is $(-2k\/n + k dot.c k!\/n^(k+1)) bold(1)$,
so $J_n\/n$ is critical for every $(n,k)$. At $d = 2$ the Hessian has exactly two
distinct eigenvalue parameters, $s_2 = k(k-1)\/(n(n-1))$ and
$t_2 = s_2^2 (k-2)!\/n^(k-2)$, again for every $(n,k)$. And the coefficient of a
degree-$d$ monomial of the deficit takes one of three values — $-2 s_d + t_d$ if
the cells form a partial permutation, $-s_d$ if they have distinct rows or
distinct columns but not both, and $0$ otherwise — so three numbers per degree
describe the whole objective, whatever $k$ is. The closed forms used in
@sec-closedform are the case $k = 3$ of that rule.

At $k = 2$ the sum has two terms and both are computable in closed form. Using
$2 sigma_2 (b) = (sum b)^2 - norm(R)^2 - norm(C)^2 + norm(b)^2$ and
$2 e_2 (R) = (sum R)^2 - norm(R)^2$, and restricting to $sum b = 0$, the deficit
collapses to @eq-k2sos, which is Theorem D. The identity was checked against the
objective built from the 1992 definition in exact rational arithmetic at
$n = 2, dots, 6$, four random $b$ per $n$ on the hyperplane, with no mismatches;
the Lean proof of `subDittert_k2` goes through @eq-universal and does not use that
check.

The same route does not reach $k = 3$. There the deficit is not a sum of squares
on the hyperplane, and the certificate of @sec-cert is needed.

= The objective at $k = 3$, and how we know it is the right one <sec-objective>

A certificate for the wrong polynomial is worthless and looks identical to a
certificate for the right one, so the construction of the objective is checked
before anything else. In centred coordinates $b = A - J_n\/n$ put
$ F(b) = (2 - gamma(n,k)) - [E_k (r) + E_k (c) - P_k (A)], $
a polynomial of degree $k$ over $QQ$; the conjecture at $(n,k)$ is $F gt.eq 0$
on $K_n$. Five independent tests are run on the construction, all passing:

+ *$sigma_k$ by two structurally different algorithms.* One enumerates all
  $binom(n,k)^2$ pairs of index sets and sums $k!$ products. The other never
  forms a submatrix at all: it uses
  $per(A + x J_n) = sum_j x^(n-j) (n-j)! thin sigma_j (A)$ in $QQ[x]$, with the
  order-$n$ permanent by Ryser inclusion–exclusion over column subsets. Forty
  random rational matrices agree, for $2 lt.eq n lt.eq 5$ and every $k$.
+ *Symbolic against from-scratch* evaluation at random rational points, at
  $(3,2)$, $(4,3)$, $(4,4)$ and $(5,3)$.
+ *A $k = n$ positive control.* The polynomial built here at $(4,4)$ is compared
  coefficient by coefficient with the one from an independent Dittert pipeline:
  1040 monomials each — that is the number carrying a non-zero coefficient in
  the degree-4 objective, out of the 4845 of degree at most $4$ in the sixteen
  entries — and zero differing coefficients. That pipeline already underlies a
  verified certificate, so it is ground truth rather than a mirror.
+ The numerical trap of @sec-trap, explicitly separated.
+ $k = 1$ is confirmed to be an identity on $K_n$, and equality at $J_n\/n$ is
  confirmed for every tested $(n,k)$.

== Two coincidences that make the bound useless as a check <sec-trap>

#warnbox[
  $2 - gamma(4,3) = 2 - 6\/64$ and $2 - gamma(4,4) = 2 - 24\/256$ are *both*
  $61\/32$. The same collision recurs at $n = 5$:
  $2 - gamma(5,4) = 2 - gamma(5,5) = 1226\/625$, which is the published Dittert
  value at $n = 5$. So seeing the right constant is *no evidence whatsoever*
  that the $k = 3$ or $k = 4$ code is doing what it claims.
]

The two cases are separated by comparing whole polynomials rather than
constants. At $n = 4$ the $k = 3$ and $k = 4$ objectives have degrees 3 and 4;
their supports together carry 1040 monomials — the $k = 3$ support, 552
monomials, sits inside the $k = 4$ one — and the two disagree at every one of
the 1040. At $n = 5$ the same comparison spans 14005 monomials, degrees 4 and 5,
again disagreeing at all of them.

= The certificate <sec-cert>

== Form

In centred coordinates the ansatz is
$ F(b) = sigma_0 (b) + sum_p (1/n + b_p) thin sigma_p (b)
  + lambda(b) dot (sum_q b_q), $ <eq-ansatz>
where $sigma_0$ and every $sigma_p$ is a sum of squares and $lambda$ is a free
polynomial. On $K_n$ the last term vanishes, since $sum_q b_q = 0$ there, and
every $1\/n + b_p = A_p gt.eq 0$; so the right side is a sum of non-negative
terms and $F gt.eq 0$ on $K_n$, which is the theorem.

The shape is Putinar's [2]: one sum-of-squares multiplier for each defining
inequality $A_p gt.eq 0$, a free multiplier for the equality $sum_q b_q = 0$,
truncated at a fixed degree. No existence theorem is invoked. Putinar's applies
to polynomials *strictly* positive on the set, and $F$ vanishes at $J_n\/n$, in
the relative interior of $K_n$; the representation is exhibited, not deduced,
and the work is in getting it at the degree $F$ already has.

The toolset sits in a standard line: sum-of-squares relaxations of polynomial
optimisation are Lasserre's hierarchy [13], and exploiting a symmetry group to
block-diagonalise the Gram matrix is Gatermann–Parrilo [14]; both are used here
in their plain forms. What is not taken from that line is the coefficient
field: the programme is posed and solved over $QQ(n)$ — one symbolic solve
whose output is a certificate for every $n$ at once, with positivity of the
resulting rational functions decided by Sturm sequences rather than per-$n$
numerics. Optimisation uniform in the dimension is itself an active area —
Levin and Chandrasekaran [15] develop any-dimensional polynomial optimisation
via de Finetti theorems — and @sec-computational's band law is this paper's
measured answer, for one problem family, to when such uniformity survives at
fixed certificate degree.

*Why the degree closes.* Here $deg F = k$, not $n$. At $k = 3$ a Gram basis of
degree $1$ gives $deg sigma lt.eq 2$ and $deg (sigma_p b_p) lt.eq 3$, matching
$deg F$ exactly with no surplus top band to cancel. The Gram matrices are
$n^2 times n^2$. This is the structural reason the whole line $k = 3$ is
accessible while a fixed $k = n$ is not: in the Dittert case the objective's
degree grows with the dimension and the ansatz cannot follow it.

*Why rounding works.* The standing obstruction to exact rational rounding is
that a tight bound forces a singular optimal Gram. Here the Hessian of $F$ at
$J_n\/n$ restricted to the tangent space $\{sum X = 0\}$ is positive definite —
at $(4,3)$ its characteristic polynomial on the projected space is exactly
$x (x - 1\/16)^9 (x - 29\/16)^6$ over $QQ$, and the multiplicities $9 = (n-1)^2$
and $6 = 2(n-1)$ are forced by Schur's lemma, since the tangent space is
$(V|1) directsum (1|V) directsum (V|V)$ with transposition fusing the first
two. So there is no forced kernel inside the tangent space: centring at the
extremiser and excluding the constant monomial removes the only degenerate
direction.

== Symmetry reduction, and the fact that its shape is fixed in $n$

The problem is invariant under $(S_n times S_n) : ZZ_2$ acting by row
permutations, column permutations and transposition. Reducing @eq-ansatz by that
group leaves, *at every $n$ alike*:

#figure(
  table(
    columns: (auto, auto),
    align: (left, left),
    stroke: 0.4pt + luma(180),
    table.header([*object*], [*count, independent of $n$*]),
    [orbit constraint rows], [$1 + 1 + 3 + 7 = 12$, of rank $11$ over $QQ(n)$],
    [$sigma_0$ variables], [$3$],
    [$sigma_11$ variables], [$11$],
    [$lambda$ variables], [$5$],
    [cone size], [$n^2$ (the only thing that grows)],
  ),
  caption: [The symmetry-reduced program at $k = 3$ with a degree-1 Gram basis.]
)

Nineteen unknowns and twelve equations, at $n = 4$, $n = 5$, $n = 6$ and beyond.
This is representation stability, and here — unlike in the $k = n$ case, where
the same stability is undercut by the growing degree — there is no counteracting
obstruction. That observation is what makes a single symbolic solve plausible;
the rest of the paper is the work of turning it into a proof.

One implementation point matters for reaching large $n$ at all. The transporter
carrying the corner orbit to position $(i,j)$ is the explicit product of the row
transposition $(0 thin i)$ with the column transposition $(0 thin j)$, at cost
$O(n^2)$; enumerating the group instead costs $2(n!)^2$, which is
$5.1 times 10^7$ already at $n = 7$. The reduced system is provably unchanged,
because two transporters differ by an element of the stabiliser of $(0,0)$,
which preserves each $sigma_11$ orbit.

= The uniform certificate <sec-general>

== The constraint system in closed form, over $QQ(n)$ <sec-closedform>

Both halves of the $12 times 19$ system are *derived* as functions of $n$, not
interpolated; "no fit is used anywhere" is a stronger statement than "the fit was
validated".

*The right-hand side.* The coefficient in $F$ of an arbitrary monomial is closed
form for all $n$ at once. Writing $d$ for the degree of the monomial and reading
the two definitions directly,
```
[monomial] e_k(r)    = C(n-d, k-d)   if the d cells lie in distinct ROWS, else 0
[monomial] sigma_k   = C(n-d, k-d)^2 (k-d)! n^{-(k-d)}
                                     if the cells form a PARTIAL PERMUTATION, else 0
```
because within one product $r_i r_j r_k$ no index repeats, so two cells in a row
cannot occur; and a term of a permanent is a bijection, so the cells must have
distinct rows *and* distinct columns. This is the case $k = 3$ of the coefficient
rule of @sec-universal. Checked against the fully expanded
objective at $n = 4, 5, 6$: 969, 3276 and 9139 monomials, no mismatches. Those
counts are of *every* monomial of degree at most 3 in the $n^2$ entries, absent
ones included — the closed form has to return zero exactly where the expanded
objective has no term, so the check is over the whole coefficient vector and not
over the support. As a
sanity check it gives the degree-one coefficient as $-6\/n + 18\/n^4$, which at
$n = 4$ is $-183\/128$, the gradient value computed independently.

*The orbit sizes.* By orbit–stabiliser,
$|"orbit"(P)| = 2 dot [n]_r dot [n]_c \/ |"Stab" P|$ with falling factorials, and
$|"Stab" P|$ found by brute force over at most $2 dot 3! dot 3! = 72$
relabellings. A multiset of at most three cells meets at most three rows and
three columns, so every orbit size is a polynomial in $n$ of degree at most $6$.
Checked against brute-force enumeration at $n = 4, 5, 6, 7$, including the
stabiliser case: no mismatches.

The structure that makes this work is that with a degree-1 basis the product
$"basis"[u] dot "basis"[v]$ *is* the pair $\{u,v\}$, so the $sigma_0$ variable
orbits and the constraint-row orbits are the same objects; and canonicalisation
is equivariant, so both incidence blocks are an orbit size times a $0\/1$
incidence.

*Cross-check against the trusted path.* The symbolic system was compared entry
by entry, right-hand side included, with the system built by the original code
path — the one that produced the already-verified fixed-$n$ certificates — at
$n = 4, 5, 6$. No mismatches. The two share no logic: one does union–find over
every monomial of the expanded objective, the other evaluates closed forms.

Row-reducing over the field $QQ(n)$ gives: 12 equations, 19 unknowns, rank 11,
one dependent row, *consistent*, with an 8-dimensional affine family of
solutions. So the linear half of the certificate exists at every $n$ at once.

== Definiteness reduces to ten rational functions of $n$ <sec-blocks>

What remains is to choose within that family so that both Gram matrices are
positive definite for every $n gt.eq 4$. Both are block-diagonalised *in closed
form* — a numerical basis at one $n$ could not settle all $n$.

*$sigma_0$.* Its Gram is $a I + b A_1 + c A_2$ in the Bose–Mesner algebra of the
rook's graph $K_n square K_n$, so it has exactly three eigenvalues:
$ theta_0 = a + 2(n-1)b + (n-1)^2 c & quad "multiplicity" 1, \
  theta_1 = a + (n-2)b - (n-1)c & quad "multiplicity" 2(n-1), \
  theta_2 = a - 2b + c & quad "multiplicity" (n-1)^2. $

*$sigma_11$.* With $V'$ the standard $(n-2)$-dimensional representation of
$S_(n-1)$ one has
$RR^(n^2) = 4(1|1) directsum 2(V'|1) directsum 2(1|V') directsum (V'|V')$,
and transposition fuses $(V'|1)$ with $(1|V')$ and splits the four-dimensional
trivial multiplicity space as $3 + 1$. The blocks are a $3 times 3$ (call it
$A$), a $1 times 1$ sign block $B$, a $2 times 2$ block $C$ of multiplicity
$2(n-2)$, and a $1 times 1$ block $D$ of multiplicity $(n-2)^2$.

Both consistency checks pass: $sum d(d+1)\/2 = 6 + 1 + 3 + 1 = 11$, the number of
orbit parameters, and $3 + 1 + 2 dot 2(n-2) + (n-2)^2 = n^2$. The decomposition
was verified against a direct eigendecomposition of the assembled
$n^2 times n^2$ matrix on *random* orbit coefficients at $n = 4, dots, 8$ — full
spectrum against the union of block spectra with predicted multiplicities, worst
discrepancy $1.4 times 10^(-13)$. Random coefficients matter here: a check run on
the real certificate could pass by accident on a matrix carrying extra structure.

#claimbox[
  *Consequence.* Positive definiteness of both Grams, for all $n gt.eq 4$, is
  exactly the positivity of *ten* explicit rational functions of $n$: the three
  $sigma_0$ eigenvalues, the three leading principal minors of $A$, the block
  $B$, the two leading minors of $C$, and the block $D$.
]

One of these ten is not independent of the rest: the block $D$ equals
$theta_2 \/ n$ *exactly*, an identity of rational functions rather than a
coincidence at sampled $n$ — the two share the same numerator and differ only
by a factor of $n$ in the denominator. So positivity of $D$ follows
immediately from positivity of $theta_2$ together with $n > 0$, and the
certificate rests on *nine* independent positivity facts, not ten; $D$ is
carried along as a consequence rather than an additional condition. We report
and certify all ten regardless — Sylvester's criterion asks for all ten
directly, and the Sturm and Lean machinery below decides each on the same
uniform footing — but a reader should not credit the certificate with ten
independent facts where nine suffice.

These ten were validated first on the independently produced, already-verified
certificates at $n = 4, 5, 6$: all ten strictly positive in each case.

== The geometry of the feasible set <sec-design>

Choosing the eight free variables as functions of $n$ is the whole difficulty,
and the shape of the difficulty is not the obvious one.

*The feasible set is unbounded, and the recession cone is exactly
two-dimensional.* It is derived, not probed. A recession direction is a
homogeneous solution with the sigmas still positive semidefinite; on the
hyperplane $sum b = 0$ every term of @eq-ansatz is non-negative on $K_n$, so each
vanishes there, and a sum-of-squares quadratic form vanishing on a hyperplane has
Gram $bold(1) u^T + u bold(1)^T$, which is positive semidefinite only for $u$ a
non-negative multiple of $bold(1)$. Hence the recession cone adds $c_0 J$ to the
$sigma_0$ Gram and $c_1 J$ to the $sigma_11$ Gram, $c_i gt.eq 0$, with $lambda$
determined. This was confirmed as an exact kernel element over $QQ(n)$ with a
round trip through the free coordinates.

*The lineality space is larger, and it is what makes optima drift.* The
quantities that actually have to be controlled need $G$ and $H$ positive
semidefinite only on $bold(1)^perp$, which gives $G = bold(1)u^T + u bold(1)^T$
and $H = bold(1)v^T + v bold(1)^T$ with $u$ forced to a multiple of $bold(1)$ by
transitivity but $v$ free on the three stabiliser classes. Its four generators
have an invertible $4 times 4$ minor on the four free $lambda$ columns, so the
lineality space is exactly the $lambda$ reparametrisation, and
$\{f_15 = f_16 = f_17 = f_18 = 0\}$ is a transversal slice. On that slice the
recession cone is trivial and *the feasible set is compact*. The essential design
problem has *four* unknowns. Numerically, drift along the lineality space is
plainly visible: the scaled free variable $f_6 n^3$ takes the values
$149, 20.3, 9.69, 35311, 13.3, 83681, 6.66$ at
$n = 20, 50, 100, 200, 500, 1000, 2000$, which no curve in $n$ will follow.

*The essential set is a sliver, and that is why no fit can hold it.* In the
scaled coordinates $beta = f dot n^3$, four of the ten quantities are differences
of terms of size $n^2$ or $n^3$ that must cancel down to $O(1)$. Working the
cancellations out forces
$ beta_6 - 2 beta_9 = O(n^(-2)), quad
  beta_12 - (2 beta_9 - 1) = O(n^(-1)), quad
  beta_11 - 2 beta_12 - 2 = O(n^(-1)), $
the last pinned to $O(n^(-3))$; asymptotically
$beta arrow.r (2b, b, 4b, 2b-1)$, a one-parameter family with
$1\/2 < b < 1$, with the analytic centre at $b approx 0.8486$. A least-squares
fit whose residual is small against the diameter of the essential set is still
far outside it, and a relation pinned to $O(n^(-3))$ is beyond the reach of
curve fitting at any degree.

== Adapted coordinates, and one exact elimination <sec-fix>

Write the cancellations into the coordinates, so that they happen symbolically
rather than numerically:
$ beta_9 = b, quad beta_6 = 2b + x/n^2, quad
  beta_12 = 2b - 1 + y/n, quad beta_11 = 2 beta_12 + 2 + z/n. $

Then *solve for $z$ exactly over $QQ(n)$ from the equation $theta_2 = D$*, rather
than fitting it. This is the step that makes the difference. The two quantities
are affine in $z$ with opposite-sign coefficients of size $n^2$, and the window
between them has width $O(n^(-2))$; at $n = 10^6$ a numerical fit would need
twelve correct digits merely to stay inside. With $z$ eliminated, the remaining
parameters carry $Theta(1)$ coefficients and an ordinary semidefinite program
over a grid of $n$ finds them. The answer is simple:

#keybox[
  $ b = 1, quad x = 8 + 20/n, quad y = -2 - 10/n, $
  $ z = frac(6n^7 - 28n^6 + 41n^5 - 28n^4 + 48n^3 - 164n^2 + 208n - 80,
            n^7 - 7n^6 + 19n^5 - 25n^4 + 16n^3 - 4n^2). $
]

The window $1\/2 < b < 1$ of @sec-design and the choice $b = 1$ here are not in
conflict, and the gap between them is worth naming. That window constrains the
*limit* of the scaled quantities; the certificate is not the limit point. Its
finite-$n$ corrections — $x\/n^2$ and $y\/n$ above, and $z$ solved exactly —
are what carry the four tight quantities, and they are non-zero at every finite
$n$. What the endpoint costs is margin, not sign: $theta_2$ decays like
$n^(-5)$. Positivity is then decided at every $n gt.eq 4$ by the Sturm step of
@sec-sturm, which acts on the exact rational functions and is indifferent to how
small the margin becomes.

The transferable form of this step is short. In a family of certificates indexed
by a parameter, identify the tight direction and eliminate it symbolically; fit
only the slack ones. Quotienting the lineality space out is necessary — without
it the optima drift and nothing converges — but it is not sufficient, because the
compact essential set that remains can still be a sliver.

Two of the ten quantities cost nothing, because they are pure gauge. Moving along
the lineality space adds $mu n^2$ to $theta_0$ and $s w^T + w s^T$ to the block
$A$, with $s = (1, 2(n-1), (n-1)^2)$ and $w$ free in $RR^3$; choosing $w$ so that
$A$ becomes $"diag"(gamma, T^T A T)$ in a basis $(e, T)$ with $e = (1,0,0)$, and
taking $gamma = 1\/n^3$ and $theta_0 = 1\/n$, reduces $A succ 0$ to
$T^T A T succ 0$, which is already one of the essential conditions. No new
positivity requirement appears.

The resulting nineteen certificate variables are exact rational functions of $n$;
they are recorded in full in the accompanying material and are not reproduced
here. Three of them are $1\/n^3$ exactly; the largest has numerator of degree 9
and denominator of degree 12.

== Obstructions to simpler designs <sec-negative>

Four routes that a reader would otherwise try are closed, each by an exact
rational witness.

- *Linear programming for the design step is infeasible*, at ansatz degrees
  $D = 0, 1, 2, 3, 4$ (8 to 40 unknowns, 350–458 coefficient rows). The blocker
  is not the ansatz: plain diagonal dominance *fails on the already-verified
  certificates* at $n = 4, 5, 6$, in row 0 of both the $3 times 3$ and the
  $2 times 2$ block, so no LP built on dominance can be feasible. The cause is
  scaling — the isotypic vectors are unnormalised, so diagonal entries differ by
  orders of magnitude — and a rescaling does exist (both blocks are H-matrices at
  the verified certificates), but the weights that work are read off the
  certificate that the LP is trying to choose. The design step is *bilinear* in
  weights and certificate, not linear.
- *Least squares through analytic centres*, at degrees 1 to 7, fails off-grid at
  $n = 17$, $n = 71$ and $n = 811$ — always between grid points, always on a
  tight quantity.
- *Pinning four entries to constant targets* fails for all 210 four-subsets. The
  centre's own entries move by a factor of four between $n = 4$ and
  $n = infinity$, so constant targets pull the solution out of the set at one end
  or the other. Separately, the subset $\{theta_2, D, C_(01), T_(01)\}$ is exactly
  singular over $QQ(n)$; 197 of the 210 are non-singular.
- *Restricting $lambda$ to be a sum of squares* is sound, since $lambda$
  multiplies an equality constraint, but it removes only the two-dimensional
  recession cone and not the four-dimensional lineality space that causes the
  drift.

== Sturm certification of all ten quantities <sec-sturm>

Substituting $n = m + 4$ turns each quantity into a ratio of polynomials in $m$
with the range becoming $m gt.eq 0$. The sign of each denominator on that range
is *checked*, not assumed. The numerator's positivity on $[0, infinity)$ is then
decided — decided, not estimated — by a Sturm chain on the squarefree part,
comparing sign variations at $0$ and at $+infinity$. There is no sufficiency gap
in this step, which is precisely why the tempting shortcut "all coefficients
non-negative in $m$" is only a heuristic: $m^2 - m + 1$ is positive everywhere
and has a negative coefficient.

#figure(
  table(
    columns: (auto, auto, auto, auto, auto),
    align: (left, right, center, center, center),
    stroke: 0.4pt + luma(180),
    table.header([*quantity*], [*sqfree deg*], [$V(0)$], [$V(infinity)$],
      [*roots in $(0,infinity)$*]),
    [`G0.theta0`], [constant $1$], [—], [—], [$0$],
    [`G0.theta1`], [$6$], [$1$], [$1$], [$0$],
    [`G0.theta2`], [$4$], [$1$], [$1$], [$0$],
    [`H.A minor1`], [constant $1$], [—], [—], [$0$],
    [`H.A minor2`], [$5$], [$1$], [$1$], [$0$],
    [`H.A minor3`], [$13$], [$3$], [$3$], [$0$],
    [`H.B`], [$5$], [$2$], [$2$], [$0$],
    [`H.C minor1`], [$5$], [$1$], [$1$], [$0$],
    [`H.C minor2`], [$12$], [$2$], [$2$], [$0$],
    [`H.D`], [$4$], [$1$], [$1$], [$0$],
  ),
  caption: [All ten quantities, positive for every $n gt.eq 4$. Each row is a
    complete decision, not a sample: no roots in $(0,infinity)$ and a positive
    value at $m = 0$. `H.D` and `G0.theta2` share the same numerator — visible
    already in the matching squarefree degree $4$ — because $D = theta_2 \/ n$
    exactly (@sec-blocks); we certify both rows independently regardless.]
)

All ten denominators are sign-definite on $n gt.eq 4$, as are the denominators of
all nineteen certificate variables, so nothing blows up at any dimension.

= Verification <sec-verify>

A certificate is worth what its checking is worth. The independent verifier
*re-derives the objective from the 1992 definition* — $e_k$ of the row and column
sums, and $sigma_k$ as an explicit double sum of subpermanents over pairs of
$k$-subsets — and uses none of the closed forms of @sec-closedform, none of the
block decomposition of @sec-blocks and none of the Sturm machinery of @sec-sturm.
The only shared code is the orbit bookkeeping that inflates nineteen numbers into
two $n^2 times n^2$ matrices, and that is exercised against stored certificates
and against deliberate mutations.

At each $n$ it checks three things: that both Gram matrices are symmetric and
*positive definite*, by exact rational $L D L^T$ on the *full* $n^2 times n^2$
matrices rather than through the blocks; that the identity @eq-ansatz holds at
random rational points; and that the constant is $2 - k!\/n^k$. Positive
definiteness of the single Gram at the corner gives it for every multiplier,
since each $sigma_p$'s Gram is a permutation conjugate of it.

#figure(
  table(
    columns: (auto, auto, auto, auto, auto),
    align: (right, center, center, center, left),
    stroke: 0.4pt + luma(180),
    table.header([$n$], [*Gram*], [$sigma_0$ $L D L^T$], [$sigma_11$ $L D L^T$],
      [*identity*]),
    [$4,5,6,7$], [$16$–$49$], [PD], [PD], [exact over $QQ$, 2 points each],
    [$12$], [$144 times 144$], [PD, $9.17 times 10^(-6)$],
      [PD, $7.77 times 10^(-7)$], [exact over $QQ$, 2 points],
    [$25$], [$625 times 625$], [PD, $1.45 times 10^(-7)$],
      [PD, $5.80 times 10^(-9)$], [$FF_p$, 3 primes, 2 points],
  ),
  caption: [Independent verification of the uniform certificate. Entries under
    $L D L^T$ are the smallest exact pivot.]
)

Because the definiteness check runs on the unblocked matrices, it is an
independent confirmation of the block theory of @sec-blocks as well as of the
numbers.

*Why $FF_p$ at $n = 25$, and why that is still exact.* The rational evaluation
would need about $2.4 times 10^8$ `Fraction` multiplications per point. The same
computation modulo a prime is exact arithmetic — not floating point — and
vectorises: with $p < 2^20$ every intermediate stays inside 64-bit integers, so
the 625 quadratic forms become 625 matrix–vector products. Run at three
unrelated primes near $2^20$, a surviving discrepancy would have to be divisible
by all three.

*Positive control.* The same verifier is run on the independently produced,
already-verified *stored* certificates at $n = 4$ and $n = 5$, using their own
orbit data rather than any mapping of ours, and accepts them. If that had failed
the verifier would have been the thing at fault.

*Negative controls, four of them.* Three single-variable perturbations of the
uniform certificate at $n = 4$ — variables 0, 5 and 16, each moved by $10^(-6)$
— are rejected over $QQ$; a perturbation at $n = 6$ is rejected in $FF_p$ at all
three primes. A verifier that never rejects proves nothing.

== The fixed-dimension certificates <sec-anchors>

#claimbox[
  *Support layer: exact rational certificates, accepted by a standalone verifier.
  These are not Lean-checked, and no theorem of this paper depends on them.*
]

Five certificates at fixed dimensions were produced independently of the uniform
construction, each with its own numerical solve and its own rounding. Each
establishes the stated bound on the stated $K_n$, with equality only at $J_n\/n$:
$Phi_3 lt.eq 16\/9$ on $K_3$; $Phi_3 lt.eq 61\/32$ on $K_4$;
$Phi_3 lt.eq 244\/125$ on $K_5$; $Phi_3 lt.eq 71\/36$ on $K_6$; and, at a second
value of $k$ in the intermediate range, $Phi_4 lt.eq 1226\/625$ on $K_5$.

The four $k = 3$ cases are covered by Theorem A and Corollary B, equality cases
included. They are retained because they are the anchors against which the
uniform certificate was checked, and because they were rounded independently of
it. The case $(5,4)$ is not reached by the uniform construction.

#figure(
  table(
    columns: (auto, auto, auto, auto, auto, auto),
    align: (center, center, center, center, center, center),
    stroke: 0.4pt + luma(180),
    table.header([$(n,k)$], [*bound*], [*basis deg*], [*monomials in $F$*],
      [*cone*], [*certificate*]),
    [$(3,3)$], [$16\/9$], [$2$], [$93$], [$54$], [$314$ rationals],
    [$(4,3)$], [$61\/32$], [$1$], [$552$], [$16$], [$19$ rationals],
    [$(5,3)$], [$244\/125$], [$1$], [$2225$], [$25$], [$19$ rationals],
    [$(6,3)$], [$71\/36$], [$1$], [$6906$], [$36$], [$19$ rationals],
    [$(5,4)$], [$1226\/625$], [$2$], [$7875$], [$350$], [$440$ rationals],
  ),
  caption: [The five fixed-dimension certificates. Every one is exact rational
    data; the identity is confirmed by *full coefficient comparison*, not by
    sampling.]
)

Smallest exact $L D L^T$ pivots, as the standalone verifier reports them — first
the $sigma_0$ Gram, then the smallest over *all* $n^2$ multiplier Grams:
$8.24 times 10^(-3)$ and $8.36 times 10^(-3)$ at $(3,3)$; $6.94 times 10^(-3)$
and $6.65 times 10^(-3)$ at $(4,3)$; $2.02 times 10^(-3)$ and
$1.93 times 10^(-3)$ at $(5,3)$; $2.72 times 10^(-4)$ and $6.48 times 10^(-4)$
at $(6,3)$; $5.83 times 10^(-4)$ and $5.87 times 10^(-4)$ at $(5,4)$. Mutation
tests perturbing a single coefficient by $10^(-20)$ are rejected in every case.

The second number needs its matrix named, because two are in circulation. The
$n^2$ multiplier Grams are permutation conjugates of one another and so share a
spectrum, but an $L D L^T$ pivot depends on the order of the indices, and the
smallest pivot is not constant across the orbit. The design pipeline factors the
Gram at the corner $p = (0,0)$ and reports that one — $7.32 times 10^(-3)$ at
$(4,3)$, $7.11 times 10^(-4)$ at $(6,3)$ — where the verifier factors all $n^2$
and reports the minimum. Both decide the same question, and the verifier's
figure is the conservative one.

All five cases pass the standalone verifier in full — six checks each,
standard library only, no shared code with the pipeline. In case $(5,4)$ the
exported data writes all 26 Gram matrices out densely so that the verifier needs
no group theory, so it runs 26 exact rational factorisations of size 350 where
only two are distinct. That redundancy is deliberate: exploiting the conjugacy
would mean either trusting the conjugating permutation or verifying it, which is
exactly the group theory the dense export exists to keep out of the verifier. No
matrix is skipped.

$(5,4)$ also needed the block-diagonalisation to be solvable at all: at cone size
350 a monolithic interior-point solve needs of order 30 GB per cone. Blocked,
$sigma_0$ gives cones $[5,5,4,2,2,1,1,1,1,1]$ and $sigma_11$ gives
$[16,14,10,7,4,4,3,2,1,1,1]$ — identical to the blocks already recorded for the
Dittert case at $n = 5$ — with largest cone 16.

= Confinement, for every $k$ <sec-confine>

Theorem E is recalled from [6] and transferred to all $k$; nothing in this
section is claimed as new mathematics. It is included because it is uniform in
$k$ where the certificate of @sec-cert is not, and because it is short enough to
formalise once for the whole family.

The proof needs no expansion of the objective. Split the deficit as
$ (2 - gamma(n,k)) - Phi_k (A)
  = [1 - E_k (r)] + [1 - E_k (c)] + [P_k (A) - gamma(n,k)], $
where the third bracket is bounded below by $-gamma(n,k)$ because $P_k$ of a
non-negative matrix is non-negative. For the first two brackets, Maclaurin's
inequality in the telescoped form of Theorem F gives $E_k (r) lt.eq E_2 (r)$ on
the simplex, and $E_2$ is exactly computable:
$ E_2 (r) = 1 - frac(sum_i (r_i - 1)^2, n(n-1)) quad "whenever" sum_i r_i = n, $
which is `SubDittertK2.E_two_eq` and needs no positivity. Together these give
Theorem E, and its contrapositive is the confinement statement: a violator of the
Cheon–Hwang bound has its line sums within $(n-1)k!\/n^(k-1)$ of $bold(1)$ in
squared $ell^2$ distance, a neighbourhood that shrinks in $n$ for every fixed
$k gt.eq 2$.

The hypothesis $E_k lt.eq E_2$ is stated in Lean as a named predicate,
`SubDittertM.MaclaurinBound`, and `SubDittertMaclaurin.maclaurinBound_holds`
discharges it for every $2 lt.eq k lt.eq n$; `theoremM'` and `confinement'` are
the resulting unconditional statements. At $k = 2$ the predicate holds with
equality, so the conclusion is not vacuous there.

== Newton's and Maclaurin's inequalities in Lean <sec-newton>

Theorem F is classical, and the contribution is the formalisation. The route
avoids the reversal of polynomials that the textbook proof uses and whose root
theory Mathlib does not carry. Writing $Q_i = "coeff"_i \/ binom(m,i)$ for a
polynomial of degree $m$, one has $Q'_i = m dot.c Q_(i+1)$, so Newton's
inequality at index $i$ for $p$ is Newton's inequality at index $i - 1$ for $p'$,
and $p'$ is real-rooted whenever $p$ is. That reduces every index $i gt.eq 2$ to
a lower degree. Differentiation shifts the index upward, so $i = 1$ is never
reached by the induction; it is not a base case at one degree but has to be
proved directly at every degree, and it is where real-rootedness is consumed.
The ingredients are Rolle's theorem for real-rooted polynomials, Vieta's
formulas, the reciprocal identity
$e_(n-j)(v) = (product_i v_i) dot.c e_j (v^(-1))$, and Chebyshev's sum
inequality.

A second, independent Lean proof of Theorem F exists, written without sight of
the first and by a different route — Mathlib's `coeff_eq_esymm_roots_of_card`
with an induction on the degree, against an induction on the index — and its
statements agree with those above. It is stored as verification evidence outside
the build, in its own namespace (`NewtonCrosscheck`); agreement between two
independent proofs is evidence that the statements are the intended ones, which
is the one thing a kernel cannot check.

= Formalisation <sec-lean>

== The verification standard <sec-standard>

#keybox[
  The development elaborates with no `sorry`, and no declaration in it depends
  on `sorryAx`. `native_decide` is used nowhere. Every declaration this paper
  cites in support of a stated result carries a `#print axioms` command, and each
  returns exactly `[propext, Classical.choice, Quot.sound]` — with one exception,
  `NewtonIneq.choose_mul_sub`, a statement about binomial coefficients, which
  returns the strict subset `[propext, Quot.sound]`.
  #v(0.4em)
  All counts here are of the Lean sources as committed at `32c811e`, the commit
  at which they were last changed. The eight files
  carrying the results of this section contain 511 axiom-audited declarations:
  377 in `SubDittertK3.lean` and 7 in `RookSum.lean`, which together prove
  Theorem A; 21 in `SubDittertUniversal.lean` (Theorem C), 17 in
  `SubDittertK2.lean` (Theorem D), 37 in `SubDittertLinear.lean`, 13 in
  `SubDittertM.lean` and 6 in `SubDittertMaclaurin.lean` (Theorem E), and 33 in
  `NewtonInequalities.lean` (Theorem F). In `SubDittertK3.lean` the 377 are
  *every* named declaration in the file, so nothing in the file carrying
  Theorem A is left unaudited. The independent cross-check of @sec-newton adds
  12 more and is deliberately outside the build.
  #v(0.4em)
  Theorem G's formalised cells rest on further files, counted at their own
  commits and held to the same standard — `StabilityK3.lean` (33 audit
  lines) and `TverbergStability.lean` (21) at `1507013`,
  `LayerIdentity.lean` (28) at `27bda3f`, `SigmaFour.lean` (46) at
  `365e44e`, `StabilityK4.lean` (14) at `944b517`, and the partial
  `StabilityK5Atoms.lean` (15) at `f2bdc7f`. @sec-stab-lean is their record,
  and the verifier of @sec-stab-verify checks that record against those
  commits mechanically.
  #v(0.4em)
  In the other files the audits cover the results and their supporting lemmas
  rather than every private definition. That is not a gap: `#print axioms`
  reports the axioms of the *transitive closure* of a proof term, so auditing a
  theorem audits every definition and lemma the theorem rests on. No file
  contains a `sorry`, so nothing in any of them can acquire `sorryAx` from
  within; and an unaudited declaration on which no stated result depends cannot
  affect a stated result.
]

The development is built against Lean 4.14.0 and Mathlib `v4.14.0` [16].
`NewtonInequalities.lean` imports Mathlib and nothing else — no permanent, no
$K_n$ — because the results it proves are library material and the boundary
should stay visible.

What the kernel cannot check is the translation of the 1992 statement into
Lean's definitions. That is what @sec-chain item 2 defends, and it is the only
place left where a human error would survive the machine.

== Theorem A, in the order it is built <sec-chain>

#keybox[
  *`subDittert_k3_full` is Theorem A, in all three parts.* For every
  $n gt.eq 4$ and every $A$ with non-negative entries summing to $n$, it proves
  $E_3 (r) + E_3 (c) - P_3 (A) lt.eq 2 - 6\/n^3$; that equality holds if and only
  if $A = J_n\/n$; and the stability bound @eq-thmA-stab with the explicit
  $theta_2 (n)$ — with every definition in those statements built from scratch
  inside Lean.
]

+ *The statement.* `Kn`, `rowSum`, `colSum`, `esym`, `subPerm`, `sigmaK`, `E`,
  `P` and `Phi` are defined from scratch, with $sigma_k$ a double sum over
  `Finset.powersetCard k univ` of the permanent of the submatrix on rows $S$ and
  columns $T$. The final statement `subDittert_k3` is written out in the 1992
  notation.
+ *Validation of the definitions*, which matters more than it looks. `Phi_uniform`
  proves $Phi_k (J_n\/n) = 2 - k!\/n^k$ for *every* $k lt.eq n$, so the
  functional as formalised is tight at the conjectured maximiser exactly where
  the conjecture says it is; instances at $n = 3, 4, 5$ specialise it to
  $2 - 6\/n^3$. `sigmaK_rankOne` proves
  $sigma_k (x y^T) = k! dot e_k (x) dot e_k (y)$, which is the check that rows
  are read from $S$ and columns from $T$: a definition that reads both indices
  off the same subset satisfies a different identity, and a symmetric test matrix
  cannot detect that error, whereas this does. A concrete
  $sigma_3 = 450$ on an explicit $3 times 3$ matrix is checked against a hand
  value.
+ *The combinatorial half, closed for all $n$ at once.* `RookSum.lean` proves a
  closed form for $sigma_3$ directly from the subpermanent definition: the
  bridge is a bijection between $k$-subsets paired with a permutation of them
  and injections $"Fin" k arrow.r "Fin" n$, stated and proved general in $k$,
  specialised to $k=3$ by a three-index inclusion–exclusion sieve. On top of
  that, `obj_eq_objPoly` proves that the objective
  $(2 - 6\/n^3) - Phi_3 (A)$ equals an explicit polynomial `objPoly n A` in the
  entries of $A$ and its row and column sums, for every $n gt.eq 3$. Together
  these eliminate `Matrix.permanent`, `subPerm`, `sigmaK`, `esym` and every sum
  over `Finset.powersetCard` from everything downstream: what remains of the
  proof mentions none of them. `objPoly` is cross-validated outside Lean against
  the from-the-1992-definition objective of @sec-verify, exactly over $QQ$, at
  random rational points for $n = 4, 5, 6, 7$, at $J_n\/n$ where it must vanish,
  and against a mutation control.
+ *The ten positivity facts.* `certPositive_of_four_le` proves all ten quantities
  of @sec-sturm positive for every *real* $n gt.eq 4$ — real, not merely natural,
  which is strictly stronger and no harder here. Sturm is not needed inside Lean:
  after the substitution $n = m + 4$ all twenty polynomials involved (ten
  numerators, ten denominators) have non-negative coefficients and a positive
  constant term, so each proof is one `ring` and one `linarith`. As noted in
  @sec-blocks, one of the ten — `H.D` — is not independent
  ($D = theta_2 \/ n$ exactly), so this proves nine independent facts and one
  immediate consequence of them; Lean proves all ten on the same uniform footing
  regardless, since the substitution argument costs nothing extra to repeat.
+ *Both Gram families, and the $sigma_0$ Gram positive definite.*
  `G0_posSemidef` and `Hm_posSemidef` prove semidefiniteness for every
  $n gt.eq 4$, with no spectral theorem in either, and `G0_posDef` upgrades the
  first to *definiteness* — which is what the equality case needs. The $sigma_0$
  form splits into four manifestly non-negative pieces, one of them
  $theta_2 (n) dot.c sum_u b_u^2$; since $theta_2 (n) > 0$ is already among the
  ten facts, that piece alone is strictly positive off the origin, so
  definiteness costs ten further lines and no new mathematics. The eigenvalue
  multiplicities of @sec-blocks are not needed for it.
  For a multiplier Gram the coordinates are the residuals about the corner's own
  row and column; in those the form breaks into blocks $A$, $B$, $C$, $D$ —
  the isotypic blocks of @sec-blocks, in this basis rather than the one
  @sec-blocks normalises them in — and each is bounded below by a completion of
  squares, Lagrange's identity in two variables and Sylvester's in three. Seven
  positive quantities drive that, and they are the leading principal minors of
  those four blocks *times the constants* $1, 2, 4, 2, 1, 4, 1$. The constants
  do not depend on $n$, so positivity is the same question either way, but a
  bridge lemma stated without them is false. They are checked outside Lean as
  identities of rational functions, and the change of coordinates exactly over
  $QQ$ at $n = 4, 5, 6$ at three corners, with a mutation control.
+ *The Positivstellensatz identity.* `certificate_identity` proves @eq-ansatz
  itself, for every $n gt.eq 4$ and every $A in K_n$, with $G_0$ and the family
  $H_p$ the explicit Grams above. Both sums over corners are expanded in ten
  global invariants of the centred coordinates. Every coefficient in that
  expansion was emitted rather than typed, and checked outside Lean as an
  identity of rational functions of $n$ by full coefficient comparison rather
  than by sampling.
+ *The deduction.* `subDittert_k3_of_certificate` derives the bound from the
  certificate through the bridge lemma: non-negativity of the
  quadratic forms from `PosSemidef`, non-negativity of the entries of $A$ from
  membership of $K_n$, then `linarith`. The $lambda(b) dot (sum_q b_q)$ term does
  not appear, because that sum vanishes on $K_n$.
+ *The equality case and the stability bound*, both for every $n gt.eq 4$.
  `subDittert_k3_bound_and_uniqueness` is the bridge lemma's packaged form
  `certificate_bound_and_uniqueness` applied to the certificate's own data; its
  separation hypothesis is `eq_uniform_of_centre_eq_zero`, which is the remark
  that the centred coordinates are $b_p = A_p - 1\/n$ entrywise, so their
  vanishing *is* $A = J_n\/n$. `subDittert_k3_stability` keeps the
  $theta_2 (n) dot.c sum_u b_u^2$ piece instead of discarding it and so proves
  @eq-thmA-stab, with `subDittert_k3_stability_explicit` the same statement with
  the constant written out; `eq_uniform_of_Phi_eq_of_stability` then re-derives
  uniqueness from stability alone, without the positive-definite bridge, so the
  equality case stands on two independent Lean proofs.
  `subDittert_k3_full` states all three parts of Theorem A as one theorem in the
  1992 notation.

*A normalisation caveat, stated exactly*, on the ten quantities of the fourth
item — a separate matter from the seven constants of the fifth. Each numerator
and denominator in the
Lean file is separately cleared to primitive integer coefficients, and the pair
is sign-flipped together where the denominator is negative on $n gt.eq 4$. Both
operations scale by a positive rational, so each Lean quantity is a constant
*positive* rational multiple of the corresponding quantity in the Sturm
pipeline; the multiple is $1$ except for `H.A minor2` and `H.B` (both $1\/2$) and
`H.C minor2` ($4$). *These four numbers are an artefact of two independent
choices of primitive-integer clearing, one on each side, and carry no
mathematical content of their own*; a different but equally valid clearing
convention on either side would change $1\/2$ and $4$ to other positive rationals
without changing anything else. This was cross-checked at $n = 4, 5, 7, 13, 101$:
the ratio is constant and positive in every case, so positivity of one is
positivity of the other, which is the only fact that matters.

== Theorems C to F in Lean <sec-chain-rest>

The uniform half of the development is independent of the certificate and much
shorter.

`universal_identity` (Theorem C) is proved for every $n$ and every
$k lt.eq n$ from two coefficient rules. The $e_k$ rule is the centre identity
`esym_one_add` of `SubDittertLinear.lean`; the $sigma_k$ rule, `sigmaK_one_add`,
is proved through a rook bridge valid at every $k$ — summing over pairs of
injections $"Fin" k arrow.r "Fin" n$ is $k!$ times the subpermanent sum — with
the fibres of the restriction map counted by Mathlib's
`Equiv.sumEmbeddingEquivSigmaEmbeddingRestricted`. One supporting lemma,
`choose_subset_of_subset`, is absent from Mathlib and is a candidate for
upstreaming.

`subDittert_k2` (Theorem D) instantiates `universal_identity` at $k = 2$, closes
$sigma_2$ and $e_2$ in closed form by the $k = 2$ sieve, and concludes through
the same bridge lemma the $k = 3$ proof uses. There is no Gram matrix in it.

`theoremM'` and `confinement'` (Theorem E) are `theoremM` and `confinement` with
the hypothesis `MaclaurinBound` discharged by `maclaurinBound_holds`. The
attribution to [6] is the first section of the header of the file that states
them.

`newtonAt_all`, `newton_esymF` and `pnorm_le_two` (Theorem F) are proved in a
file that imports Mathlib alone.

== Equality and stability <sec-uniqueness>

For each of the five fixed-dimension certificates of @sec-anchors, equality holds
*only* at $J_n\/n$. The argument is one line: the $sigma_0$ Gram is positive
*definite* by exact $L D L^T$, and its monomial basis excludes the constant, so
$sigma_0 (b) = 0$ forces $b = 0$, while every other term of @eq-ansatz is
non-negative on $K_n$.

For every $n gt.eq 4$ the same conclusion is Lean-proved, and it needs no part of
the block-diagonalisation of @sec-blocks. The Bose–Mesner form of the $sigma_0$
Gram makes its quadratic form
$ sigma_0 (b) = c_0^"tot" (sum_u b_u)^2
  + c_0^"line" (sum_i R_i^2 + sum_j C_j^2) + theta_2 (n) sum_u b_u^2 $ <eq-g0split>
identically in $b$, with all three coefficients positive on $n gt.eq 4$; the
identity is `quadForm_G0`. The last term alone is strictly positive unless every
$b_u$ vanishes, so definiteness follows from $theta_2 (n) > 0$, one of the ten
facts of @sec-sturm, by an argument that mentions neither eigenvalues nor their
multiplicities. The spectral decomposition is the route by which the coefficients
were found; the finished identity does not depend on that route.

Keeping the $theta_2$ term of @eq-g0split rather than discarding it costs nothing
and gives @eq-thmA-stab, which is strictly stronger than the equality case. The
constant is *not* claimed optimal. Both sides of @eq-thmA-stab were evaluated
exactly over $QQ$ at $n = 4, 5, 6$ and the slack ratio measured. Along directions
where the row and column sums of $A - J_n\/n$ all vanish, the first two terms of
@eq-g0split vanish identically, only the multiplier half of the certificate is
being discarded, and the ratio is constant in the size of the perturbation —
$2.88$, $4.34$, $5.70$ at $n = 4, 5, 6$. So $theta_2 (n)$ is within a factor of
about three to six of the best constant in the directions where it is closest to
tight, and further off in general directions. Sharpening it would mean retaining
part of the multiplier half, which we have not attempted.

== What is not formalised <sec-notformal>

One thing is not: the block-diagonalisation of @sec-blocks as an *equivalence* —
the Bose–Mesner eigenvalues with their multiplicities, the isotypic
decomposition, and with them the statement that positive definiteness of the two
Grams is exactly the positivity of the ten rational functions. Lean proves the
implication the theorem needs and not the converse, and it proves it by explicit
algebra rather than by that route, so the reduction of @sec-blocks is
corroborated by the Lean development without being verified by it. The two are checked against each other
outside Lean: the unblocked $n^2 times n^2$ matrices are factored directly at six
dimensions in @sec-verify.

The fixed-dimension certificates of @sec-anchors are also unformalised, as
@sec-layers records.

= A stability form of the Tverberg–Friedland theorem <sec-stability>

Tverberg conjectured in 1963 [17], and Friedland proved in 1982 [18], that
$sigma_k$ attains its minimum on the doubly stochastic polytope $Omega_n$ only
at the barycentre $J_n\/n$; at $k = n$ the statement is the generalised van
der Waerden conjecture, whose $k = n$, $sigma_n = per$ case was settled by
Egorychev [20] and Falikman [21]. Those theorems give strictness but no rate.
Theorem G is the quantitative form: for $2 lt.eq k lt.eq 5$, on the per-$k$
ranges stated with it, the deficit is bounded below by an explicit positive
multiple of the squared Frobenius distance to the barycentre. The excluded
cells are finite in number for each $k$:
$ (k,n) in {(3,3)} union {(4,n): 4 lt.eq n lt.eq 7}
  union {(5,n): 5 lt.eq n lt.eq 13}. $
One of them is a genuine obstruction rather than a gap in the argument: at
$n = k = 3$ the inequality with this constant is false, and
@sec-stab-exception exhibits the witness. For the remaining excluded cells the
argument below does not reach, and no claim is made either way.

Everything in this part is confined to the doubly stochastic polytope. The
estimates below use four a-priori facts (@sec-stab-facts) that hold on
$Omega_n$ and fail on the larger set $K_n$; nothing in this part should be
read as a statement about $K_n$. The transfer to a collar around the Birkhoff
polytope, and the degradation it costs, is the business of @sec-k4 — that is
where Theorem H consumes this part.

== Setting and notation <sec-stab-notation>

Fix $n gt.eq 2$ and let $A in Omega_n$. Put
$ B = A - J_n\/n, quad Q = norm(B)_F^2 = sum_(i,j) b_(i j)^2. $
Since $A$ is doubly stochastic, every row and every column of $B$ sums to
zero; we refer to this as the *centred slice*. Write
$ q_i = sum_j b_(i j)^2, quad q'_j = sum_i b_(i j)^2, quad
  M = max(max_i q_i, thin max_j q'_j), quad beta = 1 - 1/n, $
so that $Q = sum_i q_i = sum_j q'_j$. For $r gt.eq 2$ set
$p_r = sum_(i,j) b_(i j)^r$, and
$ Y_R = sum_i q_i^2, quad Y_C = sum_j q'^2_j, quad Z = norm(B^T B)_F^2. $
Four further invariants appear at degree five. With $f_3 (i) = sum_j b_(i j)^3$
and $g_3 (j) = sum_i b_(i j)^3$, and with $q, q'$ read as vectors,
$ Gamma_a = q^T B thin q', quad
  Gamma_b = sum_(i,j) b_(i j)^2 (B B^T B)_(i j), quad
  Gamma_c = sum_i q_i f_3 (i), quad
  Gamma'_c = sum_j q'_j g_3 (j). $

Finally, for $0 lt.eq m lt.eq k$, $s_m = [k]_m \/ [n]_m$ and
$t_m = s_m^2 dot.c (k-m)! \/ n^(k-m)$ — the coefficients of Theorem C, in the
index letter $m$ of the layer they weight. Two facts about them are used
repeatedly. First,
$ t_2 = frac(k(k-1) thin k!, n^k (n-1)^2), quad "so" quad
  c(n,k) = t_2\/4. $ <eq-stab-t2>
Second, the ratio law
$ frac(t_(m+1), t_m) = frac(n(k-m), (n-m)^2). $ <eq-stab-ratio>
Both are immediate from the definitions.

== The layer identity <sec-stab-layer>

#claimbox[
  *Lemma S1.* For every $A in Omega_n$ and every $1 lt.eq k lt.eq n$,
  $ frac(sigma_k (A), binom(n,k)^2) - frac(k!, n^k)
    = sum_(m=2)^k t_m thin sigma_m (B), quad B = A - J_n\/n. $ <eq-stab-layer>
  #v(0.4em)
  #leanline[Lean: `layer_identity` in `LayerIdentity.lean` (commit `27bda3f`),
  kernel-checked at *every* $k$, under hypotheses weaker than this part needs:
  see @sec-stab-lean.]
]

Lemma S1 is the $P_k$ half of Theorem C's decomposition @eq-universal read on
the centred slice, where the $e_d$ half vanishes; the proof below is
self-contained and is the one the Lean development formalises.

*Proof.* Expanding a permanent of a sum, for index sets $alpha, beta$ of size
$k$,
$ per((X+Y)[alpha|beta]) = sum_(S subset.eq alpha, T subset.eq beta, |S| = |T|)
  per(X[S|T]) thin per(Y[alpha without S thin | thin beta without T]). $
Take $X = J_n\/n$ and $Y = B$, so $per(X[S|T]) = d!\/n^d$ for $|S| = |T| = d$.
Summing over all $alpha, beta$ and writing $m = k - d$ for the size of the
$B$-part, each pair $(U,V)$ with $|U| = |V| = m$ is completed to a pair
$(alpha, beta)$ by choosing $S$ disjoint from $U$ and $T$ disjoint from $V$,
which can be done in $binom(n-m, k-m)^2$ ways. Hence
$ sigma_k (A) = sum_(m=0)^k binom(n-m, k-m)^2 frac((k-m)!, n^(k-m))
  sigma_m (B). $
Since $binom(n-m, k-m) \/ binom(n,k) = s_m$, dividing by $binom(n,k)^2$ turns
the coefficient into $t_m$. The term $m = 0$ contributes $t_0 = k!\/n^k$, and
the term $m = 1$ vanishes because $sigma_1 (B) = sum_(i,j) b_(i j) = 0$. $qed$

Write $F = sum_(m=2)^k t_m sigma_m (B)$ for the left side of @eq-stab-layer.
Since $t_m > 0$ for all $m lt.eq k$, Theorem G is equivalent to
$ sum_(m=3)^k t_m thin sigma_m (B) gt.eq -1/4 t_2 thin Q, $ <eq-stab-goal>
because $sigma_2 (B) = Q\/2$ on the centred slice (@sec-stab-core), so that
$t_2 sigma_2 (B) = 1/2 t_2 Q$ and the two halves of $1/2 t_2 Q$ split between
the claimed bound and the allowance in @eq-stab-goal. It is @eq-stab-goal that
we prove.

== The core expansions <sec-stab-core>

On the centred slice each $sigma_m (B)$ collapses onto a small set of
invariants. Expanding $sigma_m$ by Möbius inversion over ordered pairs of set
partitions of $[m]$, a partition with a singleton block contributes a factor
that is a row sum or a column sum of $B$, hence zero. Equivalently, only those
orbit invariants survive whose associated bipartite multigraph has minimum
degree at least two.

This expansion, together with the reductions at degrees two, three and four
below, is due to McCullagh [19, §3]; the degree-five reduction is a
specialisation of the general formula given there. In the notation of
@sec-stab-notation, for $B$ with vanishing row and column sums,
$ sigma_2 (B) = 1/2 Q, $ <eq-stab-core2>
$ sigma_3 (B) = 2/3 p_3, $ <eq-stab-core3>
$ sigma_4 (B) = 3/2 p_4 + 1/8 Q^2 + 1/4 Z - 3/4 Y_R - 3/4 Y_C, $ <eq-stab-core4>
$ sigma_5 (B) = 24/5 p_5 + 1/3 Q thin p_3 + Gamma_a + 2 Gamma_b - 4 Gamma_c
  - 4 Gamma'_c. $ <eq-stab-core5>

The coefficient of $p_m$ in $sigma_m$ is $(m-1)!\/m$, the only contributing
partition pair being the maximal one in each coordinate; this accounts for
$1/2, 2/3, 3/2, 24/5$ in equations @eq-stab-core2[]–@eq-stab-core5[].

#leanline[Lean: the $sigma_4$ expansion @eq-stab-core4 is kernel-checked at
*every* centred $B$ — `sigma_four_centred` in `SigmaFour.lean` (commit
`365e44e`), stated with both marginal hypotheses and consuming both, so the
identity holds wherever the row and column sums vanish, not only on
$Omega_n - J_n\/n$.]

== Four a-priori facts on the slice <sec-stab-facts>

#claimbox[
  *Lemma S2.* Let $A in Omega_n$ and $B = A - J_n\/n$. Then
  #v(0.2em)
  *(F1)* $-1/n lt.eq b_(i j) lt.eq 1 - 1/n$ for all $i, j$;
  #v(0.1em)
  *(F2)* $M lt.eq 1 - 1/n$;
  #v(0.1em)
  *(F3)* $Q lt.eq n - 1$;
  #v(0.1em)
  *(F4)* $norm(B)_"op" lt.eq 1$, and consequently $Z lt.eq Q$.
]

*Proof.* (F1) Each entry of $A$ lies in $[0,1]$, since $0 lt.eq A_(i j)$ and
$A_(i j)$ is at most the sum of its row, which is $1$. Subtract $1\/n$.

(F2) $q_i = sum_j A_(i j)^2 - 2/n sum_j A_(i j) + n dot.c 1/n^2
= sum_j A_(i j)^2 - 1/n$, and
$sum_j A_(i j)^2 lt.eq (max_j A_(i j)) sum_j A_(i j) lt.eq 1$ by (F1). The
same computation applies to columns.

(F3) Sum (F2) over $i$: $Q = sum_i q_i lt.eq n(1 - 1/n) = n - 1$. Equality
holds at every permutation matrix.

(F4) Let $u = n^(-1\/2) bold(1)$. Then $A u = u$ and $(J_n\/n) u = u$, so
$B u = 0$. For $x perp u$ we have $(J_n\/n) x = 0$, hence $B x = A x$. By
Birkhoff's theorem $A$ is a convex combination of permutation matrices, each
an isometry, so $norm(A x) lt.eq norm(x)$. Decomposing an arbitrary $x$ as
$alpha u + x^perp$ gives $B x = B x^perp = A x^perp$ and therefore
$norm(B x) lt.eq norm(x^perp) lt.eq norm(x)$. For the consequence,
$Z = norm(B^T B)_F^2 lt.eq norm(B^T)_"op"^2 norm(B)_F^2 lt.eq Q$. $qed$

All four are attained at the permutation matrices, so none can be improved by
a constant factor. Birkhoff's theorem is where double stochasticity is
consumed; (F4) is the fact that fails first off the slice, and @sec-k4-collar
is what replaces the whole lemma on the collar.

== Per-invariant estimates <sec-stab-estimates>

The estimates below are one-sided by design. Each invariant is bounded only on
the side that the sign of its coefficient in equations
@eq-stab-core3[]–@eq-stab-core5[] requires, and the asymmetry of the range in (F1) makes the required side the
cheap one. This is where the entry bound earns its keep: for $b$ in
$[-1/n, 1 - 1/n]$,
$ b^3 gt.eq -1/n b^2 quad "and" quad b^3 lt.eq (1 - 1/n) thin b^2, $ <eq-stab-entry>
the first because $b^3 gt.eq 0$ when $b gt.eq 0$ and
$b^3 = b dot.c b^2 gt.eq -1/n b^2$ when $b < 0$, the second symmetrically.
Summing the first over all entries gives $p_3 gt.eq -Q\/n$, a factor $n$
stronger than the two-sided bound $|p_3| lt.eq beta Q$, which would be too
weak for what follows.

#claimbox[
  *Lemma S3.* On the centred slice:
  #figure(
    table(
      columns: (auto, auto),
      align: (left, center),
      stroke: 0.4pt + luma(180),
      table.header([*estimate*], [*attained*]),
      [(a) $p_3 gt.eq -Q\/n$], [no],
      [(b) $p_5 gt.eq -Q\/n^3$], [no],
      [(c) $p_4 lt.eq beta^2 Q$], [no],
      [(d) $Y_R lt.eq M Q$ and $Y_C lt.eq M Q$], [*yes*],
      [(e) $Gamma_c lt.eq beta M Q$ and $Gamma'_c lt.eq beta M Q$], [no],
      [(f) $|Gamma_a| lt.eq M Q$], [no],
      [(g) $|Gamma_b| lt.eq beta Q$], [no],
      [(h) $Q thin p_3 gt.eq -beta Q$], [no],
      [(i) $Z lt.eq Q$], [*yes*],
      [(j) $p_4, Q^2, Z gt.eq 0$], [—],
    )
  )
]

*Proof.* (a) is @eq-stab-entry summed. (b) For $b < 0$ we have
$b^3 gt.eq -n^(-3)$ by (F1), so $b^5 = b^3 b^2 gt.eq -n^(-3) b^2$; for
$b gt.eq 0$, $b^5 gt.eq 0$. (c) $b^2 lt.eq beta^2$ by (F1), since
$beta gt.eq 1\/n$ for $n gt.eq 2$.

(d) $Y_R = sum_i q_i^2 lt.eq (max_i q_i) sum_i q_i lt.eq M Q$. Equality holds
when all $q_i$ agree, in particular at every permutation matrix.

(e) By @eq-stab-entry, $f_3 (i) lt.eq beta q_i$, and $q_i gt.eq 0$, so
$Gamma_c = sum_i q_i f_3 (i) lt.eq beta sum_i q_i^2 = beta Y_R
lt.eq beta M Q$ by (d).

(f) $|Gamma_a| = |q^T B q'| lt.eq norm(q) norm(B)_"op" norm(q')
lt.eq sqrt(Y_R) sqrt(Y_C) lt.eq M Q$, using (F4) and then (d).

(g) By Cauchy–Schwarz and then (F4),
$ |Gamma_b| lt.eq (sum_(i,j) b_(i j)^4)^(1\/2) norm(B B^T B)_F
  lt.eq sqrt(p_4) thin norm(B)_"op" norm(B^T B)_F
  lt.eq sqrt(p_4) sqrt(Z) lt.eq beta sqrt(Q) dot.c sqrt(Q), $
using (c) and (i).

(h) Multiply (a) by $Q gt.eq 0$ and apply (F3):
$Q p_3 gt.eq -Q^2\/n gt.eq -(n-1)/n Q$.

(i) is (F4). (j) is clear. $qed$

== Proof of Theorem G <sec-stab-proof>

Combining equations @eq-stab-core3[]–@eq-stab-core5[] with Lemma S3 term by
term —
discarding the nonnegative invariants that carry a plus sign, by (j) — gives
lower bounds $sigma_m (B) gt.eq -C_m (n) thin Q$ with
$ C_3 (n) = frac(2, 3n), quad C_4 (n) = 3/2 beta, quad
  C_5 (n) = frac(24, 5 n^3) + 10/3 beta + 8 beta^2. $ <eq-stab-C>
For $C_4$: the only negative terms of @eq-stab-core4 are $-3/4 (Y_R + Y_C)$,
bounded by $3/2 M Q lt.eq 3/2 beta Q$ using (d) and (F2). For $C_5$: the six
terms of @eq-stab-core5 contribute $24/5 n^(-3)$, $1/3 beta$,
$M lt.eq beta$, $2 beta$, $4 beta M lt.eq 4 beta^2$ and
$4 beta M lt.eq 4 beta^2$ respectively, by (b), (h), (f), (g) and (e).

By @eq-stab-goal it therefore suffices that
$ Phi(n,k) := frac(4, t_2) sum_(m=3)^k t_m thin C_m (n) < 1. $ <eq-stab-phi>
Using the ratio law @eq-stab-ratio, $Phi$ is an explicit rational function of
$n$ for each $k$:
$ Phi(n,3) = frac(8, 3(n-2)^2), $ <eq-stab-phi3>
$ Phi(n,4) = frac(16, 3(n-2)^2) + frac(12 n(n-1), (n-2)^2 (n-3)^2), $ <eq-stab-phi4>
$ Phi(n,5) = frac(8, (n-2)^2) + frac(36 n(n-1), (n-2)^2 (n-3)^2)
  + frac(24 n^3 thin C_5 (n), (n-2)^2 (n-3)^2 (n-4)^2). $ <eq-stab-phi5>
For $k = 2$ the sum in @eq-stab-phi is empty, so $Phi(n,2) = 0$ and the
conclusion holds for every $n gt.eq 2$.

From @eq-stab-phi3, $Phi(n,3) < 1$ exactly when $(n-2)^2 > 8\/3$, that is
$n gt.eq 4$. For $k = 4$ and $k = 5$ the same conclusion is reached without
any appeal to numerics, as follows. Write each $Phi(dot.c, k)$ in lowest terms
as a ratio of integer polynomials in $n$ with no common content. The
denominators are then
$ 3(n-2)^2, quad 3(n-2)^2 (n-3)^2, quad 5(n-2)^2 (n-3)^2 (n-4)^2 $
for $k = 3, 4, 5$ respectively, each positive for $n > 4$. So
$Phi(n,k) < 1$ is equivalent to $P_k (n) > 0$, where $P_k$ denotes the
denominator minus the numerator:
$ P_3 (n) = 3n^2 - 12n + 4, $
$ P_4 (n) = 3n^4 - 30n^3 + 59n^2 - 48n - 36, $
$ P_5 (n) = 5n^6 - 90n^5 + 445n^4 - 1760n^3 + 620n^2 + 2400n - 3456. $
Substituting $n = m + n_k$, where $n_k$ is the threshold, makes every
coefficient nonnegative with the constant term positive:
$ P_3 (m+4) = 3m^2 + 12m + 4, $
$ P_4 (m+8) = 3m^4 + 66m^3 + 491m^2 + 1280m + 284, $
$ P_5 (m+14) = 5m^6 + 330m^5 + 8845m^4 + 121160m^3 + 861620m^2
  + 2716720m + 1660864. $
Since $m gt.eq 0$ corresponds to $n gt.eq n_k$, this settles every
$n gt.eq n_k$ at once. The thresholds are sharp for this argument:
$P_3 (3) = -5$, $P_4 (7) = -568$ and $P_5 (13) = -306876$, so
$Phi gt.eq 1$ at $n = n_k - 1$ in each case.

The values at the thresholds are $Phi(8,4) = 0.8948 dots$ and
$Phi(14,5) = 0.8094 dots$, and $Phi(dot.c, k)$ is decreasing above the
threshold, reaching $0.1351 dots$ at $(k,n) = (4,15)$ and $0.2540 dots$ at
$(k,n) = (5,20)$ and tending to $0$ like $n^(-2)$. This proves Theorem G. $qed$

The binding term throughout is $Y_R$ (with $Y_C$), whose estimate (d) is
attained at the permutation matrices. The thresholds in Theorem G therefore
cannot be lowered by sharpening (d). They can be lowered by retaining the
three nonnegative terms of @eq-stab-core4 that the proof discards; at a
permutation matrix those terms make $sigma_4 (B)$ positive, whereas
@eq-stab-C allows it to be as negative as $-3/2 beta Q$. @sec-stab-addendum
determines how much that route can give, and shows that it stops short of
$sigma_4 gt.eq 0$.

== The cell $(3,3)$ is a genuine exception <sec-stab-exception>

#claimbox[
  *Proposition S4.* For $n = k = 3$ the conclusion of Theorem G is false.
  #v(0.4em)
  #leanline[Lean: `not_stabilityAt_three_three` in `TverbergStability.lean`
  (commit `1507013`), with the witness stored as `witness33` rather than
  cited.]
]

*Proof.* Let $P$ be a permutation matrix of order $3$ and take
$A = 1/2 (J_3 - P)$, the doubly stochastic matrix that is uniform off a
permutation:
$ A = mat(0, 1\/2, 1\/2; 1\/2, 0, 1\/2; 1\/2, 1\/2, 0). $
Then $per(J_3 - P) = 2$, so $sigma_3 (A) = per(A) = 2\/8 = 1\/4$, while
$binom(3,3)^2 dot.c 3! \/ 3^3 = 2\/9$. Hence $F = 1\/4 - 2\/9 = 1\/36$. Also
$Q = norm(A - J_3\/3)_F^2 = 1\/2$, so $F\/Q = 1\/18$. But
$c(3,3) = t_2\/4 = 1\/12 > 1\/18$. $qed$

This is the only cell among those excluded from Theorem G that is known to be
a counterexample. For $(4,n)$ with $4 lt.eq n lt.eq 7$ and $(5,n)$ with
$5 lt.eq n lt.eq 13$ the inequality is not decided here.

== Sharpness <sec-stab-sharp>

#claimbox[
  *Proposition S5.* Let $k gt.eq 3$ and let $c_"opt" (n,k)$ be the largest
  constant for which the conclusion of Theorem G holds. Then in the range
  covered by Theorem G,
  $ 1/4 t_2 lt.eq c_"opt" (n,k) < 1/2 t_2. $
]

*Proof.* The lower bound is Theorem G with @eq-stab-t2. For the upper bound,
take $B = J_n\/n - P$ for a permutation matrix $P$ and consider
$A_s = J_n\/n + s B$ for small $s > 0$, which is doubly stochastic for
$0 lt.eq s lt.eq 1\/(n-1)$. The entries of $B$ are $-beta$ at the $n$ cells
of $P$ and $1\/n$ elsewhere, so
$ p_3 (B) = -n beta^3 + frac(n^2 - n, n^3)
  = frac(n-1, n^2) (1 - (n-1)^2) < 0 quad (n gt.eq 3). $
By Lemma S1 and equations @eq-stab-core2[]–@eq-stab-core3[],
$ frac(F(s B), norm(s B)_F^2) = 1/2 t_2
  + s thin t_3 thin frac(2/3 p_3 (B), Q_B) + O(s^2), $
which is strictly less than $1/2 t_2$ for all small $s > 0$. $qed$

So the constant of Theorem G is optimal to within a factor two, and the factor
two cannot be closed to a factor one: no constant as large as $1/2 t_2$ works
for any $k gt.eq 3$.

One measurement corroborates the picture at $k = 4$, and it is a verified
computation, not a theorem: the largest admissible constant, measured
against the claimed $c(n,4)$, is $1.88$, $1.91$, $1.93$ at $n = 8, 9, 10$ —
rising toward the factor-two ceiling of Proposition S5 and never reaching
it.

== Verification <sec-stab-verify>

Every displayed identity and estimate of this part is checked over the
rationals, with no floating-point arithmetic in any decision, by the
standalone script `graded_verify_stability.py`; its output is
`results/graded_verify_stability.log`. The script imports nothing beyond the
standard library. It verifies, in order: Lemma S1 against brute-force
subpermanent sums; the core expansions, equations
@eq-stab-core2[]–@eq-stab-core5[], against brute-force subpermanent sums; the four facts of Lemma S2, with (F4)
tested both directly on random rational vectors and through its consequence
$Z lt.eq Q$; each estimate of Lemma S3 in the one direction the proof uses,
reporting its slack ratio so the two tightness claims in the table are
checkable; the per-layer bounds of @eq-stab-C; the closed forms
of equations @eq-stab-phi3[]–@eq-stab-phi5[], the thresholds and the
exceptional sets; the
four quoted values of $Phi$ and its monotonicity above each threshold; the
polynomial argument of @sec-stab-proof, by building $Phi(dot.c, k)$ as an
exact rational function, reducing it to lowest terms as an integer pair,
cross-checking it against the arithmetic evaluation, and confirming the sign
pattern of $P_k (m + n_k)$, the sharpness values $P_k (n_k - 1) lt.eq 0$, and
every denominator and coefficient displayed in @sec-stab-proof term by term;
Theorem G end to end on doubly stochastic matrices at every covered cell
listed in @sec-stab-proof; Proposition S4 with its witness; Proposition S5
through the closed form for $p_3 (J_n\/n - P)$; and the formalisation scope
stated in @sec-stab-lean, against the Lean sources themselves.

That last check is the one exception to the script being self-contained: it
reads the Lean files out of the repository at named commits. Run with
`--no-lean` it skips them, and records in its log that the scope claims of
@sec-stab-lean went unchecked in that run; it does not pass them quietly.

The test matrices include the permutation matrices, $(J_n - P)\/(n-1)$, the
barycentre, random rational convex combinations of permutation matrices, and
near-vertex matrices — that is, the configurations at which the estimates of
Lemma S3 are attained or nearly attained.

The verifier carries mutation controls, which were run and which fire: four
deliberate faults — the constant doubled, a sign flip in @eq-stab-core4, each
threshold lowered by one so that an excluded cell is claimed as covered, and
the estimate of Lemma S3(a) over-tightened — are each rejected by the check
responsible for them. With no fault injected those same four checks raise
nothing, so each rejection is attributable to its fault. A verifier that never
rejects would establish nothing, and `--mutate` reruns the controls alone.

== What is machine-checked, and what is not <sec-stab-lean>

*What is machine-checked.* Theorem G is kernel-checked at $k = 2$, for every
$n gt.eq 2$, at $k = 3$, for every $n gt.eq 4$, and at $k = 4$, for every
$n gt.eq 8$ — in each case the whole range the statement covers for that
$k$, with no arithmetic gap between the formalised and the written range.
The $k = 2, 3$ cells are `stabilityAt_two` and `stabilityAt_three` in
`StabilityK3.lean` (commit `1507013`); the $k = 4$ cell is `stabilityAt_four`
in `StabilityK4.lean` (commit `944b517`). All three discharge
`TverbergStability.StabilityAt k n`: the displayed inequality of Theorem G,
with the constant `cVal` equal to $c(n,k)$ and $sigma_k$ as the subpermanent
sum. The $k = 4$ proof follows this part's route step for step: the layer
identity at $k = 4$, the core expansion @eq-stab-core4 as
`sigma_four_centred` (`SigmaFour.lean`, commit `365e44e`), the slice fact
(F2) and estimate (d) with the discard of the three nonnegative terms, and
the threshold arithmetic consumed as the committed `Phi4_lt_one`, with the
bridge `layer_ratio_lt` checking that $Phi$ rebuilt from the Lean
coefficients is exactly @eq-stab-phi4. Lemma S1, the layer identity that
@sec-stab-core runs on, is kernel-checked at *every* $k$, not only at the
cells above: `layer_identity` in `LayerIdentity.lean` (commit `27bda3f`),
28 of 28 declarations audited. Its hypotheses are weaker than this part's —
it assumes $1 lt.eq k lt.eq n$ and $sum_(i j) B_(i j) = 0$, the single
scalar constraint, where Lemma S1 as stated here assumes $A$ doubly
stochastic. The doubly stochastic case is the corollary. So the identity
underneath the whole argument holds, formally, on a strictly larger set than
the theorem needs.

Two limits of the $k = 4$ formalisation must not be over-read, and we state
them where the claim is made. First, the threshold $8$ is a limit of the
argument, not known sharp: the cells $(k = 4, 4 lt.eq n lt.eq 7)$ are
undecided, and there is no $k = 4$ analogue of `three_threshold_not_slack` —
nothing here should be read as implying one. Second, the binding atom is
$Y_R$ (with $Y_C$), whose estimate is attained at the permutation matrices,
so the threshold cannot move by sharpening anything in the formalised file;
it moves only by retaining the three discarded nonnegative terms of
@eq-stab-core4, the route whose limit @sec-stab-addendum measures.

Three further claims of this part are kernel-checked alongside those. Two sit
in `TverbergStability.lean`: Proposition S4, with its witness stored rather
than cited (`witness33`, `not_stabilityAt_three_three`), and the threshold
layer of @sec-stab-proof at $k = 3, 4, 5$ — the cleared numerators $P_k$ of
$1 - Phi(dot.c, k)$, their shifted forms $P_k (m + n_k)$ with the
coefficients displayed there, and $Phi(n,k) < 1$ above each threshold
(`phiPoly3/4/5`, `phiPoly3/4/5_pos`, `Phi3/4/5_lt_one`). The third sits in
`StabilityK3.lean`: the sharpness of the $k = 3$ threshold, in the strong
form that assuming stability at every $n gt.eq 3$ is contradictory
(`three_threshold_not_slack`).

*What is not.* At $k = 5$ the estimates that feed the budget are not fully
formalised, and so neither is Theorem G there: there is no
`stabilityAt_five`, and the $(k = 5, n gt.eq 14)$ cell rests on written
proofs plus this part's verifier. Five of the $k = 5$ per-invariant atoms
*are* kernel-checked — `StabilityK5Atoms.lean` (commit `f2bdc7f`), whose
header lists what is not there — but the expansion @eq-stab-core5, the
estimates (f) and (g), the fact (F4) and the assembly are not, so the cell
is not closed and its grade does not change. Partial atom coverage is not
cell coverage, and we do not average the two.

*How that division is checked, not asserted.* The verifier's V12 reads the
Lean files above, each at the commit cited for it — `git show`, so the
working tree cannot flatter the claim — and confirms each half. On the
positive half: that `cVal` *is* $c(n,k)$, compared as exact rationals over
$2 lt.eq k lt.eq 7$, $2 lt.eq n lt.eq 29$ rather than as text; that the
hypotheses of `stabilityAt_two`, `stabilityAt_three` and `stabilityAt_four`
are the thresholds claimed above; that `sigma_four_centred` is present with
both marginal hypotheses in its statement; and that Lean's $P_3, P_4, P_5$,
which are an independent derivation, agree at every point with the
polynomials this verifier builds for @sec-stab-proof. It recomputes the two
values Lean stores for Proposition S4, $sigma_3 = 1\/4$ and
$norm(B)_F^2 = 1\/2$, in its own exact arithmetic. On the negative half:
that no `stabilityAt_five` exists — with a non-vacuity check that the same
search does find the three theorems that are there, since an absence found
by a broken search is not an absence.

On Lemma S1 it checks that Lean's coefficient `tVal` is this part's $t_m$,
again as exact rationals and not as text, and that `layer_identity` carries
every ingredient of the displayed identity while its hypotheses contain no
double stochasticity — with the matching non-vacuity check that the token
*is* findable, since it occurs in `StabilityK3.lean`. It runs the orphan
diff on the four files that carry audit blocks, empty in both directions:
33 of 33 declarations in `StabilityK3.lean` carry `#print axioms` lines, as
do 14 of 14 declarations in `StabilityK4.lean` and 46 of 46 declarations in
`SigmaFour.lean`, with 28 of 28 in `LayerIdentity.lean`; no line in any of
the four lacks a declaration, and no source contains `sorry` or
`native_decide` outside its comments. All four counts are parsed back out of
this section, so a number stated here and a number measured there cannot
drift apart.

One limit of that check is worth stating. The axiom sets themselves — that
each of the 121 audited declarations reports a subset of `propext`,
`Classical.choice`, `Quot.sound`, with no `sorryAx` — come from elaborating
the files, which only Lean can do and which this verifier does not repeat.
V12 checks that each audit block is complete and that the sources are free of
`sorry`; the conformance of what those blocks print is the Lean build's
evidence, not this script's.

== Addendum: the limit of the discarded-terms route <sec-stab-addendum>

@sec-stab-proof discards the three nonnegative invariants of @eq-stab-core4
and notes that retaining them would lower the thresholds. This section
determines by how much. The answer is bounded, and the natural target fails.

#claimbox[
  *Proposition S6.* $sigma_4$ restricted to the centred slice is indefinite.
  At $n = 4$, the doubly stochastic matrix
  $ A = 1/2 mat(1, 1, 0, 0; 1, 0, 0, 1; 0, 0, 1, 1; 0, 1, 1, 0) $
  has $B = A - J_4\/4 = 1/4 M_0$ with
  $ M_0 = mat(1, 1, -1, -1; 1, -1, -1, 1; -1, -1, 1, 1; -1, 1, 1, -1), $
  and $per(M_0) = -8$, so $sigma_4 (B) = -1\/32$ while $Q = 1$.
]

Rows three and four of $M_0$ are the negatives of rows one and two, so $M_0$
has rank two; all its line sums vanish. Two independent searches over
$Omega_4$ — random sampling of rational convex combinations of permutation
matrices, and local descent by $2 times 2$ cycle moves — both bottom out at
$sigma_4\/Q = -1\/32$ exactly, at matrices of this shape.

So the hoped-for $sigma_4 gt.eq 0$ is false, and the route can at best
replace $C_4$ of @eq-stab-C by a constant $epsilon$ with
$epsilon gt.eq 1\/32$. Doing so would give thresholds $(k=3, n gt.eq 4)$,
$(k=4, n gt.eq 5)$, $(k=5, n gt.eq 12)$, against Theorem G's $(4, 8, 14)$;
the same thresholds result for every $epsilon lt.eq 1\/16$, so the exact
constant does not matter to the outcome. The available gain is therefore
three steps at $k = 4$, two at $k = 5$, and none at $k = 3$. Proving any such
$epsilon$ is a separate problem: the inequality is tight along a family
(below), false at $epsilon = 0$, and the elementary term-by-term bounds of
@sec-stab-estimates give only $epsilon approx 9\/8$. This unproved
$epsilon$ is exactly the hypothesis of the conditional statement in
@sec-k4-statement, and it is recorded there as a parked research problem.

The equality family of @sec-stab-estimates has an explanation, which also
locates the negativity.

#claimbox[
  *Proposition S7.* For centred $u, v$ (that is,
  $sum_i u_i = sum_j v_j = 0$) and $B = c thin u v^T$, which is automatically
  doubly centred,
  $ sigma_4 (B) = 3/2 c^4 D(u) D(v), quad
    D(x) = sum_i x_i^4 - 1/2 (sum_i x_i^2)^2. $
]

The $2 times 2$ cycle directions are precisely the locus $D = 0$: for
$u = e_i - e_(i')$ one has $sum u^4 = 2$ and $(sum u^2)^2 = 4$, so
$D(u) = 0$. That is why $sigma_4$ vanishes identically along them rather than
by accident. The zero locus is larger than the two-entry vectors —
$D(2,-1,-1,0) = 0$ as well.

$D$ takes both signs: $D(1,1,-1,-1) = -4$ and $D(3,-1,-1,-1) = 12$. Choosing
$D(u) > 0$ against $D(v) < 0$ makes $sigma_4$ negative on a rank-one
direction inside $Omega_4$: with $u = (3,-1,-1,-1)$, $v = (1,1,-1,-1)$ and
$c = 1\/12$, the entries of $J_4\/4 + B$ are nonnegative and
$sigma_4 (B)\/Q = -1\/96$. An exhaustive search over rank-one directions with
small integer $u, v$ inside $Omega_4$ bottoms out at exactly that value,
three times smaller in magnitude than the rank-two minimum $-1\/32$. So
negativity begins at rank one but the extremum is not attained there, and a
proof for rank-one directions alone would not settle the question.

*On novelty.* Tverberg's inequality and Friedland's proof give strictness but
no rate. We are not aware of a previous quantitative form, and Theorem G
appears to be the first stability form of the Tverberg–Friedland theorem. The
claim of machine-checked status divides with the cells, as @sec-stab-lean
sets out: at $k = 2$, $k = 3$ and $k = 4$ the theorem is kernel-checked, and
we are not aware of an earlier kernel-checked stability form of
Tverberg–Friedland at any $k$; at $k = 5$ the support layer is written
proofs plus the exact verifier, and no machine-checked status is claimed for
that cell. The narrower scoping is deliberate: quantitative stability bounds
for other permanent inequalities do exist, and the claim above is about
Tverberg–Friedland specifically.

= The case $k = 4$: confinement, splitting, and the collar <sec-k4>

This part proves Theorem H and establishes the insensitivity computation
stated beside it. The argument is local. Confinement (Theorem E) traps any
violator in a collar around the Birkhoff polytope; a collar matrix splits
orthogonally into a line-sum block and a doubly centred block; the two
blocks are governed by separate results, and the five cross terms between
them have exact reductions, all displayed below. The computation is the
second deliverable: at every sampled admissible value of the collar bound on
row squared norms — the one constant in the argument that is not settled —
the threshold stays at $n gt.eq 10$, and a mechanical audit pins down where
that constant can act at all.

== Statement, scope, and the remaining gap <sec-k4-statement>

In the centred coordinates of @sec-objective, with
$F(A) = (2 - gamma(n,4)) - Phi_4 (A)$, Theorem H asserts $F(A) > 0$ for all
$A in K_n$ other than $A = J_n\/n$, where $F = 0$, for every $n gt.eq 10$.

*Not formalised.* Theorem H is not machine-checked, and neither is the
insensitivity computation. Their support layer is written proofs together
with the exact verifier of @sec-k4-verify, which recomputes every displayed
quantity of this part over the rationals.

*What is formalised is a neighbouring statement, on the slice.* The
stability form of the Tverberg–Friedland theorem is kernel-checked at
$k = 2$, $k = 3$ *and* $k = 4$ on the doubly stochastic slice itself
(@sec-stab-lean; the $k = 4$ cell is `stabilityAt_four`, `StabilityK4.lean`,
commit `944b517`). This part consumes that result through the centred-block
input at $k = 4$ — so the slice form of the input is now kernel-checked —
but everything the collar costs on top of the slice is not: the collar facts
of @sec-k4-collar, the cross-term reductions, the merge and the budget are
supported by written proofs plus the verifier only. No claim of
machine-checked status attaches to Theorem H.

*The remaining honest gap is $n = 8$ and $n = 9$.* Theorem H begins at
$n = 10$, and the anchor certificates of @sec-k4-anchors settle $(5,4)$,
$(6,4)$ and $(7,4)$, so $k = 4$ is not settled at exactly $n = 8, 9$ by
what this paper carries. Two routes close the gap: fixed-$n$ certificates
at the two open cells, whose state is @sec-k4-anchors; or the
certificate-family solve in $QQ(n)$, which needs no anchors
(@sec-computational). Under the hypothesis of the conditional statement
below the line would be fully closed: the conditional route reaches
$n gt.eq 8$, and its only outstanding cell, $(7,4)$, is settled by anchor
certificate.

#warnbox[
  *Conditional statement (the hypothesis is part of the statement; this is
  not a result of this paper).* Suppose that on the doubly centred slice
  $sigma_4 (z) gt.eq -epsilon norm(z)_F^2$ for some
  $epsilon lt.eq 1\/16$. Then for $k = 4$ and every $n gt.eq 8$, $F(A) > 0$
  for all $A in K_n$ other than $J_n\/n$.
  #v(0.4em)
  The hypothesis is *not proved*. It is known to be false at $epsilon = 0$,
  and the measured obstruction is $epsilon gt.eq 1\/32$, with the explicit
  rank-two witness of Proposition S6. It is recorded as a parked research
  problem, and this box should be read as a conditional statement and not as
  a theorem.
]

*Instruments used and not re-derived.* The line block is `pincer_line.py`:
`F_line` and the $(S 4)$ closed form for $sigma_d$ of a rank-two line matrix,
`line_margin` (margins computed, not tabulated), `u_max`, `lam_line`. The
centred block is `pincer_onesided.py`: `deficit_centred`. The decomposition,
the identity $sigma_2 (z^((a,b))) = 2 z_(a b)^2 - q_a - q'_b + Q\/2$, and the
$k = 3$ instance of the assembly are `pincer_assembly_k3.py`. The collar
bound on row squared norms is the committed cap of `graded_lemmaB.py`, and
the operator-norm degradation off the slice is the collar form (K4) of
@sec-k4-collar, the analogue of the slice fact (F4).

== The decomposition, stated once <sec-k4-decomp>

Let $A in K_n$ and $B = A - J_n\/n$ with row sums $R$ and column sums $C$.
Set
$ x_i = R_i\/n, quad y_j = C_j\/n, quad L_(i j) = x_i + y_j, quad z = B - L, $
so $sum_i x_i = sum_j y_j = 0$, $z$ is doubly centred, and
$norm(L)_F^2 = n(mu + nu)$ with $mu = norm(x)^2$, $nu = norm(y)^2$. As in
@sec-stab-notation, but now for the centred block $z$, write
$Q = norm(z)_F^2$, $q_i = sum_j z_(i j)^2$, $q'_j = sum_i z_(i j)^2$,
$N = z z^T$, $N' = z^T z$, and $f_3 (a) = sum_b z_(a b)^3$,
$g_3 (b) = sum_a z_(a b)^3$.

Confinement bounds the line block only:
$ mu + nu lt.eq u_max (n,k) = frac((n-1) thin k!, n^(k+1)). $ <eq-k4-umax>

== The layer identity, and what couples <sec-k4-layers>

Theorem C's identity @eq-universal gives
$F = sum_(d=1)^k [t_d thin sigma_d (B) - s_d (e_d (R) + e_d (C))]$, with the
same coefficients $s_d, t_d$ that @sec-stab-notation writes in the layer
index $m$. Two facts make the split usable.

*The $e_d$ half never couples.* $z$ has vanishing line sums, so the row and
column sums of $L + z$ are those of $L$ alone.

*Expansion by the number of $z$ factors.* For any $X, Y$ and any $d$,
$ sigma_d (X + Y) = sum_(j=0)^d thin sum_(|S| = |T| = j)
  per(X[S|T]) thin sigma_(d-j) (Y^((S,T))), $ <eq-k4-expand>
$Y^((S,T))$ being $Y$ with rows $S$ and columns $T$ deleted. Taking $X = z$,
$Y = L$ and collecting,
$ F(L + z) = F_"line" (x, y) + F_"centred" (z)
  + sum_d t_d dot.c ("cross parts of " sigma_d). $ <eq-k4-split>
At $d = 2$ the cross part vanishes *identically*, not merely to leading
order.

== The five cross-term reductions <sec-k4-cross>

All five are exact and are verified against brute force in @sec-k4-verify.

At $d = 3$:
$ X_1 = (n-2)^2 thin x^T z thin y, quad X_2 = (2 - n) thin Xi, quad
  Xi := sum_i x_i q_i + sum_j y_j q'_j. $ <eq-k4-X>

At $d = 4$:
$ Y_1 = -(n-2)(n-3)^2 [thin x^T z thin (y compose y)
  + (x compose x)^T z thin y thin], $ <eq-k4-Y1>
$ Y_2 = (n-2)(n-3) [ -sum_(s_1 < s_2) N_(s_1 s_2) e_2 (x_I)
  - sum_(t_1 < t_2) N'_(t_1 t_2) e_2 (y_J) ]
  + 2(n-3)^2 sum_(i,j) z_(i j)^2 x_i y_j, $ <eq-k4-Y2>
$ Y_3 = -(n-3) [thin 2 A_1 - A_2 + 2 A_3 - A_4 thin], quad
  A_1 = sum_a x_a f_3 (a), quad A_2 = x^T z thin q', quad
  A_3 = sum_b y_b g_3 (b), quad A_4 = q^T z thin y, $ <eq-k4-Y3>
where $compose$ is the entrywise product, and $I = [n] without S$,
$J = [n] without T$ for the deleted index pairs $S = {s_1, s_2}$,
$T = {t_1, t_2}$.

Three mechanisms produce them, and each is the same principle: anything
separable in the deleted indices is annihilated by
$sum_a z_(a b) = sum_b z_(a b) = 0$.

*(a) $Y_1$: the restricted $e_1$ is not zero.* On $I = [n] without {a}$ and
$J = [n] without {b}$ one has $e_1 (x_I) = -x_a$, $e_1 (y_J) = -y_b$ and
$e_2 (y_J) = e_2 (y) + y_b^2$. In the $(S 4)$ closed form for $sigma_3$ the
$t = 0$ and $t = 3$ terms depend on $b$ alone and on $a$ alone and die; the
$t = 1, 2$ terms leave $x_a y_b^2$ and $x_a^2 y_b$ with coefficient
$-(n-2)(n-3)^2$.

*(b) $Y_2$: a vanishing lift.* Its $e_2$ pieces depend on $S$ alone and $T$
alone, and $sum_T per(z[S|T]) = -N_(s_1 s_2)$,
$sum_S per(z[S|T]) = -N'_(t_1 t_2)$. For the $x_S y_T$ piece, lift the
restricted sum to the unrestricted one over all four indices: every expanded
piece carries a lone $sum_s z_(s t)$ or $sum_t z_(s t)$, so the lift is
*identically zero* and the restricted sum is a pure diagonal correction,
equal to $2 sum_(i j) z_(i j)^2 x_i y_j$. An absolute-value bound discards
precisely that cancellation and overshoots by four orders of magnitude.

*(c) $Y_3$: subpermanents through a row.*
$sigma_1 (L^((S,T))) = -(n-3)(x_S + y_T)$, and
$sum_(S,T) per(z[S|T]) thin x_S = sum_a x_a Psi_a$ with
$Psi_a = sum_b z_(a b) sigma_2 (z^((a,b))) = 2 f_3 (a) - (z q')_a$.

== The merge, and why $k = 4$ inherits the clean form <sec-k4-merge>

On the collar $A gt.eq 0$ gives the *per-entry* bound
$ z_(i j) gt.eq -(1/n + x_i + y_j), $ <eq-k4-entry>
not $z_(i j) gt.eq -1\/n$. Cubing and summing,
$ sum_(i j) z_(i j)^3 gt.eq -1/n Q - Xi, $ <eq-k4-merge-eq>
and the perturbation is *exactly* the invariant of the cross term $X_2$. The
two effects are therefore one quantity, to be charged once — but *at its full
summed coefficient*: the $m = 3$ layer contributes $2/3 Xi$ and the cross
term $(n-2) Xi$, so the coefficient is $(3n-4)\/3$, not $(n-2)$. Counting
once deletes the double count, not a coefficient.

At $k = 4$ the layers are $m = 2, 3, 4$, and the only odd-power one-sided
step is at $m = 3$: the centred core of $sigma_4$ is @eq-stab-core4 —
$3/2 p_4 + 1/8 Q^2 + 1/4 Z - 3/4 (Y_R + Y_C)$, in the invariants of
@sec-stab-notation now taken of $z$ — every term of even degree. So no second
perturbation can arise and the merge keeps its single-coefficient form. This
is special to $k lt.eq 4$: at $m = 5$ the perturbation enters as
$(1\/n + x_i + y_j)^3$, which is four cross invariants rather than one.

== The collar facts <sec-k4-collar>

Write $rho^2 = (n-1) k! \/ n^(k-1)$ for the confinement radius on line sums,
and $beta_c = 1 + rho - 1\/n$. The four facts below are the collar forms of
(F1)–(F4) of Lemma S2, in the same order, with the degradation the collar
costs; the verifier's log names them G1–G4.

*(K1)* $-1\/n lt.eq b_(i j) lt.eq beta_c$. The lower side needs only
$A gt.eq 0$ and so does *not* degrade off the slice; that asymmetry is what
makes the $m = 3$ step cheap.
*(K2)* $max_i q_i (B) lt.eq (1 + rho)^2 - 1\/n + 2 rho\/n$, from
$sum_j A_(i j)^2 lt.eq (max_j A_(i j)) (sum_j A_(i j)) lt.eq (1 + rho)^2$.
*(K3)* $Q lt.eq n - 1 + rho^2$, since $Q = sum_(i j) A_(i j)^2 - 1$ and
$sum_(i j) A_(i j)^2 lt.eq sum_i (1 + R_i)^2 = n + p_2 (R)$.
*(K4)* $norm(B)_"op" lt.eq sqrt((1 + rho)^2 + rho^2\/n)$: a nonnegative
matrix with all line sums at most $1 + rho$ has operator norm at most
$1 + rho$, and $B u = R\/sqrt(n)$ for $u = bold(1)\/sqrt(n)$. Birkhoff is
lost off the slice; the bound is not. Consequently
$norm(z)_"op" lt.eq norm(B)_"op" + sqrt(2 n thin u_max)$.

*The one unsettled constant.* The slice bound $q_i (z) lt.eq 1 - 1\/n$
requires row sums equal to $1$ *and* nonnegativity; on the collar
$J_n\/n + z$ has row sums $1$ but can have negative entries, so the bound
does not transfer, and it is refuted — a permutation with one reweighted row
violates it by a factor $1.63$ at $n = 10$ and $1.58$ at $n = 11$, and
violations occur from $(k,n) = (3,4)$ upward at perturbations as small as
$t = 1\/60$. We therefore write $q_i (z) lt.eq c thin (1 - 1\/n)$ and carry
$c$ symbolically. @sec-k4-insens shows the threshold does not depend on it.

== The budget <sec-k4-budget>

Layer two is the budget: on the centred block
$t_2 sigma_2 (z) = 1/2 t_2 Q$, and on the line block
$F_"line" gt.eq 1/2 lambda_"line" (mu + nu)$. Every other contribution is
bounded below and charged to whichever budget it scales with — a term
carrying $(mu + nu)$ to the line budget, one carrying $Q$ to the centred
budget. $X_1$ and $Y_1, Y_2$ carry $(mu + nu)$ or $(mu + nu)^(3\/2)$ and go
to the line side; $Xi$ and $Y_3$ carry $Q$ or $sqrt(mu + nu) sqrt(M Q)$,
with $M = max(max_i q_i, max_j q'_j)$ as before, and go to the centred side,
$Y_3$ split between the two by the arithmetic–geometric mean. The resulting
consumption, as a fraction of each budget, is what @sec-k4-verify recomputes
line by line; both totals below $1$ is the conclusion.

== Insensitivity to the unsettled constant <sec-k4-insens>

This is a computation with an audited structure, graded as exactly that in
its statement in the introduction; what follows is the record. Only three
budget lines involve $c$: the $sigma_4$ core line is *linear* in it, and the
two $Y_3$ lines ride on $sqrt(c)$. Everything else — the $m = 3$ core, $Xi$,
the line tail, $X_1$, $Y_1$, $Y_2$ — is independent of it. That
decomposition is not read off the derivation alone: it is asserted
mechanically, every budget line recomputed at $c$ and $2c$, at $n = 10$ and
$n = 16$, with the run aborting on any change — so a line that silently
acquired a $c$-dependence would kill the computation rather than skew it.
At $n = 10$ the linear share of the centred column is $0.379$ and the total
exposure $0.488$; by $n = 20$ these are $0.311$ and $0.341$. So about half
the column is insulated, and the linear part carries the already-small
factor $t_4\/t_2$.

#figure(
  table(
    columns: (auto, auto),
    align: (left, center),
    stroke: 0.4pt + luma(180),
    table.header([*$c$*], [*honest threshold*]),
    [1.00 (slice value; refuted on the collar)], [9],
    [1.25], [9],
    [1.50], [9],
    [1.58 (smallest constructed violation, at $n = 11$)], [10],
    [1.63 (largest constructed violation, at $n = 10$)], [10],
    [2.00], [10],
    [2.34 (collar cap, low)], [10],
    [2.53 (collar cap, high)], [10],
    [3.00], [11],
    [4.00], [11],
  ),
  caption: [The threshold of Theorem H at the ten sampled values of the
    collar constant $c$. The admissible band is $1.58 lt.eq c lt.eq 2.53$,
    and the threshold is $10$ at every sampled value in it. Every row is
    parsed out of this document and recomputed by the verifier of
    @sec-k4-verify.]
) <k4-sens-table>

The admissible band is $1.58 lt.eq c lt.eq 2.53$: below it the constructed
violation forbids, above it the proved cap forbids. The threshold is $10$ at
every sampled value in the band, and the audited structure above names the
only three lines through which an unsampled $c$ could act; no claim is made
for unsampled values. What the computation does establish is direction:
sharpening the constant cannot improve Theorem H at any sampled value, and
no sampled weakening within the cap damages it. On the route of the
conditional statement the picture differs, because there the $sigma_4$ core
line is replaced by $epsilon$ and is $c$-free while the $Y_3$ lines are not:
the cap is worth one step, $n gt.eq 9$ becoming $n gt.eq 8$.

== Verification <sec-k4-verify>

`graded_verify_k4.py` recomputes every displayed quantity of this part over
$QQ$ with no floating-point arithmetic in any decision, and *reads the
numbers out of this document* — the sensitivity table of @sec-k4-insens is
parsed from the typst source of this paper, not restated in the script — so
that displayed and checked cannot drift apart. It checks: the expansion
@eq-k4-expand at $d = 2, 3, 4$ against brute force, including that the
$d = 2$ cross part is exactly zero; the end-to-end identity @eq-k4-split
with every $t_d$ in place, against $F$ computed from the 1992 functional;
all five reductions of @sec-k4-cross against brute force; the per-entry
bound and the merge of @sec-k4-merge, on configurations of *both* signs of
$sum z^3$; the four collar facts of @sec-k4-collar; every budget line of
@sec-k4-budget recomputed from the layer identity; and the sensitivity table
row by row against the parsed document. Its output is
`results/graded_verify_k4.log`.

Mutation controls, each with a *separating* witness — one on which the
injected fault actually changes the value, asserted in the same line:

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, left),
    stroke: 0.4pt + luma(180),
    table.header([*control*], [*fault*], [*caught by*]),
    [M1], [a $t_d$ factor dropped from a cross term], [end-to-end identity],
    [M2], [the merge coefficient $(3n-4)\/3$ replaced by $(n-2)$],
      [budget-line check],
    [M3], [the $d = 2$ cross part assumed nonzero], [expansion check],
    [M4], [$c$ rescaled in a $c$-independent line], [sensitivity audit],
  ),
  caption: [The four mutation controls of `graded_verify_k4.py`.]
)

Two of these encode errors made and corrected while the argument was being
assembled: a dropped $t_4$, and the merge coefficient. They are controls
because they happened.

= The anchor cells: $k = 4$, $5 lt.eq n lt.eq 9$ <sec-k4-anchors>

Theorem H begins at $n = 10$. The five cells below it are each a fixed-$n$
question, and each is recorded here at the grade it has actually reached —
no cell inherits the grade of a neighbour. *Anchor grade* — the $(5,4)$
standard — means an exact rational certificate accepted in full by the six
checks of the standalone verifier of @sec-anchors: the bound, $sigma_k$ by
two structurally different algorithms, the polynomial identity by *full*
coefficient comparison, positive definiteness of the assembled Gram matrices
by exact $L D L^T$ over $QQ$, equality only at $J_n\/n$, and mutation tests
rejected. Anything less is stated as what it is.

#figure(
  table(
    columns: (auto, auto, auto),
    align: (center, left, left),
    stroke: 0.4pt + luma(180),
    table.header([*cell*], [*status*], [*support*]),
    [$(5,4)$], [settled: $Phi_4 lt.eq 1226\/625$ on $K_5$, equality only at
      $J_5\/5$], [anchor grade: the stored certificate
      `subdittert_n5k4d2_certificate.json` of @sec-anchors — 26 exact
      $L D L^T$ factorisations of size 350, full coefficient comparison,
      mutation tests rejected; two independent full runs logged],
    [$(6,4)$], [settled: $Phi_4 lt.eq 107\/54$ on $K_6$, equality only at
      $J_6\/6$], [anchor grade, on the stored exact witness
      `n6_H2_201.json`: all six checks of the $(5,4)$ standard — the
      full-monomial identity over all 40,386 coefficients; both assembled
      Gram matrices (cone size 702) positive definite over $QQ$, least
      pivots $4.083407 times 10^(-5)$ ($sigma_0$) and
      $1.070308 times 10^(-5)$ ($sigma_11$); conjugacy proved exactly,
      all 36 transporters inducing basis bijections with the corner Gram
      invariant under the stabiliser; equality only at $J_6\/6$; mutation
      tests rejected],
    [$(7,4)$], [settled: $Phi_4 lt.eq 4778\/2401$ on $K_7$, equality only
      at $J_7\/7$], [anchor grade, on the stored exact witness
      `n7_H2_201.json`: all six checks of the $(5,4)$ standard — the
      full-monomial identity over all 156,555 coefficients; $sigma_k$ by
      two structurally different algorithms; the bound; equality only at
      $J_7\/7$; mutation tests rejected; conjugacy proved exactly, all 49
      transporters inducing basis bijections; and check [4], both assembled
      Gram matrices positive definite over $QQ$, by the congruence route
      stated below, every link of which is a stored artefact],
    [$(8,4)$], [not settled; one check short of anchor grade], [on the
      stored exact witness `n8_H2_201.json`, five of the six checks of the
      $(5,4)$ standard hold: the full-monomial identity over all 496,448
      coefficients, computed in two parts that sum exactly; $sigma_k$ by
      two structurally different algorithms; the bound $1021\/512$;
      equality only at $J_8\/8$; mutation tests rejected — and the
      conjugacy is proved exactly, all 64 transporters inducing basis
      bijections. Positivity holds block-wise: all 21 canonical blocks
      positive definite over $QQ$, least pivot $1.960 times 10^(-5)$. What
      has not run is the assembled $2144 times 2144$ factorisation — check
      [4] of the standard — and block definiteness is not assembled
      definiteness, so the cell is not settled],
    [$(9,4)$], [not settled], [no witness exists: the exact solve exceeded
      available memory at this size. Nothing is stored, and nothing is
      claimed],
  ),
  caption: [The five cells between Theorem A's line and Theorem H's range,
    each at its own grade, as of 30 July 2026.]
) <k4-anchor-table>

*How $(7,4)$ closed check [4].* Both assembled Grams are positive definite
over $QQ$ by congruence rather than by a single direct factorisation, and
each link of the route is a stored artefact. The 21 isotypic components are
*exactly* $H$-orthogonal over $QQ$ and their translates span — 1,368,988
inner products checked, every one exactly zero
(`anchor_wtest_n67_part1.log`). On each component the congruence block is
the Kronecker product of two smaller matrices, $h_b$ and $C_b$, and all 21
of each are positive definite under exact $L D L^T$
(`anchor_cb_measure_n7.log`; the $h_b$ independently in
`verify_H2_n7.log`); the Kronecker argument then makes each component block
positive definite, orthogonality-with-spanning assembles the components,
and the conjugacy (A1)/(A2) extends the verdict to all 49 multiplier Grams
(`anchor_check3_n7.log`). The two component computations use different
bases of the same components, so their join is itself checked — every
component dimension $d dot.c e$ against the spanned dimension, all 21
components, total $2548 = 2 times 1274$ (`anchor_join_n567.log`), with four
rejection controls that fire (`anchor_join_controls.log`). That join check
is a consistency check between stored artefacts, not an independent
verification: the mathematics is in the links. $sigma_0$ additionally
admits a direct assembled factorisation, positive definite over $QQ$ with
least pivot $1.637015 times 10^(-5)$; the full factorisation record,
including $sigma_11$'s, is archived when the run completes, and the
congruence route does not depend on it.

With the cells as they stand, the unconditional state of the line $k = 4$
is: settled for $n = 5, 6, 7$ (anchor grade) and for every
$n gt.eq 10$ (Theorem H, written-proof plus exact-verifier grade); not
settled at $n = 8$ and $n = 9$. The line becomes settled for every
$n gt.eq 5$ exactly when the two open cells of @k4-anchor-table reach at
least anchor grade, and not before. None of the theorems of this paper
depends on any cell of the table.

= Toward a certificate family at $k = 4$ and $k = 5$ <sec-computational>

#claimbox[
  *Support layer: exact rational computation with stored witnesses. Nothing in
  this section is a theorem of this paper, and nothing in it is Lean-checked.*
]

The line $k = 4$ now carries Theorem H, but Theorem H is not a certificate:
the local route bounds the deficit below by budgeted charges rather than
exhibiting an identity, and it neither reaches the open cells
$n = 7, 8, 9$ of @sec-k4-anchors nor offers anything to formalise by the
pattern of Theorem A. A certificate family in $QQ(n)$ at $k = 4$ would do
all three at once — supersede the local route, close the open cells in one
stroke, and inherit the $k = 3$ formalisation pattern. This section records
the decided groundwork toward one.

The certificate programme of @sec-cert has a shape that depends on $k$ only
through $e = ceil((k-1)\/2)$, because a common Gram basis of degree $e$ gives
$deg(b_p sigma_p) = 2e + 1$, which must reach $deg F = k$. Mixed degrees are
ruled out for even $k$: if $sigma_0$ carried basis degree $k\/2$ and the
multipliers $k\/2 - 1$, the degree-$k$ part of the identity would make the top
form $F_k$ a sum of squares on the hyperplane, and @eq-universal shows
$F_k (b) = s_k [s_k sigma_k (b) - e_k (R) - e_k (C)]$, which is negative at
explicit doubly centred integer matrices — the smallest is a $4 times 4$ with
$per(b) = -854$. So $e(k) = ceil((k-1)\/2)$ and the programme's counts are
constant on the bands $\{2,3\}$, $\{4,5\}$, $\{6,7\}$, and so on: within a band
the constraint matrix is literally the same matrix and only the right-hand side
moves. Band one is $\{2,3\}$, which Theorems A and D close.

The same computation bounds the method's reach. The binding block's multiplicity
is $2, 16, 93$ at $e = 1, 2, 3$, and the programme grows with it: 19 unknowns at
$e = 1$ and 440 at $e = 2$. The route therefore reaches every *fixed* $k$ at all
large $n$ and cannot reach $k = n$, where the stabilisation threshold and the
parameter collide.

For band two the current state is a decided sweep rather than a certificate. At
$k = 4$ the pinning programme was decided over $QQ$ at $n = 5, 6, 7$, with no
verdict resting on a solver's reported sign: infeasibility is witnessed by a
rational Farkas multiplier, positive semidefinite by construction, whose value is
constant and non-positive on the affine set; feasibility by a rational point with
every canonical block positive definite under exact $L D L^T$. The full pinning
is infeasible at all three dimensions, as are twelve of the thirteen
single-block omissions. The one programme that survives — 201 pins, omitting the
$16 times 16$ block of $sigma_11$ — has an exact strictly feasible rational point
at every dimension tested, $n = 5, 6, 7, 8$, with least stored pivots
$5.11 times 10^(-5)$, $4.94 times 10^(-5)$, $4.84 times 10^(-5)$ and
$1.96 times 10^(-5)$. The cases $n gt.eq 6$ had resisted every floating-point
instrument, and the failure has an exact explanation: three integer relations
among the seventy diagonal constraints leave the working coordinates roughly
twelve digits below the constant column's scale, so each solver ran beneath its
own cancellation floor. A change of variables taking the constraint values
themselves as the unknowns — validated first against the known $n = 5$ verdict
as a positive control — produced the points. Every verdict has its witness stored as exact rationals and
re-checked by a standalone verifier that re-derives the constraint system and the
pin rows from the problem definition, carries its own elimination and its own
$L D L^T$, and confirms that every canonical basis has full column rank — without
which block definiteness would not imply definiteness of the whole and the test
would be vacuous. Mutation controls were run and failed as they should.

There is no certificate family in $n$ for band two, so there is nothing yet to
formalise.

= Assessment <sec-assessment>

*What is proved, at what grade.* Theorem A, for every $n gt.eq 4$, by an
exact rational certificate whose coefficients are rational functions of $n$,
with definiteness decided by Sturm sequences over $QQ$ and the identity
verified independently at six dimensions — machine-checked end to end.
Theorems C to F, in Lean, uniformly in $n$ and $k$. Theorem G,
kernel-checked at $k = 2$, $3$ and $4$, over the whole stated range for each
of those $k$, and carried at $k = 5$ by written proofs plus the exact
verifier of @sec-stab-verify. Theorem H, by written proofs plus the exact
verifier of @sec-k4-verify, not formalised; the insensitivity computation
beside it is graded in its own statement. No floating-point number enters
any of these decisions: the numerics find candidates, and every accepted
statement is re-established over $QQ$ or over $FF_p$.

*What kind of proofs these are.* Theorem A is a computer proof, and a small
one by the standards of the genre — nineteen rational functions of $n$, of
degree at most 12. It is checkable in minutes at any fixed $n$. It conveys
very little insight into *why* the bound holds; @sec-design is the closest
thing to an explanation we can offer, and it is an explanation of the
certificate's geometry rather than of the inequality. Theorems G and H are the opposite kind of
object: ordinary estimates assembled by hand, whose computer content is
verification rather than construction — the exact verifiers recompute what
the written proofs display, and in two places parse this document itself so
that displayed and checked cannot drift; the insensitivity computation is
the same species with a smaller claim. Theorems C to F are ordinary
mathematics that happens to be machine-checked.

*What is machine-checked, precisely.* Theorem A itself in all three parts, and
with it every step between the 1992 statement and them: the definitions, the
tightness of the functional at $J_n\/n$ for every $k lt.eq n$, the rank-one
identity that pins the definition of $sigma_k$, the closed form for $sigma_3$ and
its reduction of the objective to an explicit polynomial, the ten positivity
facts for all real $n gt.eq 4$, positive semidefiniteness of both Gram families
and positive *definiteness* of the $sigma_0$ Gram, the Positivstellensatz
identity, the deduction from certificate to bound, the equality case — twice, by
independent routes — and the stability bound with its explicit constant. Beyond
Theorem A: the universal decomposition at every $(n,k)$, the case $k = 2$ at
every $n$, the confinement at every $2 lt.eq k lt.eq n$, Newton's and
Maclaurin's inequalities, and — for Theorem G — the cells $(k = 2,$ every
$n gt.eq 2)$, $(k = 3,$ every $n gt.eq 4)$ and $(k = 4,$ every
$n gt.eq 8)$, the layer identity at every $k$ under a weaker hypothesis, the
$sigma_4$ core expansion at every centred matrix, the threshold polynomials
at $k = 3, 4, 5$, the $(3,3)$ counterexample with its stored witness, and
the non-slackness of the $k = 3$ threshold — subject to the two stated
limits of the $k = 4$ formalisation, which @sec-stab-lean carries.
@sec-standard states the standard and pins it to a commit; @sec-stab-lean
does the same for the stability files at their own commits. What the machine does not check is that the Lean definitions say what
the 1992 paper says; @sec-chain item 2 is the argument that they do. We state
the division explicitly because "machine-checked" is otherwise an ambiguous
claim.

*What is not claimed.* At $k = 4$: nothing beyond Theorem H's range
$n gt.eq 10$, the settled cells $(5,4)$, $(6,4)$ and $(7,4)$, and the
per-cell records of @sec-k4-anchors, each at its stated grade — the cells
$n = 8$ and $n = 9$ are open here. At $k = 5$: nothing beyond the stability cell
$(k = 5, n gt.eq 14)$ of Theorem G, at written-proof plus exact-verifier
grade; the Cheon–Hwang inequality itself is not claimed at any $(5, n)$
except the anchor $(5,4)$ of @sec-anchors, which concerns $k = 4$. No
statement about general $k$ beyond Theorems C and E. Nothing refereed. The
constant $theta_2 (n)$ of @eq-thmA-stab is not claimed optimal
(@sec-uniqueness), and the constant $c(n,k)$ of Theorem G is optimal only to
within the factor two of @sec-stab-sharp. No novelty is claimed for the
identity of Theorem C, for the statement of Theorem D, for Theorem E, or for
Theorem F. We have not read Cheon and Wanless 2007 [7] and do not rely on it.

*On the priority claims.* @sec-priority records public dated claims on the
$k = n$ endpoint that appeared within a single week of this work, three of
them in public repositories [11] with no corresponding preprint, and one
assembly among them claiming Dittert in full. To our knowledge Theorem A is
the first resolved case of the Cheon–Hwang conjecture with $2 < k < n$, and
Theorem G is the first stability form of the Tverberg–Friedland theorem
(@sec-stab-addendum states that claim's scope). Both claims cover public code
repositories as well as the indexed literature; both are priority claims, not
claims of difficulty; and both are perishable on a line that has moved this
fast — they should be re-checked before this paper is submitted anywhere.
Theorem H extends the resolved range to a second line at a lower grade, and
its priority claim is subordinate to its grade: written proofs plus an exact
verifier, not machine-checked, not refereed.

*Where the methods stop.* $deg F = k$, so the Gram basis degree must grow
with $k$, and the degree-counting obstruction that blocks the $k = n$ line at
even dimensions reappears in $k$; @sec-computational quantifies it. The line
$k = 3$ is tractable exactly because its degree budget is fixed while the
dimension grows. The local route of @sec-k4 stops where its merge does: at
$m = 5$ the one-sided step splinters into four cross invariants
(@sec-k4-merge), so $k = 5$ needs new ideas on the centred block, not more of
the same. The natural next targets are the open cells of @sec-k4-anchors by
the fixed-dimension method, and — a genuinely different question — whether
$k = 4$ admits the same uniform certificate treatment as $k = 3$
(@sec-computational).

= Data availability <sec-data>

The certificates as exact rational data, the objective builders, the
block-diagonalisation, the Sturm decision, the independent verifiers with their
positive and negative controls, and the Lean development are supplied as a
reproduction kit accompanying this paper. So are the two exact verifiers of
the newer parts — `graded_verify_stability.py` (@sec-stab-verify) and
`graded_verify_k4.py` (@sec-k4-verify) — together with the instrument modules
they declare and do not re-derive, and their stored logs. Its README carries
the file manifest, naming the claim each file backs and the procedure for
re-running each check. The failed design branches are retained there, because
@sec-negative is only checkable against them.

#v(1em)
#line(length: 100%, stroke: 0.4pt + luma(180))
#v(0.5em)

#text(9pt)[
  *Bibliography*

  [1] G.-S. Cheon and S.-G. Hwang, _Maximization of a matrix function related to
  the Dittert conjecture_, Linear Algebra and its Applications *165* (1992),
  153–165, `doi:10.1016/0024-3795(92)90234-2`.

  [2] M. Putinar, _Positive polynomials on compact semi-algebraic sets_, Indiana
  University Mathematics Journal *42* (1993), 969–984.

  [3] S.-G. Hwang, _On a conjecture of E. Dittert_, Linear Algebra and its
  Applications *95* (1987), 161–169. (Dittert's conjecture at $n = 3$.)

  [4] R. Sinkhorn, _A problem related to the van der Waerden permanent theorem_,
  Linear and Multilinear Algebra *16* (1984), 167–173.
  (Dittert's conjecture at $n = 2$.)

  [5] G.-S. Cheon and I. M. Wanless, _An update on Minc's survey of open problems
  involving permanents_, Linear Algebra and its Applications *403* (2005),
  314–342.

  [6] G.-S. Cheon and I. M. Wanless, _Some results towards the Dittert conjecture
  on permanents_, Linear Algebra and its Applications *436* (2012), 791–801,
  `doi:10.1016/j.laa.2010.08.041`. (Theorem 2.1 is Theorem E at $k = n$.)

  [7] G.-S. Cheon and I. M. Wanless, _An interpretation of the Dittert conjecture
  in terms of semi-matchings_, Discrete Mathematics *307* (2007),
  `doi:10.1016/j.disc.2007.01.008`. (Not consulted; no result here depends
  on it.)

  [8] Divya K. U. and K. Somasundaram, _Lih Wang's and Dittert's conjectures on
  permanents_, Special Matrices *12* (2024), 20240006,
  `doi:10.1515/spma-2024-0006`; cf. arXiv:2312.00464v1, whose abstract claims
  Dittert at $n = 4$. The published version makes no such claim.

  [9] Z. Pang, _Proof of Dittert's conjecture for dimensions $n gt.eq 17$_,
  arXiv:2606.01531 (1 June 2026). Preprint, no DOI, not refereed.

  [10] B. Kafidov, _Dittert's conjecture in dimension 16 via a joint-deficit
  scaling lemma_, arXiv:2607.19439 (21 July 2026). Preprint, no DOI, not
  refereed.

  [11] Public repositories claiming Dittert cases, all created 21–25 July 2026,
  none refereed, all accessed 28 July 2026:
  `123ljh0bot/Dittert_Conjecture_in_Dimension_4` ($n = 4$, Lean 4 with an SOS
  certificate); `pedromnasc/dittert-conjecture-proof` ($n = 4, 5, 8$–$16$, and
  the `subdittert/` package quoted in @sec-intermediate);
  `lueluelue2006/dittert-conjecture-draft` and
  `lueluelue2006/dittert-n7-extension`, attributed to Hongyuan Lu
  ($n = 6$–$15$). Each is at `https://github.com/` followed by the owner and
  name shown.

  [12] G.-S. Cheon and S. Yoon, _A note on the Dittert conjecture for permanents_
  (2006); G.-S. Cheon, _On the monotonicity of the Dittert function_ (1993). The
  remaining two of the five papers citing [1]; neither works on the
  generalisation.

  [13] J. B. Lasserre, _Global optimization with polynomials and the problem of
  moments_, SIAM Journal on Optimization *11* (2001), 796–817.

  [14] K. Gatermann and P. A. Parrilo, _Symmetry groups, semidefinite programs,
  and sums of squares_, Journal of Pure and Applied Algebra *192* (2004),
  95–128.

  [15] E. Levin and V. Chandrasekaran, _Any-dimensional polynomial optimization
  via de Finetti theorems_, arXiv:2507.15632 (2025).

  [16] The mathlib Community, _The Lean mathematical library_, CPP 2020.

  [17] H. Tverberg, _On the permanent of a bistochastic matrix_, Mathematica
  Scandinavica *12* (1963), 25–35.

  [18] S. Friedland, _A proof of a generalized van der Waerden conjecture on
  permanents_, Linear and Multilinear Algebra *11* (1982), 107–120.
  Zbl 0482.15003.

  [19] P. McCullagh, _An asymptotic approximation for the permanent of a
  doubly stochastic matrix_, arXiv:1205.5723 (2012). The centred-core
  expansions of $sigma_2, sigma_3, sigma_4$ in @sec-stab-core are his, and
  the degree-five reduction specialises his general formula.

  [20] G. P. Egorychev, _The solution of van der Waerden's problem for
  permanents_, Advances in Mathematics *42* (1981), 299–305.

  [21] D. I. Falikman, _A proof of van der Waerden's conjecture on the
  permanent of a doubly stochastic matrix_, Matematicheskie Zametki *29*
  (1981), 931–938.
]
