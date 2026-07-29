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
    The Cheon–Hwang Sub-Dittert Conjecture at $k = 3$,\
    for Every Dimension
  ]
  #v(0.4em)
  #text(11pt)[with a decomposition of the deficit uniform in $n$ and $k$]
  #v(0.8em)
  #text(11pt)[D C P Revere]
  #v(0.15em)
  #text(9pt)[dcprevere\@gmail.com]
  #v(0.4em)
  #text(9pt, style: "italic")[Draft — 29 July 2026]
]

#v(1em)

#block(inset: (x: 1.2cm))[
  #text(9.5pt)[
    *Abstract.* Cheon and Hwang conjectured in 1992 that
    $E_k (r) + E_k (c) - P_k (A) lt.eq 2 - k!\/n^k$ for every non-negative
    $n times n$ matrix of total sum $n$ and every $1 lt.eq k lt.eq n$, with
    equality only at $J_n\/n$; the endpoint $k = n$ is Dittert's conjecture. We
    prove the case $k = 3$ for every $n gt.eq 4$ — the inequality, the equality
    case, and a quantitative strengthening of both — by a single
    Positivstellensatz certificate whose nineteen symmetry-reduced coefficients
    are explicit rational functions of $n$. The strengthening is
    #set math.equation(numbering: none)
    $ (2 - 6\/n^3) - [E_3 (r) + E_3 (c) - P_3 (A)] gt.eq theta_2 (n) dot.c
      norm(A - J_n\/n)_F^2 $
    with $theta_2 (n) = (n^4 + 40 n^2 - 84 n + 40) \/ (n^5 (n-1)^3 (n-2))$, which
    contains the equality case as the special case where the left side
    vanishes. Together with Hwang's 1987 theorem at $n = 3$ this settles $k = 3$
    in every dimension. The proof is uniform in $n$ because the governing degree
    is $k$, not $n$: the symmetry-reduced program has the same $12 times 19$
    shape at every dimension, so its solution is computed once over $QQ(n)$.
    Positive definiteness of the two $n^2 times n^2$ Gram matrices is reduced in
    closed form — Bose–Mesner algebra of the rook's graph for one, the
    representation theory of $S_(n-1)$ for the other — to the positivity of ten
    rational functions of $n$ (nine independent; the tenth equals one of the
    other nine divided by $n$), each decided on $n gt.eq 4$ by a Sturm sequence
    over $QQ$.

    The $k = 3$ certificate sits inside an exact decomposition of the deficit
    that is uniform in $n$ and in $k$. The case $k = 2$, which is classical,
    follows from that decomposition in a few lines; we give the derivation and a
    machine-checked proof. We also formalise, for every $2 lt.eq k lt.eq n$, the
    confinement of any violator to a shrinking neighbourhood of the Birkhoff
    polytope — at $k = n$ this is Theorem 2.1 of Cheon and Wanless 2012, and the
    extension to all $k$ is a routine transfer of their method — together with
    the Newton and Maclaurin inequalities that the confinement consumes, neither
    of which is in Mathlib. Every result stated below as a theorem is proved in
    Lean 4 with no `sorry` and on Lean's standard axioms, and is cited by its
    declaration name.
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

== Support layers <sec-layers>

Every result above is stated with the layer it rests on, because in this corner
of the literature the distinction has recently been expensive.

- *Theorems A and C–F are proved in Lean 4*, on Lean's standard axioms, with no
  `sorry` anywhere in the development and no use of `native_decide`. @sec-lean
  states the verification standard precisely and pins it to a commit. Theorem A
  is Lean-proved in all three parts, equality case and stability bound included.
- *Corollary B* rests on Theorem A for $n gt.eq 4$ and on the published
  literature at $n = 3$.
- *The fixed-dimension certificates of @sec-anchors are not Lean-checked.* They
  are exact rational data accepted by an independent standalone verifier. They
  are recorded as anchors, and no theorem above depends on them.
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
  carrying the results of this paper contain 511 axiom-audited declarations: 377
  in `SubDittertK3.lean` and 7 in `RookSum.lean`, which together prove
  Theorem A; 21 in `SubDittertUniversal.lean` (Theorem C), 17 in
  `SubDittertK2.lean` (Theorem D), 37 in `SubDittertLinear.lean`, 13 in
  `SubDittertM.lean` and 6 in `SubDittertMaclaurin.lean` (Theorem E), and 33 in
  `NewtonInequalities.lean` (Theorem F). In `SubDittertK3.lean` the 377 are
  *every* named declaration in the file, so nothing in the file carrying
  Theorem A is left unaudited. The independent cross-check of @sec-newton adds
  12 more and is deliberately outside the build.
  #v(0.4em)
  In the other files the audits cover the results and their supporting lemmas
  rather than every private definition. That is not a gap: `#print axioms`
  reports the axioms of the *transitive closure* of a proof term, so auditing a
  theorem audits every definition and lemma the theorem rests on. No file
  contains a `sorry`, so nothing in any of them can acquire `sorryAx` from
  within; and an unaudited declaration on which no stated result depends cannot
  affect a stated result.
]

The development is built against Lean 4.14.0 and Mathlib `v4.14.0` [13].
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

= Computational evidence toward $k = 4$ and $k = 5$ <sec-computational>

#claimbox[
  *Support layer: exact rational computation with stored witnesses. Nothing in
  this section is a theorem of this paper, and nothing in it is Lean-checked.*
]

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

*What is proved.* Theorem A, for every $n gt.eq 4$, by an exact rational
certificate whose coefficients are rational functions of $n$, with definiteness
decided by Sturm sequences over $QQ$ and the identity verified independently at
six dimensions. Theorems C to F, in Lean, uniformly in $n$ and $k$. No
floating-point number enters any of these decisions: the numerics find
candidates, and every accepted statement is re-established over $QQ$ or over
$FF_p$.

*What kind of proof this is.* Theorem A is a computer proof, and a small one by
the standards of the genre — nineteen rational functions of $n$, of degree at
most 12. It is checkable in minutes at any fixed $n$. It conveys very little
insight into *why* the bound holds; @sec-design is the closest thing to an
explanation we can offer, and it is an explanation of the certificate's geometry
rather than of the inequality. Theorems C to F are ordinary mathematics that
happens to be machine-checked.

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
every $n$, the confinement at every $2 lt.eq k lt.eq n$, and Newton's and
Maclaurin's inequalities. @sec-standard states the standard and pins it to a
commit. What the machine does not check is that the Lean definitions say what
the 1992 paper says; @sec-chain item 2 is the argument that they do. We state
the division explicitly because "machine-checked" is otherwise an ambiguous
claim.

*What is not claimed.* No case with $k gt.eq 4$ beyond the fixed-dimension
certificate at $(5,4)$, which is not Lean-checked; no statement about general
$k$ beyond Theorems C and E; nothing refereed. The constant $theta_2 (n)$ of
@eq-thmA-stab is not claimed optimal (@sec-uniqueness). No novelty is claimed for
the identity of Theorem C, for the statement of Theorem D, for Theorem E, or for
Theorem F. We have not read Cheon and Wanless 2007 [7] and do not rely on it.

*On the priority claim.* @sec-priority records public dated claims on the $k = n$
endpoint that appeared within a single week of this work, three of them in public
repositories [11] with no corresponding preprint. To our knowledge Theorem A is
the first resolved case of the Cheon–Hwang conjecture with $2 < k < n$; the claim
covers public repositories as well as the indexed literature, and it is a
priority claim, not a claim of difficulty. Such a claim is perishable on a line
that has moved this fast, and it should be re-checked before this paper is
submitted anywhere.

*Where the method stops.* $deg F = k$, so the Gram basis degree must grow with
$k$, and the degree-counting obstruction that blocks the $k = n$ line at even
dimensions reappears in $k$; @sec-computational quantifies it. The line $k = 3$
is tractable exactly because its degree budget is fixed while the dimension
grows. The natural next targets are $(6,4)$ and $(6,5)$ by the fixed-dimension
method, and — a genuinely different question — whether $k = 4$ admits the same
uniform treatment as $k = 3$.

= Data availability <sec-data>

The certificates as exact rational data, the objective builders, the
block-diagonalisation, the Sturm decision, the independent verifiers with their
positive and negative controls, and the Lean development are supplied as a
reproduction kit accompanying this paper. Its README carries the file manifest,
naming the claim each file backs and the procedure for re-running each check. The
failed design branches are retained there, because @sec-negative is only
checkable against them.

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

  [13] The mathlib Community, _The Lean mathematical library_, CPP 2020.
]
