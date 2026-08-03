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
#let cap = math.op("cap")
#let supp = math.op("supp")

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
  #text(15pt)[The Cheon–Hwang Sub-Dittert Conjecture, in Full]
  #v(0.55em)
  #text(10pt, style: "italic")[
    one capacity chain for $3 lt.eq k lt.eq n-1$, the two endpoint lines,\
    and the equality case at every cell
  ]
  #v(1.1em)
  #text(10.5pt)[D C P Revere]
  #v(0.25em)
  #text(9pt)[dcprevere\@gmail.com]
  #v(0.25em)
  #text(8.5pt, style: "italic")[Draft — 3 August 2026]
  #v(0.9em)
  #line(length: 38%, stroke: 0.4pt + luma(140))
]

#v(0.5em)

#block(inset: (x: 1.0cm))[
  #text(9pt)[
    *Abstract.* Cheon and Hwang conjectured in 1992 that
    $E_k (r) + E_k (c) - P_k (A) lt.eq 2 - k!\/n^k$ for every non-negative
    $n times n$ matrix of total sum $n$ and every $1 lt.eq k lt.eq n$, with
    equality only at $J_n\/n$. The endpoint $k = n$ is Dittert's conjecture;
    on the doubly stochastic face the statement is the Tverberg–Friedland
    theorem, so all of the content sits off that face. We assemble a proof at
    every cell $(k,n)$ with $2 lt.eq k lt.eq n$, inequality and equality case
    alike, and we grade every line of the assembly separately because the
    lines do not have the same strength.

    One mechanism carries the interior. Border $A$ into a $(2n-k) times
    (2n-k)$ matrix whose permanent is $((n-k)!)^2 sigma_k (A)$, price its
    permanent below by its capacity, and pay the price with an entropy witness
    written down in closed form from $A$ itself. The engine of that step is
    refereed literature and is stated as such: Gurvits' capacity theorem, the
    sharp univariate extraction of Csikvári–Schweitzer and Brändén–Leake–Pak,
    and the Friedland–Gurvits derivation of the Friedland–Tverberg inequality.
    What is new here is the composition off the face: a closed form for the
    unrefined constant showing that its frontier is the single line $k = n-1$
    (Theorem F); an exact arithmetic identity showing that repricing the
    $n - k$ identical border rows as one degree-$(n-k)$ extraction pays the
    shortfall to the last digit at every $(k,n)$; and a strictness theorem
    giving $Phi_k (A) lt.eq 2 - gamma - (1 - theta) D(A)$ with
    $1 - theta gt.eq 0.7308$, so equality forces the doubly stochastic face,
    where Friedland's 1982 theorem finishes it. That covers
    $3 lt.eq k lt.eq n-1$ but four small cells, which the $k = 3$ and $k = 4$
    lines and one anchor certificate cover.

    The two endpoint lines are stated with their real provenance. At $k = 2$
    and $k = 3$ the results are kernel-checked in Lean 4. At $k = n$ the line
    is a chain of mixed grade — refereed at $n lt.eq 3$, our own independent
    certificates at $n = 4, 5$ (independent confirmation, not priority), and
    re-derived unrefereed preprints for $n gt.eq 6$ — and the assembled claim
    inherits that grade where it is made. We prove that the capacity chain
    cannot reach $k = n$, and reduce that line to a quantitative van der
    Waerden stability estimate which does not exist in the literature.
  ]
]

#v(0.5em)

= The conjecture, and what is claimed <sec-intro>

Let $K_n = { A in RR^(n times n) : A_(i j) gt.eq 0, sum_(i,j) A_(i j) = n }$,
and for $A in K_n$ let $r$ and $c$ be its vectors of row and column sums.
Write $sigma_k (A)$ for the sum of the permanents of all $k times k$
submatrices of $A$ — rows chosen from one $k$-subset, columns from another,
independently — and put
$ E_k (v) = frac(e_k (v), binom(n,k)), quad
  P_k (A) = frac(sigma_k (A), binom(n,k)^2), quad
  gamma(n,k) = frac(k!, n^k), quad
  Phi_k (A) = E_k (r) + E_k (c) - P_k (A), $
with $e_k$ the elementary symmetric function. Throughout, $Omega_n$ is the
doubly stochastic polytope, $m = n - k$, and
$ D(A) = 2 - E_k (r) - E_k (c) gt.eq 0 $ <eq-defD>
is the _line-sum deficit_; $D gt.eq 0$ and $D(A) = 0$ if and only if
$A in Omega_n$, by Maclaurin's inequality applied to $r$ and to $c$ (this
needs $k gt.eq 2$).

#block(fill: luma(250), inset: 8pt, radius: 3pt, width: 100%)[
  *The conjecture (Cheon and Hwang [1], 1992).* For every $A in K_n$ and every
  $1 lt.eq k lt.eq n$, $Phi_k (A) lt.eq 2 - gamma(n,k)$, with equality only
  at $A = J_n\/n$.
]

At $k = n$ one has $sigma_n = per$ and $E_n (v) = product_i v_i$, so the
statement reads
$product_i r_i + product_j c_j - per(A) lt.eq 2 - n!\/n^n$: _Dittert's
conjecture_ verbatim, Conjecture 28 of the Cheon–Wanless survey [3], open in
the refereed literature at every $n gt.eq 4$. At $k = 1$ the inequality is an
identity _on $K_n$_, since the difference is a constant multiple of
$sum_(i j) A_(i j) - n$; that case is excluded everywhere below. On
$Omega_n$ the deficit @eq-defD vanishes and the conjecture becomes
$sigma_k (A) gt.eq binom(n,k)^2 gamma(n,k)$ — the theorem conjectured by
Tverberg [7] and proved by Friedland [8], whose $k = n$ case is the van der
Waerden conjecture settled by Egorychev [9] and Falikman [10]. _So the entire
content of Cheon–Hwang lies off the doubly stochastic face_, and that is the
single fact organising this paper.

The known cases before this work were $k lt.eq 2$ at every $n$; every $k$ at
$n lt.eq 3$; $k = n$ at $n = 2$ (Sinkhorn [4]) and $n = 3$ (Hwang [5]); and
the line $k = 3$ at every $n gt.eq 4$, together with $k = 4$ at every
$n gt.eq 5$, from the companion paper [22]. The intermediate range
$2 < k < n$ had otherwise gone untouched.

#keybox[
  *Theorem 1 (the conjecture, at every cell).* For every $n gt.eq 2$, every
  $2 lt.eq k lt.eq n$ and every $A in K_n$,
  $ Phi_k (A) lt.eq 2 - frac(k!, n^k), $ <eq-main>
  with equality if and only if $A = J_n\/n$.
  #leanline[*The grade of this statement is composite, and the composite is
  only as strong as its weakest line.* The range $3 lt.eq k lt.eq n-1$ is
  @sec-capacity: exact-verifier grade on refereed imports. The lines $k = 2$
  and $k = 3$ are kernel-checked in Lean 4; the line $k = 4$ and the four
  exceptional cells are exact-verifier grade (@sec-endpoints). *The line
  $k = n$ is `[P]` for $n gt.eq 6$* — unrefereed preprints, every displayed
  inequality re-derived here in exact arithmetic, but not refereed
  (@sec-dittert). @eq-main therefore carries `[P]` wherever it is quoted as a
  statement about the whole plane.]
]

== How to read the grades <sec-grades>

Five layers are used, and no claim is allowed to inherit a neighbour's layer.

#figure(
  table(
    columns: (auto, auto),
    align: (left, left),
    stroke: tstroke,
    inset: 5pt,
    table.header([*layer*], [*what it means here*]),
    [kernel-checked],
      [proved in Lean 4 at a named commit, no `sorry`, no `native_decide`,
       `#print axioms` returning a subset of
       `[propext, Classical.choice, Quot.sound]`],
    [`[V]`],
      [verified in exact arithmetic over $QQ$ end to end, by a standalone
       verifier carrying fault-injection controls that must fire on mutated
       input and stay silent on clean input],
    [`[R]`],
      [refereed literature, quoted and used as stated],
    [`[P]`],
      [unrefereed public source, re-derived here in exact arithmetic — the
       mathematics was checked, the refereeing was not done],
    [`[I]`],
      [measured at floating-point grade; scouting only, and load-bearing
       nowhere in this paper],
    table.hline(stroke: 0.7pt + luma(40)),
  ),
  caption: [The support layers. Exact verification and machine checking are
    different things from refereeing, and weaker ones. Nothing in this paper
    is refereed, including this paper.]
) <grade-table>

== The map of the proof <sec-map>

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, left),
    stroke: tstroke,
    inset: 5pt,
    table.header([*region*], [*what carries it*], [*grade*]),
    [$3 lt.eq k lt.eq n-1$, minus four cells],
      [the capacity chain: @sec-capacity, Theorem 2],
      [`[V]` on `[R]`],
    [$k = 2$, every $n gt.eq 2$],
      [a manifest sum of squares; @sec-k2],
      [kernel-checked],
    [$k = 3$, every $n gt.eq 4$],
      [one certificate family in $QQ(n)$; @sec-k3, [22]],
      [kernel-checked],
    [$k = 3$, $n = 3$],
      [Hwang 1987 [5] (this is Dittert at $n = 3$)],
      [`[R]`],
    [$k = 4$, every $n gt.eq 4$],
      [(4,4) certificate, five anchors, one collar theorem; @sec-k4],
      [`[V]`],
    [$(k,n) = (5,6)$],
      [anchor certificate; @sec-cells],
      [`[V]`],
    [$k = n$, $n lt.eq 3$],
      [Sinkhorn [4], Hwang [5]],
      [`[R]`],
    [$k = n$, $n = 4, 5$],
      [our own anchor certificates; @sec-d45],
      [`[V]`],
    [$k = n$, $n gt.eq 6$],
      [three unrefereed preprints, re-derived; @sec-dittert],
      [`[P]`],
    table.hline(stroke: 0.7pt + luma(40)),
  ),
  caption: [Coverage of the $(k,n)$ plane, $2 lt.eq k lt.eq n$. The four cells
    excluded from the capacity range are $(k,n) = (3,4), (3,5), (4,5), (5,6)$,
    and each is covered by a row below it.]
) <map-table>

= The capacity chain <sec-capacity>

This section proves the conjecture, in full, on
$ R = { (k,n) : 3 lt.eq k lt.eq n-1 } without { (3,4), (3,5), (4,5), (5,6) }. $ <eq-region>
One mechanism does all of it. The engine is imported and is refereed; the
composition off the face, the frontier analysis, the exact payment and the
strictness theorem are the contribution.

== The bordered matrix and its capacity <sec-border>

For $2 lt.eq k lt.eq n$ put $m = n - k$, $N = 2n - k$, and
$ M_k (A) = mat(A, J_(n times m); J_(m times n), 0_(m times m)), quad
  per(M_k (A)) = (m!)^2 sigma_k (A). $ <eq-border>
In a permanent term of $M_k (A)$ the $m$ all-ones columns can only be covered
by $A$-rows and the $m$ all-ones rows only by $A$-columns, since the corner
block vanishes; so exactly $k$ $A$-rows meet $A$-columns, those index sets are
the pair $(alpha, beta)$, and the two leftover matchings contribute $m!$ each.
Write $p_M (x) = product_i (sum_j M_(i j) x_j)$, a product of linear forms
with non-negative coefficients, hence H-stable and homogeneous of degree $N$
in $N$ variables, with
$per(M) = partial^N p_M \/ partial x_1 dots.c partial x_N (0)$, and
$ cap(p) = inf_(x > 0) frac(p(x), x_1 dots.c x_N). $

#claimbox[
  *Lemma C (the capacity is constant on the face).* For every $A in Omega_n$
  and every $1 lt.eq k lt.eq n$,
  $ cap(M_k (A)) = cap_0 := frac(n^(2n-k), k^k), $
  attained at $x^* = (1, dots, 1, 1\/k, dots, 1\/k)$ with $n$ ones and $m$
  copies of $1\/k$.
  #leanline[`[V]`. The Legendre-type objective $log p_M (e^y) - sum_j y_j$ is
  convex, so the displayed stationary point is a global minimiser; both
  stationarity computations use only $r equiv c equiv 1$.]
]

Two consequences are worth stating at once. First, $d log cap \/ d A_(i j) =
k\/n$ at every $(i,j)$ on the face, so the directional derivative of
$cap(M_k (A))$ along any direction inside $K_n$ vanishes on $Omega_n$: _the
capacity is flat on the face_. Second, and for the same reason, any bound of
the form $sigma_k gt.eq c dot.c cap$ has _no slack at all_ at $J_n\/n$ and
must therefore be exactly tight there or fail outright. That is the whole
difficulty of the constant, and it is why the frontier of @sec-frontier is a
line rather than a region.

== The engine, and where it comes from <sec-engine>

#block(fill: luma(250), inset: 8pt, radius: 3pt, width: 100%)[
  *Provenance, stated up front.* The three inputs below are refereed or
  published literature and are not our results. Each was independently
  re-derived here in exact arithmetic — that is a check on our use of them,
  not a claim on them.

  #v(0.4em)
  *(E1) Gurvits' capacity theorem* [11]. For $p$ homogeneous, H-stable, of
  degree $N$ in $N$ variables with non-negative coefficients, with
  $C_i = min(deg_p (i), i)$,
  $ frac(partial^N p, partial x_1 dots.c partial x_N)(0) gt.eq cap(p) dot.c
    product_(2 lt.eq i lt.eq N) ((C_i - 1)\/C_i)^(C_i - 1). $

  *(E2) The sharp univariate extraction.* For $a_1, dots, a_n gt.eq 0$ and
  $f(S) = product_i (a_i + S) = sum_t c_t S^t$, and $0 lt.eq m lt.eq n$,
  $ c_m gt.eq G(n,m) dot.c inf_(S > 0) f(S)\/S^m, quad
    G(n,m) = frac(binom(n,m) m^m (n-m)^(n-m), n^n) tilde
    sqrt(frac(n, 2 pi m (n-m))), $ <eq-lemmaU>
  with equality at $a = (1, dots, 1)$. This is Csikvári–Schweitzer [13],
  Lemma 2.8 (attributed there to Gurvits [15]), and Brändén–Leake–Pak [14],
  Corollary 5.9, where sharpness is proved. It is _not_ ours.

  *(E3) The descent mechanism.* Multiplying by $L(x)^(n-k)$, which does not
  decrease capacity, to descend from the $m = 0$ case _is_ the Friedland–Gurvits
  proof of the Friedland–Tverberg inequality [12], Theorem 3.1 and
  Corollary 3.2 (2006). @sec-payment below is, in its mechanism, a
  rediscovery of that 2006 theorem.
]

Applying (E1) to $p_M$ with the labelling that parks the $m$ border columns at
the top labels — the optimal labelling, since $((d-1)\/d)^(d-1)$ decreases —
gives the _unrefined_ constant
$ per(M_k (A)) gt.eq C_"ref" (n,k) cap(M_k (A)), quad
  C_"ref" (n,k) = frac(n!, n^n) ((n-1)\/n)^((n-1)(n-k)), $ <eq-cref>
valid for every $A gt.eq 0$. Write
$rho_"ref" (n,k) = C_"ref" cap_0 \/ ((m!)^2 binom(n,k)^2 gamma)$ for the ratio
of the certified value at $J_n\/n$ to the true one. By the flatness just
noted, the chain runs at $(k,n)$ only if $rho_"ref" gt.eq 1$, and
$rho_"ref" lt.eq 1$ always.

== The frontier of the unrefined constant is a line <sec-frontier>

#keybox[
  *Theorem F (the frontier, exactly).* For every $n gt.eq 3$ and every
  $1 lt.eq k lt.eq n-1$,
  $ frac(rho_"ref" (n,k), rho_"ref" (n,k+1))
    = frac((1 + 1\/k)^k, (1 + 1\/(n-1))^(n-1)). $ <eq-thmF>
  Since $x mapsto (1 + 1\/x)^x$ is strictly increasing, $rho_"ref"$ is
  strictly increasing in $k$ and flat from $n-1$ to $n$; with
  $rho_"ref" (n,n) = 1$,
  $ rho_"ref" (n,n-1) = 1, quad
    rho_"ref" (n,k) = product_(i=k)^(n-2)
      frac((1 + 1\/i)^i, (1 + 1\/(n-1))^(n-1)) < 1
    quad "for every" k lt.eq n-2. $
  #leanline[`[V]` `graded_verify_capfrontier.py`: all 29 checks pass, all 10
  fault-injection controls fire. The ratio identity is verified over $QQ$ on
  3159 cells at $n = 4 dots 80$ and the product form at $n = 3 dots 49$; the
  closed form reproduces the earlier measured table digit for digit on all 21
  of its rows. _This is ours._]
]

Theorem F converts a measured table and an asymptotic guess into a theorem,
and the asymptotic $1 - rho_"ref" tilde (n-k)^2\/(4 n^2)$ falls out of it. It
also prices what a wider region would cost: reaching $k = n - j$ requires the
Gurvits constant to improve at the bordered degree profile by exactly
$1\/rho_"ref" (n, n-j)$ — a factor $1.00600$ at $(n,j) = (10,2)$, tending to
$1$ like $j^2\/(4n^2)$ at fixed $j$, but tending to
$1\/sqrt(c e^(1-c)) > 1$ along $k = c n$. So no limiting argument delivers the
interior, and a constant fraction of the plane costs a genuine constant-factor
strengthening of a van der Waerden-type bound. _One structural slack is
visible_: (E1) does not use that the $m$ border rows of $M_k (A)$ are
identical linear forms.

== The exact payment <sec-payment>

That slack is the whole of the gap, and paying it closes the gap exactly — not
asymptotically. The border variables enter $p_M$ only through their sum:
$ p_M (x, x_(n+1), dots, x_(n+m)) = L(x)^m product_(i lt.eq n) ((A x)_i + S),
  quad S = sum_(b) x_(n+b), quad L(x) = sum_(j lt.eq n) x_j, $
so the $m$-fold border derivative is $m! [S^m]$: _one_ coefficient extraction
from _one_ variable of degree $n$, which is exactly the situation of
@eq-lemmaU. The unrefined constant instead charges $((n-1)\/n)^(n-1)$ once per
border variable — it spends $m$ single-variable steps on a single extraction,
and the resulting loss $e^(-m)$ against $tilde 1\/sqrt(m)$ is entirely an
artefact of that choice.

#keybox[
  *Theorem G$'$ (refined constant).* For every $A gt.eq 0$,
  $ per(M_k (A)) gt.eq C_"new" (n,k) cap(M_k (A)), quad
    C_"new" (n,k) = frac(n!, n^n) dot.c frac(m! thin G(n,m), m^m), quad
    m = n - k. $

  *Theorem H$'$ (the collapse).* $C_"new" (n,k) cap_0
  = (m!)^2 binom(n,k)^2 gamma(n,k)$ _exactly_, i.e.
  $rho_"new" (n,k) = 1$ at _every_ $k$; equivalently
  $C_"new" \/ C_"ref" = 1\/rho_"ref"$ identically.
  #leanline[*Mechanism imported* — (E2) and (E3) of @sec-engine; the honest
  description of Theorem G$'$ is that it is Friedland–Gurvits [12] applied to
  this family. What is ours is the composition and the bookkeeping identity
  below. `[V]` `graded_verify_borderrows.py`: all 20 checks pass, all 7
  controls fire; $rho_"new" = 1$ on every cell $2 lt.eq k lt.eq n$,
  $n = 3 dots 44$, and $C_"new" = C_"ref"$ exactly at $m = 0, 1$.]
]

The proof of Theorem H$'$ is one line of arithmetic, and it is worth writing
out because a constant that closes to the last digit at every cell is rare.
Both sides reduce, using $(n - m)^(n-m) = k^k$, to
$ n! thin m! thin binom(n,m) = (m!)^2 binom(n,k)^2 k!
  quad (= (n!)^2 \/ k! "on both sides"), $ <eq-payment>
which is $binom(n,m) = binom(n,k)$ together with $binom(n,k) = n!\/(k! m!)$.
The identity is forced by the identical-rows structure: the same $m!$ that
appears in @eq-border as the two leftover matchings appears in @eq-lemmaU as
the extraction factor.

Two remarks, both recorded deliberately. First, $G(n,1) = ((n-1)\/n)^(n-1)$
and $G(n,0) = G(n,n) = 1$, so the refinement _reduces_ to @eq-cref exactly at
$m = 0, 1$ — the two lines where Theorem F says the unrefined labelling was
already sharp. Nothing is claimed where nothing was owed. Second, on
$Omega_n$ Theorem H$'$ reads $sigma_k (A) gt.eq binom(n,k)^2 gamma$, which is
Friedland–Tverberg. That agreement is _not_ corroboration: the derivation is
Friedland and Gurvits' own derivation of that inequality, so the check cannot
fail. It fixes the depth of the claim — the refined bound is exactly as strong
as a known sharp theorem on the face — and no evidential weight is placed on
it.

== The witness, and the region <sec-witness>

The chain has four steps, and all four are tight at $J_n\/n$:
#block(inset: (left: 6pt))[
  #set enum(numbering: n => [(S#n)])
  + $E_k (r) + E_k (c) = 2 - D(A)$ — the definition @eq-defD;
  + $P_k (A) gt.eq gamma dot.c cap(M_k (A))\/cap_0$ — Theorems G$'$/H$'$;
  + $cap(M_k (A)) gt.eq cap_0 exp(-(m\/n) sum chi)$ — the entropy witness;
  + $(m\/n) sum chi lt.eq D(A)\/gamma$ — the $chi$-comparison.
]

Step (S3) is where a lower bound on an infimum is needed, and a lower bound on
an infimum is a _dual feasible point_: a guess that only has to be checked,
never found. Let $W gt.eq 0$ be doubly stochastic with
$supp(W) subset.eq supp(M)$; then weighted AM–GM on each row, multiplied over
$i$ and using the column sums of $W$, gives
$cap(M) gt.eq product_(i,j) (M_(i j)\/W_(i j))^(W_(i j))$ — the easy half of
the classical scaling duality, proved here from scratch so that nothing
external is load-bearing at this step. The point that works is written down
from $A$ itself: for $A in K_n$ with $max_i r_i lt.eq n\/k$ and
$max_j c_j lt.eq n\/k$, put
$ W_(i j) = (k\/n) A_(i j), quad
  W_(i, n+b) = frac(1 - (k\/n) r_i, m), quad
  W_(n+a, j) = frac(1 - (k\/n) c_j, m), $
with the $m times m$ corner zero. Its row and column sums are $1$ in one line
each, and evaluating the witness with
$chi(t) = (1-t) log(1-t) + t = sum_(p gt.eq 2) t^p\/(p(p-1)) gt.eq 0$ gives
exactly (S3) with $chi$ evaluated at $(k\/m) R_i$ and $(k\/m) C_j$, where
$R = r - bold(1)$, $C = c - bold(1)$.

#claimbox[
  *The witness is exactly tight on the face.* At $R = C = 0$ every $chi$
  vanishes and the bound returns $cap_0$, which Lemma C says is the true
  value. So (S3) is not a lossy surrogate for the capacity; it _is_ the
  capacity on $Omega_n$, and the loss off the face is the explicit $chi$-sum.
  #leanline[`[V]` checked as an identity in the free $QQ$-module on
  ${log p : p "prime"}$, $n = 4 dots 9$, every $2 lt.eq k < n$, at $J_n\/n$,
  at permutation matrices and at off-face product points
  (`graded_verify_thmb.py`, all 32 checks pass, all 9 controls fire).]
]

The hypothesis $max(r_i, c_j) lt.eq n\/k$ has to be earned, and it is: on the
region $\{D < gamma\}$ — the only region where anything is owed, since
$D gt.eq gamma$ gives @eq-main outright from (S1) and $P_k gt.eq 0$ — an
exact extremal computation for
$hat(E)_k (u) = max { E_k (r) : r gt.eq 0, sum r = n, r_1 = u }$ pins every
line sum. Step (S4) then needs three rational conditions,
$ "(C1)" gamma lt.eq 1\/12, quad
  "(C2)" 3 gamma k^2 (n-1)^2 lt.eq (m(k-1))^2, quad
  "(C3)" gamma k^2 (n-1) lt.eq m (k-1)(1 - kappa), $
with $kappa = 3 gamma (k-2)(n-1)\/(k-1)^2$. These hold on exactly the region
@eq-region.

#claimbox[
  *The exclusion set, exactly.* (C1)–(C3) hold at every
  $3 lt.eq k lt.eq n-1$ except at $(k,n) = (3,4), (3,5), (4,5), (5,6)$.
  The cell set is infinite, so the infinite half is a lemma and not a table.
  Write $m = n-k$ and
  $ Lambda(n,k) = frac(gamma k^2 (n-1), m (k-1)), quad
    Xi(n,k) = frac(3 gamma k^2 (n-1)^2, (m (k-1))^2), $
  so that (C2) reads $Xi lt.eq 1$, (C3) reads $Lambda lt.eq 1 - kappa$, and
  $theta = Lambda\/(1 - kappa)$ in @eq-theta below.

  *Lemma T (the tail).* For every $n gt.eq 10$ and every
  $3 lt.eq k lt.eq n-1$, the conditions (C1), (C2) and (C3) all hold, and
  moreover $theta(n,k) lt.eq 144\/955 = 0.15078 dots < 1$.

  _Proof._ Five elementary steps over $QQ$, (T0)–(T4), and an assembly (T5).
  (T0) $gamma$ is non-increasing in $k$, since
  $gamma(n,k+1)\/gamma(n,k) = (k+1)\/n lt.eq 1$ on $k lt.eq n-1$; hence
  $gamma lt.eq gamma(n,3) = 6\/n^3$ across the strip, and
  $gamma lt.eq h!\/n^h$ with $h = floor(n\/2) + 1$ once $k gt.eq h$.
  (T1) $(k-1)^2 - 4(k-2) = (k-3)^2 gt.eq 0$, so $(k-2)\/(k-1)^2 lt.eq 1\/4$
  and $kappa lt.eq (3\/4) gamma (n-1) < 9\/(2n^2)$; at $n gt.eq 10$ this gives
  $1 - kappa > 191\/200$, so $theta$ is well defined and positive.
  (T2) Small $k$, $3 lt.eq k lt.eq n\/2$: then $m gt.eq n\/2$, $k-1 gt.eq k\/2$
  and $k-1 gt.eq 2k\/3$, whence $Lambda lt.eq 24k\/n^3 lt.eq 12\/n^2$ and
  $Xi lt.eq 27 gamma lt.eq 162\/n^3$.
  (T3) Large $k$, $n\/2 < k lt.eq n-1$: this is the dangerous side, where $m$
  may be $1$ and the $(n-k)$ in the denominator gives nothing, so the
  super-exponential decay of $gamma$ replaces it. With $gamma lt.eq h!\/n^h$
  and $k - 1 gt.eq (n-1)\/2$, $Lambda lt.eq B(n) := 2 n^2 h!\/n^h$ and
  $Xi lt.eq 6 B(n)$.
  (T4) $B(n+2) lt.eq B(n)$ for $n gt.eq 8$, since
  $B(n+2)\/B(n) lt.eq (n+4)(n+2)\/(2n^2) lt.eq 1$ once
  $n^2 - 6n - 8 gt.eq 0$; with $B(10) = 18\/125$ and
  $B(11) = 1440\/14641 < 18\/125$, induction along each parity class gives
  $B(n) lt.eq 18\/125$ for every $n gt.eq 10$.
  (T5) Assembly at $n gt.eq 10$. (C1): $gamma lt.eq 6\/n^3 lt.eq 6\/1000 < 1\/12$.
  (C2): $Xi lt.eq 162\/1000$ by (T2) and $Xi lt.eq 6 B(n) lt.eq 108\/125$ by
  (T3). (C3): $Lambda lt.eq max(12\/100, 18\/125) = 18\/125$, so
  $theta lt.eq (200\/191)(18\/125) = 144\/955$. $qed$

  The crossover is $n_1 = 10$, and the condition that fixes it is (C2), not
  (C3) — the opposite of the small-$n$ picture. (C3) alone would close from
  $n gt.eq 8$, where $B(8) = 15\/32$ gives $theta lt.eq 60\/119 < 1$; but
  (T3)'s certificate for (C2) is $6B(n)$, and $6B(8) = 45\/16$ and
  $6B(9) = 160\/81$ both exceed $1$. So the exact finite part is the 21 cells
  with $4 lt.eq n lt.eq 9$, decided cell by cell over $QQ$, of which exactly
  the four listed fail. Lemma T is a ceiling and not a value: the true maximum
  of $theta$ on the tail is $0.03618 dots$ at $(k,n) = (3,10)$, a factor
  $4.2$ under $144\/955$, and it falls away super-exponentially after that.
  What the lemma buys is reach, not sharpness; the tight corner of $R$ is not
  in the tail at all, but at $(k,n) = (6,7)$ inside the finite part.
  #leanline[`[V]` `graded_verify_strict.py` block [6]: (T0)–(T5) are each
  re-checked as the inequality each one is, over the 12403 cells with
  $n lt.eq 160$, together with the crossover $n_1 = 10$, the 21 exact cells
  below it, and the resulting global maximum $155520\/577877$ at
  $(k,n) = (6,7)$; the direct sweep of (C1)–(C3) over $QQ$ runs independently
  to $n lt.eq 300$. Three of the verifier's eight mutation controls target
  Lemma T alone: the crossover pushed down (the certificate fails at every
  $n_1 < 10$), the finite part truncated (6 orphan cells at $n = 9$), and (T3)
  run on the polynomial cap $6\/n^3$ in place of $h!\/n^h$ (which certifies
  nothing at $n = 10$). _A published
  earlier reading of this computation said all four failures were (C2)-only;
  that is false at $(3,4)$, where $gamma = 3\/32 > 1\/12$ and (C1) and
  (C3) fail too. Three of the four are (C2)-only. The exclusion set itself
  is unchanged, and no statement depends on which condition fails._]
]

== Strictness off the face <sec-strict>

Steps (S1)–(S4) give the inequality @eq-main on the region @eq-region, but not
the equality case: the
certified chain is tight along the whole of $Omega_n$, so it cannot by itself
distinguish $J_n\/n$ from any other doubly stochastic matrix. The equality
half comes from noticing that (S4) was proved with a margin that was thrown
away when it was stated as a yes/no condition. The (C1)(C2)(C3) analysis in
fact proves
$ (m\/n) sum chi lt.eq theta(n,k) dot.c D(A)\/gamma, quad
  theta(n,k) = frac(gamma k^2 (n-1), (n-k)(k-1)(1 - kappa)), quad
  kappa = frac(3 gamma (k-2)(n-1), (k-1)^2), $ <eq-theta>
and (C3) is the statement $theta lt.eq 1$.

#keybox[
  *Theorem E (strictness, with a deficit slope).* Let $(k,n) in R$ and
  $A in K_n$. Then
  $ D(A) < gamma: quad & Phi_k (A) lt.eq 2 - gamma - (1 - theta(n,k)) D(A), \
    D(A) gt.eq gamma: quad & Phi_k (A) lt.eq 2 - D(A), $
  and $theta(n,k) < 1$. Consequently $Phi_k (A) = 2 - gamma$ forces
  $D(A) = 0$, i.e. $A in Omega_n$.
  #leanline[`[V]` `graded_verify_strict.py`: all 42 checks pass, all 8 controls
  fire. $theta < 1$ on all 6899 cells of $R$ with $n lt.eq 120$, and on every
  cell of $R$ by Lemma T, whose steps (T0)–(T5) the same verifier re-checks;
  the
  equivalence of (C3) with $theta lt.eq 1$ recomputed over $QQ$ with zero
  mismatches for $n lt.eq 400$; Theorem E measured against $Phi_k$ rebuilt
  from the definition at 81 off-face points, tightest slack
  $9.80 times 10^(-6)$. _Two precision points are stated rather than buried._
  (C3) is $theta lt.eq 1$, not $theta < 1$; the strict inequality is an
  extra fact, and it is true — $theta = 1$ at no cell of $R$. And $theta$ is
  proved, not proved sharp: halving it leaves every check of the verifier
  passing, and the Hessian of $P_k - gamma + theta D$ at $J_n\/n$ restricted
  to ${sum b = 0}$ is positive _definite_, so the bound has genuine
  second-order room at the equality point.]
]

_Proof._ Near branch: (S1) and (S2) give
$Phi_k lt.eq 2 - D - gamma cap\/cap_0$; then (S3), $e^(-x) gt.eq 1 - x$, and
the sharpened @eq-theta give
$cap\/cap_0 gt.eq 1 - theta D\/gamma$. Far branch:
$Phi_k = 2 - D - P_k lt.eq 2 - D lt.eq 2 - gamma$, strict when $D > gamma$. At
$D = gamma$ exactly, equality would need $P_k = 0$, i.e. $sigma_k (A) = 0$; by
König's theorem the support then has no $k$-matching, so a vertex cover of at
most $k-1$ lines carries all the mass $n$, so some line sum is at least
$n\/(k-1)$, whence $D gt.eq 4\/(3(n-1)^2) > 6\/n^3 gt.eq gamma$ — a
contradiction. Finally $D(A) = 0$ iff $r = c = bold(1)$, by Maclaurin
equality. $qed$

The slope is never small. Exactly,
$ 1 - theta = 422357\/577877 = 0.7308769859 dots
  quad "at the worst cell" (k,n) = (6,7), $
and $1 - theta = 0.861644$ at $(7,8)$, $0.966897$ at $(9,10)$, tending to $1$.
That $(6,7)$ is the worst cell of the whole of $R$, and not merely of the
swept part, is Lemma T: its tail ceiling $144\/955$ sits below
$155520\/577877$, so the maximum found in the finite part is the global one.
So off the face $Phi_k$ falls below $2 - gamma$ by at least $0.73 thin D(A)$
everywhere on $R$.

== The face, and the theorem <sec-face>

On $Omega_n$ the deficit vanishes and $Phi_k = 2 - P_k$, so
$Phi_k = 2 - gamma$ there is exactly $sigma_k (A) = binom(n,k)^2 gamma$.

#claimbox[
  *Import (Friedland 1982 [8]).* For $2 lt.eq k lt.eq n$, $sigma_k$ on
  $Omega_n$ attains its minimum $binom(n,k)^2 gamma(n,k)$ _only_ at
  $A = J_n\/n$.
  #leanline[`[R]`, and cited alone. Friedland–Gurvits [12] Corollary 3.2 gives
  a second, capacity-based proof, but its equality clause is preprint-grade —
  the hypothesis of Theorem 3.1 there carries a typographical error, the
  equality sentence is ungrammatical, and the $m = n$ equality case is
  deferred elsewhere — so no weight is placed on it. At $k = 1$ the
  uniqueness genuinely fails, $sigma_1 equiv n$ on $Omega_n$; hence
  $k gt.eq 2$ throughout.]
]

#keybox[
  *Theorem 2 (the conjecture on the capacity region).* For every
  $(k,n) in R$ as in @eq-region and every $A in K_n$,
  $Phi_k (A) lt.eq 2 - k!\/n^k$, with equality if and only if
  $A = J_n\/n$. Quantitatively, $Phi_k (A) lt.eq 2 - gamma - 0.73 thin D(A)$
  whenever $D(A) < gamma$.
  #leanline[`[V]` on `[R]` imports (E1)–(E3) and Friedland [8]. Verifiers:
  `graded_verify_capfrontier.py` (29 checks, 10 controls),
  `graded_verify_borderrows.py` (20, 7), `graded_verify_thmb.py` (32, 9),
  `graded_verify_strict.py` (42, 8). _Not kernel-checked and not soon
  formalisable_: (E1) needs H-stable polynomials and the full Gurvits
  induction, and Friedland's theorem is a rock of the same size
  (@sec-machine).]
]

_What Theorem 2 does not give._ A stability constant in the doubly centred
directions. $D$ vanishes identically on $Omega_n$, so for a perturbation with
zero row and column sums the deficit of Theorem E is $0$ and this route says
nothing at all. The quantitative record in those directions is @sec-thresholds,
which is a different machine.

= The endpoint $k = 2$, the low lines, and the four exceptional cells <sec-endpoints>

== $k = 2$, every $n gt.eq 2$ <sec-k2>

#claimbox[
  *Theorem D.* $Phi_2 (A) lt.eq 2 - 2\/n^2$ for every $A in K_n$, with
  equality only at $J_n\/n$. With $kappa = 2\/(n(n-1))$ and $b = A - J_n\/n$
  the deficit is a manifest sum of squares on $\{sum_(i j) b_(i j) = 0\}$:
  $ (2 - 2\/n^2) - Phi_2 (A) = 1/2 [ kappa^2 norm(b)^2
      + kappa (1 - kappa) (norm(R)^2 + norm(C)^2) ]. $
  #leanline[Kernel-checked: `SubDittertK2.subDittert_k2`. _The statement is
  classical_; the contributions are the derivation from the uniform layer
  identity and the machine-checked proof. Since $kappa > 0$ and
  $kappa lt.eq 1$ for $n gt.eq 2$, the right side vanishes only at $b = 0$,
  which is the equality case.]
]

A second, independent fact pins the same line. At $k = 2$ the critical system
of $Phi_2$ solves in closed form on the whole affine hyperplane
$\{sum a_(i j) = n\}$ — not merely on $K_n$ — and its only solution is
$J_n\/n$: constancy of the gradient forces
$a_(i j) = alpha - (binom(n,2) - 1)(r_i + c_j)$, summing over $j$ forces every
$r_i$ equal, and the mass constraint finishes it. `[V]`

== $k = 3$, every $n gt.eq 3$ <sec-k3>

#claimbox[
  *Theorem A ([22]).* For every $n gt.eq 4$ and every $A in K_n$,
  $E_3 (r) + E_3 (c) - P_3 (A) lt.eq 2 - 6\/n^3$, with equality if and only
  if $A = J_n\/n$; and more precisely
  $ (2 - 6\/n^3) - Phi_3 (A) gt.eq theta_2 (n) norm(A - J_n\/n)_F^2, quad
    theta_2 (n) = frac(n^4 + 40 n^2 - 84 n + 40, n^5 (n-1)^3 (n-2)) > 0. $
  With Hwang's theorem [5] at $n = 3$ the line is closed at every $n gt.eq 3$.
  #leanline[Kernel-checked: `SubDittertK3.subDittert_k3_full`, all three parts
  in one theorem, at commit `32c811e`. _The $n = 3$ cell is refereed
  literature, not Lean_: this line's support is Lean plus the published
  theorem, and the corollary must not be cited as a single-layer result.]
]

== $k = 4$, every $n gt.eq 4$ <sec-k4>

The line is closed by three different things, and none of them inherits the
grade of another. At $n gt.eq 10$ it is a theorem of the collar route: a
violator is confined to a neighbourhood of $Omega_n$, a collar matrix splits
orthogonally into a line-sum block and a doubly centred block, the centred
block is governed by a stability form of the Tverberg–Friedland theorem, and
the five cross terms between the blocks have exact reductions. At
$5 lt.eq n lt.eq 9$ it is five fixed-dimension certificates at anchor grade.
At $n = 4$ — which is the Dittert cell $(4,4)$ — it is the certificate of
@sec-d45.

_Anchor grade_ means an exact rational certificate accepted in full by six
checks of a standalone verifier: the bound; $sigma_k$ by two structurally
different algorithms; the identity by _full_ coefficient comparison;
definiteness of the assembled Gram matrices by exact $L D L^T$ over $QQ$;
equality only at $J_n\/n$; and mutation tests rejected. Anything less is
stated as what it is.

#figure(
  table(
    columns: (auto, auto, auto),
    align: (center, left, left),
    stroke: tstroke,
    inset: 4.5pt,
    table.header([*cell*], [*bound settled on $K_n$*], [*support*]),
    [$(4,4)$], [$Phi_4 lt.eq 61\/32$],
      [anchor grade; both assembled $152 times 152$ Gram matrices positive
       definite over $QQ$; identity over 1,040 monomials (@sec-d45)],
    [$(4,5)$], [$Phi_4 lt.eq 1226\/625$],
      [anchor grade; 26 exact $L D L^T$ factorisations of size 350],
    [$(4,6)$], [$Phi_4 lt.eq 107\/54$],
      [anchor grade; identity over 40,386 coefficients, cone size 702],
    [$(4,7)$], [$Phi_4 lt.eq 4778\/2401$],
      [anchor grade; 156,555 coefficients, positivity by congruence],
    [$(4,8)$], [$Phi_4 lt.eq 1021\/512$],
      [anchor grade; 496,448 coefficients, cone size 2144],
    [$(4,9)$], [$Phi_4 lt.eq 4366\/2187$],
      [anchor grade; 1,355,805 coefficients, cone size 3402],
    [$n gt.eq 10$], [$Phi_4 lt.eq 2 - 24\/n^4$],
      [Theorem H of [22]: written proof plus the exact verifier
       `graded_verify_k4.py`; _not_ kernel-checked],
    table.hline(stroke: 0.7pt + luma(40)),
  ),
  caption: [The line $k = 4$. In every row equality holds only at $J_n\/n$.]
) <k4-table>

== The four exceptional cells <sec-cells>

The cells excluded from @eq-region are $(k,n) = (3,4), (3,5), (4,5), (5,6)$.
The first two are $k = 3$ cells and fall under @sec-k3; the third is $(4,5)$
in @k4-table. The fourth is an anchor of its own.

#claimbox[
  *The $(5,6)$ anchor.* $Phi_5 (A) lt.eq 643\/324 = 2 - 5!\/6^5$ on $K_6$,
  with equality only at $J_6\/6$.
  #leanline[`[V]`, anchor grade, six checks. The companion cells $(5,5)$ —
  which is also the Dittert cell $n = 5$ — and $(5,7)$ are recorded in
  @sec-d45 and in the data kit; no statement here rests on $(5,7)$.]
]

So the whole of $2 lt.eq k lt.eq n-1$ is covered, at the grades of
@map-table. One line remains.

= The line $k = n$: Dittert's conjecture <sec-dittert>

This is the line whose grade the whole assembly inherits, and it is stated
here with its provenance rather than with its verdict.

#figure(
  table(
    columns: (auto, auto, auto, auto),
    align: (center, left, center, left),
    stroke: tstroke,
    inset: 4.5pt,
    table.header([*$n$*], [*source of record*], [*grade*], [*what carries it*]),
    [$2$], [Sinkhorn 1984 [4]], [`[R]`], [refereed],
    [$3$], [Hwang 1987 [5]], [`[R]`], [refereed],
    [$4$], [our anchor certificate], [`[V]`],
      [six checks; both assembled $152 times 152$ Gram matrices positive
       definite over $QQ$. _No refereed proof exists; the first public claim
       is the July 2026 assembly's [20]_],
    [$5$], [our anchor certificate], [`[V]`],
      [six checks; both assembled $350 times 350$ Gram matrices positive
       definite over $QQ$],
    [$6 lt.eq n lt.eq 15$], [Lu, revision 2.0 [17]], [`[P]`],
      [every analytic step re-derived by hand, every constant reproduced as an
       exact rational, 98 four-variable certificates re-certified, 3 Bernstein
       trees node for node, 129 exact comparisons across $8 lt.eq n lt.eq 15$ with zero
       failures],
    [$16$], [Kafidov [19]], [`[P]`], [full re-derivation; all exact rational
      bounds reproduce],
    [$gt.eq 17$], [Pang [18]], [`[P]`], [full re-derivation; every constant
      reproduces exactly],
    table.hline(stroke: 0.7pt + luma(40)),
  ),
  caption: [The $k = n$ line. `[V]` means _we_ checked it, not that anyone
    refereed it; `[P]` means an unrefereed public source whose mathematics we
    re-derived. Dittert's conjecture is described in the current refereed
    literature as unsettled, and this table does not change that.]
) <dittert-table>

#block(fill: luma(250), inset: 8pt, radius: 3pt, width: 100%)[
  *Priority at $n = 4$, stated plainly.* The cell $n = 4$ has no refereed
  proof — Cheon–Wanless [3] p. 792 records it as "still open for
  $n gt.eq 4$", and Pang's Remark 2 repeats it. It is nonetheless _not first
  here_: the July 2026 public assembly [20] already contains an $n = 4$
  certificate, and that is the first public claim. The certificate of
  @sec-d45 is *independent confirmation at anchor grade, not priority.* The
  same wording applies at $n = 5$.
]

== Why the capacity chain cannot reach $k = n$ <sec-kn>

At $k = n$ one has $m = 0$, $cap_0 = 1$, $M_n (A) = A$, and Theorem H$'$ is a
literal no-op: $C_"new" (n,n) = C_"ref" (n,n) = n!\/n^n$ exactly, `[V]` for
$n = 2 dots 44$. Both facts that make the line look reachable —
$rho_"ref" (n,n) = 1$ and $G(n,0) = 1$ — are true and neither helps. The
reason is a theorem, not a missing estimate.

#claimbox[
  *Lemma K1.* For every $A in K_n$, $cap(A) lt.eq product_i r_i lt.eq 1$, and
  $cap(A) = 1$ _if and only if_ $A in Omega_n$.
]

So step (S3) at $k = n$ asserts $cap(A) gt.eq 1$, which is _exactly the
hypothesis $A in Omega_n$_: not a weak estimate but a false one at every
off-face point. This is what the border was doing all along — at $m gt.eq 1$
the witness of @sec-witness dumps the line-sum deficit into the border block;
at $m = 0$ there is nowhere to put it. (Step (S4) at $m = 0$ is the vacuous
$0 lt.eq D\/gamma$, so the conditions (C2), (C3) are symptoms and not the
break.) On $Omega_n$ itself the chain is exact and refereed: $per(A) gt.eq
gamma$ with equality only at $J_n\/n$. The `[P]` grade attaches to
$K_n without Omega_n$ — which is the whole of Dittert's difficulty, so this is
a restatement and not a reduction.

Replacing the witness by the exact capacity reduces all of $k = n$ to one
statement, and that statement is false.

#keybox[
  *Theorem K.* The inequality
  $gamma (1 - cap(A)) lt.eq D(A)$, for $A in K_n$ with $D(A) < gamma$, is
  FALSE at every $n gt.eq 2$, with exact rational witnesses that are strictly
  positive, fully indecomposable, and at which the capacity infimum is
  attained.

  *Theorem K$'$ (the sharp criterion).* Near $A_0 in Omega_n$ that inequality
  holds _if and only if_ $gamma lt.eq 1 - sigma_2 (A_0)^2$, with $sigma_2$ the
  second largest singular value.
  #leanline[`[V]` `graded_verify_kn.py`: all 35 checks pass, all 9 controls
  fire. Witnesses $A(n,epsilon,t) = (1-epsilon) I_n + (epsilon\/n) J_n
  + t(E_(12) - E_(11))$ with $D = t^2$ exactly, $epsilon = gamma\/5$, at
  $n = 2 dots 7$; the measured threshold is $epsilon^* = 1 - sqrt(1 - gamma)$
  to nine places. The witnesses are strictly positive, so every column degree
  is $n$ and the degree-refined form of (E1) gives exactly $n!\/n^n$: _the
  refutation survives the strongest form of the imported engine._]
]

Since $sigma_2 arrow.r 1$ at every permutation matrix and at every
decomposable point, the criterion fails on an open neighbourhood of the
permutation matrices at every $n gt.eq 2$. The structural reason is worth
stating plainly: $cap equiv 1$ on _all_ of $Omega_n$, while Dittert's own
margin $per(A) - gamma$ ranges over the whole of $[0, 1 - gamma]$ there. A
route whose value on the equality manifold is constant cannot tell $J_n\/n$
from $I_n$, so it must survive the worst off-face capacity decay uniformly
over that manifold — and that decay is unbounded. Consistently with this,
no analogue of Theorem E exists at $k = n$ with any $theta < 1$: the deficit
there is $gamma(cap - 1) lt.eq 0$.

== The reduction: what would make this line self-contained <sec-reduction>

Step (S2) is lossy in exactly one identifiable way. The exact statement is
$per(A) = cap(A) per(B)$ for the Sinkhorn scaling $A = D_1 B D_2$ with
$B in Omega_n$, and (S2) replaces $per(B)$ by its van der Waerden floor
$gamma$. Keeping $per(B)$, the requirement holds locally at _every_ face
point: $per(B) - gamma > 0$ off $J_n\/n$, and at $J_n\/n$ the two vanishing
orders match.

#keybox[
  *Theorem R (the reduction).* The missing input at $k = n$ is a
  _quantitative van der Waerden stability estimate_ — $per(B) - n!\/n^n$
  bounded below in terms of $1 - sigma_2 (B)^2$ for $B in Omega_n$ — and not
  a capacity estimate at all. Any such estimate, composed with Theorem K$'$,
  makes the line $k = n$ self-contained at the grade of @sec-capacity.
  #leanline[`[V]` for the factorisation and the composition arithmetic
  (`graded_verify_kn.py`). *No such estimate exists in the literature.* A
  search of the Gurvits capacity line, Brändén–Leake–Pak, Schrijver,
  Linial–Samorodnitsky–Wigderson, the quasirandom Latin square line and the
  Dittert-specific literature returned nothing of the form
  $per(B) gt.eq n!\/n^n + c dot.c "dist"(B, J_n\/n)^2$ or any
  $sigma_2$-indexed variant; and _no capacity-based approach to Dittert
  appears anywhere_. The successful classical route uses a pair of
  _structural_ theorems instead — Knopp–Sinkhorn [16] on the zero face and
  Hwang 1986 [6] in the positive-support case, with the Cheon–Wanless
  dilation between them — and neither is indexed by $sigma_2$.]
]

Two cheap versions of the missing half are recorded as closed. The exact
factorisation $cap(A) per(B) gt.eq gamma - D(A)$ is _literally_ Dittert's
conjecture, checked as an identity of statements, so all content lies in
bounding the two factors separately — and Theorem K says the trivial choice
fails. And the scale-invariant strengthening of Gurvits that would give
Dittert in one line,
$ "(S′)" quad per(A) gt.eq (n!\/n^n) product_i r_i product_j c_j
  quad "for every" A in K_n, $
is false, and false inside $\{D < gamma\}$, the only region that matters: at
$n = 3$, with $A$ the matrix with rows $(0, 1\/2, 1\/6)$, $(1\/2, 0, 5\/6)$,
$(1\/6, 2\/3, 1\/6)$, one has $p = 8\/9$, $q = 49\/54$,
$D = 11\/54 = (11\/12) gamma < gamma$ and $per(A) = 1\/6 < gamma p q =
392\/2187$, a ratio of $0.929847$. `[V]` exactly over $QQ$; Dittert itself
holds there with margin $4\/27$. (S′) is tight on the whole rank-one family
and at $J_n\/n$, which is why it is worth refuting rather than ignoring.

= Results of independent interest <sec-independent>

Three by-products stand on their own, and one of them supplies exactly what
@sec-capacity cannot.

== Unconditional thresholds, with stability <sec-thresholds>

The capacity route gives no constant in the doubly centred directions. A
different machine does: confinement traps a violator in a collar of the
Birkhoff polytope, a uniform stability form of the Tverberg–Friedland theorem
governs the centred block, and a layer budget prices every cross term.

#keybox[
  *Theorem U (thresholds with stability).* For every $k gt.eq 3$ and every
  $n gt.eq tilde(N)(k)$, every $A in K_n$ satisfies
  $Phi_k (A) lt.eq 2 - k!\/n^k$, with equality only at $J_n\/n$, and
  quantitatively
  $ (2 - gamma) - Phi_k (A) gt.eq c_U (n,k) norm(A - J_n\/n)_F^2,
    quad c_U (n,k) > 0 "explicit". $
  The $eta$-priced thresholds
  $ tilde(N)(5 dots 12) = 29, 35, 43, 53, 63, 75, 88, 102 $
  are _unconditional_.
  #leanline[`[V]`, composed from parts of mixed grade, and the composition is
  the object verified (`graded_verify_universal.py`, 301 checks;
  `graded_verify_uniformG.py`; `graded_verify_collar.py`). Three links are
  kernel-checked — the layer identity, confinement, and Newton/Maclaurin — and
  the rest are written proofs with exact verifiers behind them. The thresholds
  are unconditional because the connected-cumulant bound $|S_G (B)| lt.eq Q$
  is now proved for every pattern of at most twelve edges (@sec-cores); the
  range $k gt.eq 13$ remains conditional on one further core lemma.
  $tilde(N)(k)$ is a threshold _for this argument_ and is not claimed
  optimal.]
]

This is the campaign's only quantitative-stability record, and it is the one
place where the near-diagonal corner is _not_ reached: the wedge
$k + 1 lt.eq n < tilde(N)(k)$ is untouched by Theorem U and is covered, in
this paper, by @sec-capacity instead. The two machines are complementary in
exactly that sense.

== The core census and L-CUT <sec-cores>

The obstruction to the local calculus behind Theorem U is a combinatorial
object that appears to be new: a _core_, a simple graph of minimum degree
$gt.eq 3$, first realised at edge count $e_min (H) = 2 e(H) - "maxcut"(H)$.

#claimbox[
  *Theorem (census).* There are exactly eleven cores realisable at
  $e lt.eq 12$, and exactly forty-one at $e lt.eq 14$. The first
  $3$-connected cores are the wheel $W_4$ at $e = 10$ and the prism at
  $e = 11$ — _not_ the cube.

  *Theorem (L-CUT at $e lt.eq 14$).* One inequality schema subsumes the four
  separate core lemmas: split a core at a separator $S$ with
  $V - S = A union.sq B$, pay the edges inside $S$ pointwise, and bound each
  side in $ell^2$. The covering condition $N(A) - A = N(B) - B = S$ is not a
  convenience but is _forced_ by the $ell^2$ step. Of the forty-one cores at
  $e lt.eq 14$, exactly two are complete and the other thirty-nine admit a
  covering split with both sides at most two vertices, in only three side
  shapes; $K_4$ is a wheel, so $K_5$ is the unique hole, and it is first
  realised at $e = 14$.
  #leanline[`[V]` `graded_verify_u5core3.py` (727 checks, 6 controls firing at
  30 positions) and `graded_verify_canon.py` (2106 checks, 4 controls at 12
  positions); the sweeps at $e = 8 dots 12$ certify $127, 317, 1018, 2989,
  9930$ isomorphism classes with none uncertified, which is what makes
  $e_0 = 12$ and the thresholds above unconditional. A separate delineation
  result: the bound is _false_ without the entry bound
  $b_(i j) gt.eq -1\/n$, with an explicit nine-edge witness whose core is
  empty — so the failure is in leaf propagation, not core structure. This
  material may be published separately; it is stated here at pointer level.]
]

== Dittert at $n = 4$ and $n = 5$ <sec-d45>

Both cells carry exact sum-of-squares certificates produced and verified here,
at the full six-check anchor standard, including equality only at $J_n\/n$.

#figure(
  table(
    columns: (auto, auto, auto),
    align: (center, left, left),
    stroke: tstroke,
    inset: 4.5pt,
    table.header([*cell*], [*what was produced*], [*what checked it*]),
    [$(5,5)$],
      [$440$ unknowns, $87$ rows, $21$ canonical blocks; strictly feasible at
       round $0$, least block eigenvalue $+1.913166 times 10^(-5)$],
      [identity over 14,005 monomials, full coefficient comparison over $QQ$;
       both assembled $350 times 350$ Gram matrices positive definite over
       $QQ$, least pivots $1.1546 times 10^(-4)$ and
       $3.1719 times 10^(-5)$],
    [$(4,4)$],
      [$423$ unknowns; the 21-block design _does not exist_ at $n = 4$, so the
       certificate came from the early-exit arm],
      [identity over 1,040 monomials; both assembled $152 times 152$ Gram
       matrices positive definite over $QQ$, with no multiplicity count
       anywhere in the chain],
    table.hline(stroke: 0.7pt + luma(40)),
  ),
  caption: [The two Dittert cells settled here. Independent confirmation of
    the July 2026 assembly's $n = 4$ claim, not priority.]
) <d45-table>

Two details are load-bearing for the grade. The check that distinguishes
$k = n$ from $k = n-1$ cannot be the bound itself:
$k!\/n^k = (k-1)!\/n^(k-1)$ exactly when $k = n$, so at $(5,5)$ the tested
bound $1226\/625$ is also $2 - 4!\/5^4$ and carries no $k$-information
whatever. The discriminating evidence is the coefficient count — 14,005
monomials at $(5,5)$ against 7,875 at $(5,4)$ — typed in from an independently
derived closed form _before_ the run, the same closed form having reproduced
7,875, 40,386 and 809,529 at three other cells. A $k = 4$ certificate could
not have passed. And the cell data at $(5,5)$ came from a cache that predated
the work, so it was rebuilt from scratch and compared: identical to the fresh
$k = 5$ build, and different from the $k = 4$ cell in 3 of 87 constraint rows
and 18 of 87 right-hand sides.

= Verification <sec-verification>

== What a graded verifier is <sec-verifier>

Every displayed constant in this paper is produced by a verifier that computes
in exact rational arithmetic end to end, with no floating-point number
entering any decision — floats appear in format strings and nowhere else. That
is necessary and not sufficient, so each verifier additionally carries
_fault-injection controls_: deliberately mutated inputs or disabled lemmas
that the verifier is required to reject at two or more independent positions,
while staying silent on clean input. A verifier with no firing control is
treated as unverified.

Two culture rules are stated because they were each learned from a failure.
_A mutation control that disables a lemma while a synonym stays enabled tests
nothing_: controls must partition the hypothesis space, not the code. And _a
checker needs its own control_: several counting instruments here were caught
mis-counting by a positive control that measured a known answer.

== One command <sec-onecommand>

The whole campaign re-verifies with a single command, which discovers and runs
every graded verifier in sequence and exits non-zero if any fails.

```
cd problems/permanents/sub-dittert
../guard.sh python3 verify_all.py
```

Twenty-two verifiers are discovered, and the full suite is green. The run of
3 August 2026 reports `VERIFIERS: 22/22 pass` with `OVERALL: ALL VERIFIERS
PASS`, every verifier returning zero failures; the log is `verify_all.log` in
the reproduction kit. The verifiers carrying the theorems of this paper are the
following; each count is quoted from that verifier's own log.

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, left),
    stroke: tstroke,
    inset: 4.5pt,
    table.header([*verifier*], [*what it certifies*], [*result*]),
    [`graded_verify_capfrontier.py`], [Theorem F and the exact price of each
      further line], [29 checks, 10 controls fire],
    [`graded_verify_borderrows.py`], [Theorems G$'$/H$'$; the extraction bound
      @eq-lemmaU re-derived from Newton; the degeneration at $m = 0, 1$],
      [20 checks, 7 controls fire],
    [`graded_verify_thmb.py`], [the entropy witness, its exactness on the face,
      and (C1)(C2)(C3)], [32 checks, 9 controls fire],
    [`graded_verify_strict.py`], [Theorem E, the König corner, $D = 0$ iff on
      $Omega_n$, and Lemma T — steps (T0)–(T5), the crossover $n_1 = 10$ and
      the 21 exact cells below it], [42 checks, 8 controls fire],
    [`graded_verify_kn.py`], [Theorems K and K$'$, the $sigma_2$ threshold, the
      refutation of (S′)], [35 checks, 9 controls fire],
    [`graded_verify_u5core3.py`], [the census, the four core lemmas, L-CUT],
      [727 checks, 6 controls at 30 positions],
    [`graded_verify_canon.py`], [the sweeps establishing $e_0 = 12$],
      [2106 checks, 4 controls at 12 positions],
    [`graded_verify_universal.py`], [the composed Theorem U and its interface],
      [301 checks, 0 failures],
    table.hline(stroke: 0.7pt + luma(40)),
  ),
  caption: [The verifiers behind this paper's displayed constants. First
    acceptance of any certificate goes through a separate trusted verifier that
    shares no code with the producer; the modular fast layer is for
    re-verification only.]
) <verifier-table>

== What is kernel-checked, and what is not <sec-machine>

#keybox[
  The Lean 4 development elaborates with no `sorry`, no declaration depends on
  `sorryAx`, and `native_decide` is used nowhere. Every declaration cited in
  support of a stated result carries a `#print axioms` command returning a
  subset of `[propext, Classical.choice, Quot.sound]`. Build success is not an
  axiom audit, and the two are kept separate.
]

_Kernel-checked._ The line $k = 3$ in full — inequality, equality case and the
stability bound $theta_2 (n)$ — as `subDittert_k3_full` at commit `32c811e`,
whose audit block covers all 377 named declarations of its file. The line
$k = 2$ (`subDittert_k2`). The uniform layer identity at every $k lt.eq n$
(`universal_identity`). Confinement at every $k$, with its Maclaurin
hypothesis discharged (`theoremM'`, `confinement'`). Newton's inequalities and
Maclaurin for every real-rooted real polynomial (`newtonAt_all`,
`newton_esymF`, `pnorm_le_two`), neither of which is in Mathlib v4.14.0. The
Tverberg–Friedland stability form at $k = 2, 3, 4, 5$ over the whole range each
case states. The padding refutation, and the shifted-coefficient framework.

_Not kernel-checked, and not soon formalisable._ Everything in @sec-capacity.
The obstruction is external, not internal: the five internal steps of the chain
are all within reach of Mathlib — weighted AM–GM, an exact logarithm identity,
Newton, Maclaurin, and three decidable rational conditions with two monotone
ratio lemmas — but the input the cell rests on is Gurvits' capacity theorem
(E1), which needs H-stable polynomials and the full Gurvits induction, and the
equality case rests on Friedland's theorem. Those are the two large
unformalised rocks, together with Egorychev–Falikman behind them. Any Lean
statement of Theorem 2 today would have to carry (E1) as a named hypothesis,
which is the honest shape and is queued at low priority.

_Also not kernel-checked._ The $k = 4$ collar theorem and every fixed-dimension
certificate: those rest on written proofs plus exact standalone verifiers with
stored rational witnesses. The $k = n$ line is not formalised at any $n$. What
the kernel cannot check anywhere is that the Lean definitions say what the 1992
paper says; two validation theorems argue that they do —
$Phi_k (J_n\/n) = 2 - k!\/n^k$ for every $k lt.eq n$, and
$sigma_k (x y^T) = k! e_k (x) e_k (y)$, which is the check that rows and
columns are read from _different_ subsets — and that is the only place left
where a human error would survive the machine.

= Two conjectures <sec-conjectures>

== The second extremal structure <sec-secondex>

Three independent searches, run with different objectives, all located the
same second-highest critical structure of $Phi_k$ on $K_n$: an exhaustive
Karush–Kuhn–Tucker census over structured faces, the layer analysis of the
flow to $J_n\/n$, and the equality family of the diagonal boundary gap. In each
the answer is the same orbit — the $2$-regular circulants
$A_n^((t)) = (I_n + C^t)\/2$ with $gcd(t,n) = 1$, all equivalent under row and
column permutation to $A_n = (I_n + C)\/2$.

The evidence is exact. The bipartite support graph of $I + C$ is a single
$2n$-cycle, so deleting one row and one column leaves two even paths with a
unique perfect matching each; hence $per(A_n (p|q)) = 2^(1-n)$ for _every_
$(p,q)$, $per(A_n) = 2 dot.c 2^(-n)$, and $sigma_(n-1)(A_n) = n^2 2^(1-n)$.
Consequently
$ Phi_n (A_n) = 2 - 2^(1-n), quad
  (2 - n!\/n^n) - Phi_n (A_n) = 2^(1-n) - n!\/n^n > 0
  quad "for every" n gt.eq 3, $
with values $1\/36, 1\/32, 241\/10000, 41\/2592, 71569\/7529536,
709\/131072$ at $n = 3 dots 8$ and equality at $n = 2$, where
$A_2 = J_2\/2$. Of the 784 structured faces tested at $4 lt.eq n lt.eq 7$,
exactly 14 satisfy the first-order conditions, and every one of them has
$k = n$ and is in this orbit; at $k < n$ the same matrices fail with an exact
positive rational witness ($1\/12$ at $(k,n) = (2,4)$, $1\/8$ at $(3,4)$,
$11\/120$ at $(4,6)$). `[V]`

#claimbox[
  *Conjecture 1 (the second extremum).* For every $n gt.eq 3$, the largest
  value of $Phi_n$ on $K_n without {J_n\/n}$ is attained at
  $A_n = (I_n + C)\/2$, and equals $2 - 2^(1-n)$. Equivalently, the tightest
  non-$J$ margin is exactly $2^(1-n) - n!\/n^n$, which is $1\/36$ at $n = 3$.
  #leanline[Conjecture grade; the evidence above is exact and the search
  coverage is not. Its practical content: _every remaining sharpness question
  in this problem localises at that orbit_, and any future route to $k = n$
  must clear $1\/36$ at $n = 3$. At $k < n$ the orbit is not critical, which
  is consistent with @sec-capacity's chain being strict off the face.]
]

== Quantitative van der Waerden stability <sec-vdwconj>

@sec-reduction showed that one estimate would make the $k = n$ line
self-contained, and that no such estimate is in the literature at any strength.

The estimate is stated _qualitatively_, and deliberately so. Two exact facts
fix its shape before any constant is written down, and both are cheap enough
that stating a constant without them would be careless.

#claimbox[
  *Conjecture 2 (stability of the van der Waerden minimum).* For every
  $n gt.eq 3$ there is a constant $c(n) > 0$ such that for every
  $B in Omega_n$,
  $ per(B) - frac(n!, n^n) gt.eq c(n) dot.c frac(n!, n^n) dot.c sigma_2 (B)^2, $
  <eq-conj2>
  with $sigma_2$ the second largest singular value of $B$.
  #leanline[Conjecture grade; no value of $c(n)$ is claimed, and no claim is
  made that $c(n)$ can be taken absolute. Both sides vanish at $J_n\/n$ and to
  the same order: writing $B = J_n\/n + X$ with $X$ doubly centred, $sigma_2 (B)
  = norm(X)_"op"$ exactly, and $per(B) - n!\/n^n = (n!\/n^n) frac(n, 2(n-1))
  norm(X)_F^2 + O(norm(X)^3)$, so the rank-one directions cap
  $c(n) lt.eq n\/(2(n-1))$. _Nothing of this shape appears in the refereed
  literature_; the known structural substitutes — Knopp–Sinkhorn [16] on the
  zero face, Hwang [6] on the positive-support case — are not indexed by
  $sigma_2$.]
]

_Two exact checks, and one refutation that fixes the index._ At the circulant
$A_n = (I_n + C)\/2$ of @sec-secondex the margin is exactly the tight value of
Conjecture 1, so @eq-conj2 is a genuine constraint there and not a formality:
at $n = 3$, $per = 1\/4$, $sigma_2^2 = 1\/4$ and the margin is $1\/36$, forcing
$c(3) lt.eq 1\/2$; at $n = 4$, $per = 1\/8$, $sigma_2^2 = 1\/2$ and the margin
is $1\/32$, forcing $c(4) lt.eq 2\/3$. Both are consistent with the local cap
$n\/(2(n-1)) = 3\/4, 2\/3$, so the conjecture is not refuted at either cell, and
the $1\/36$ point of @sec-secondex is respected. `[V]` exactly over $QQ$. _The
index cannot be $1 - sigma_2^2$._ That variant — $per(B) - n!\/n^n gt.eq
c (n!\/n^n)(1 - sigma_2 (B)^2)$ — reads correctly at the permutation matrices
but is false at $B = J_n\/n$ for _every_ $c > 0$ and every $n$, since there the
left side is $0$ while $sigma_2 = 0$ makes the right side $c thin n!\/n^n > 0$.
It is worth recording because it is the form Theorem K$'$ appears to ask for.

_Remark (the quantitative demand, and why @eq-conj2 does not meet it)._ What
the composition of @sec-reduction actually consumes is a _pair_ of bounds,
$cap(A) gt.eq Phi(D(A), sigma_2 (B))$ and $per(B) gt.eq gamma Psi(sigma_2 (B))$
with $Phi dot.c gamma dot.c Psi gt.eq gamma - D$. The second-order law behind
Theorem K$'$ prices $Phi$: along the worst direction at $A_0 in Omega_n$ the
capacity drop is $D\/(1 - sigma_2 (A_0)^2)$ to second order, so $Phi$ degrades
like $1\/(1 - sigma_2^2)$ in exactly the regime that decides the line, and
$Psi$ would have to compensate by _growing_ as $sigma_2 arrow.r 1$. Estimate
@eq-conj2 does not do that: its right side stays bounded by
$(n!\/n^n) n\/(2(n-1))$. So @eq-conj2 is the correct _shape_ for a stability
estimate — right index, matched vanishing order at $J_n\/n$, exact caps at
$n = 3, 4$ — but it is not by itself enough to close $k = n$, and the paper
claims no more than that. The two factors are anti-correlated precisely where
each is extreme, which is the structural reason @sec-kn gives for the line
being closed to this route; a sufficient $Psi$ would have to be a genuinely
stronger statement than @eq-conj2, and we do not have one.

= What is not claimed <sec-notclaimed>

The plane claim @eq-main carries `[P]` from the $k = n$ line and should be
quoted with that tag, not one hop away from it. Theorem 2 is inequality _and_
equality on the region @eq-region, but it supplies no stability constant in the
doubly
centred directions at any cell; @sec-thresholds supplies those only for
$n gt.eq tilde(N)(k)$, and no constant is claimed optimal anywhere. The
constant $theta$ of Theorem E is proved, not proved sharp. Nothing in
@sec-capacity is kernel-checked, and the reason is external (@sec-machine). No
floating-point number enters any accepted statement. Priority is claimed
nowhere on the $k = n$ line; the $n = 4$ and $n = 5$ certificates are
independent confirmation. Finally, nothing here is refereed, including this
paper, and priority claims of any kind are perishable and should be re-checked
before submission anywhere.

A catalogue of closed strategies is maintained alongside this work and is part
of the architecture rather than an appendix curiosity: eleven named strategy
classes are refuted with exact witnesses — balancing, $k$-monotonicity, padding
transfer (machine-checked), the iterated lift, real-rootedness, the odd-layer
lemma, the $d$-vector flow, ratio monotonicity (which is Holens–Đoković,
false by Wanless's 1999 witness), first-order maximiser localisation, the
cumulant bound without its entry hypothesis, and generic-target dimension
counting. Several of these sharpen or correct statements in the published
literature, and each closes a seam that would otherwise be re-entered.

= Data availability <sec-data>

The exact rational certificates and their standalone verifiers, the graded
verifiers with their fault-injection controls and logs, the audit rebuilds
behind @dittert-table, the census sweeps behind @sec-cores, the refutation
witnesses named above, and the Lean development at the commits cited in
@sec-machine are supplied as a reproduction kit, whose README names the claim
each file backs and the procedure for re-running each check. The failed design
branches are retained there, since several closed routes are only checkable
against them.

#v(0.6em)
#line(length: 100%, stroke: 0.4pt + luma(180))
#v(0.4em)

#text(8pt)[
  _Bibliography_

  [1] G.-S. Cheon and S.-G. Hwang, _Maximization of a matrix function related
  to the Dittert conjecture_, Linear Algebra Appl. _165_ (1992), 153–165.
  #h(1em) [2] G.-S. Cheon and I. M. Wanless, _An update on Minc's survey of
  open problems involving permanents_, Linear Algebra Appl. _403_ (2005),
  314–342.
  #h(1em) [3] G.-S. Cheon and I. M. Wanless, _Some results towards the
  Dittert conjecture on permanents_, Linear Algebra Appl. _436_ (2012),
  791–801.
  #h(1em) [4] R. Sinkhorn, _A problem related to the van der Waerden
  permanent theorem_, Linear Multilinear Algebra _16_ (1984), 167–173.
  (Dittert at $n = 2$.)
  #h(1em) [5] S.-G. Hwang, _On a conjecture of E. Dittert_, Linear Algebra
  Appl. _95_ (1987), 161–169. (Dittert at $n = 3$.)
  #h(1em) [6] S.-G. Hwang, Linear Algebra Appl. _76_ (1986), 31–44. (The
  positive-support case of the classical route.)
  #h(1em) [7] H. Tverberg, _On the permanent of a bistochastic matrix_,
  Math. Scand. _12_ (1963), 25–35.
  #h(1em) [8] S. Friedland, _A proof of a generalized van der Waerden
  conjecture on permanents_, Linear Multilinear Algebra _11_ (1982), 107–120.
  (The equality case used in @sec-face is this paper's, alone.)
  #h(1em) [9] G. P. Egorychev, _The solution of van der Waerden's problem
  for permanents_, Adv. Math. _42_ (1981), 299–305.
  #h(1em) [10] D. I. Falikman, _A proof of van der Waerden's conjecture on
  the permanent of a doubly stochastic matrix_, Mat. Zametki _29_ (1981),
  931–938.
  #h(1em) [11] L. Gurvits, _Van der Waerden/Schrijver–Valiant like conjectures
  and stable (aka hyperbolic) homogeneous polynomials: one theorem for all_,
  Electron. J. Combin. _15_ (2008) \#R66; arXiv:0711.3496. (Input (E1).)
  #h(1em) [12] S. Friedland and L. Gurvits, _Lower bounds for partial matchings
  in regular bipartite graphs and applications to the monomer–dimer entropy_,
  arXiv:math/0603410 (2006), Theorem 3.1 and Corollary 3.2. (Input (E3): the
  mechanism of @sec-payment is theirs.)
  #h(1em) [13] P. Csikvári and Á. Schweitzer, arXiv:2006.16847, Lemma 2.8,
  attributed there to [15]. (Input (E2).)
  #h(1em) [14] P. Brändén, J. Leake and I. Pak, arXiv:2008.05907,
  Corollary 5.9. (Input (E2), in bivariate Lorentzian form, with sharpness.)
  #h(1em) [15] L. Gurvits, Inform. and Comput. _240_ (2015), 42–55.
  #h(1em) [16] P. Knopp and R. Sinkhorn, Linear Multilinear Algebra _11_
  (1982), 351–355. (The minimum permanent over the zero face of $Omega_n$.)
  #h(1em) [17] H. Lu, _Dittert's conjecture in dimensions six through fifteen:
  an exact computer-assisted proof_, revision 2.0, 25 July 2026. Public
  repository, no DOI, not refereed; audited and re-derived in full here.
  #h(1em) [18] Z. Pang, _Proof of Dittert's conjecture for dimensions
  $n gt.eq 17$_, arXiv:2606.01531 (2026). Preprint, not refereed.
  #h(1em) [19] B. Kafidov, _Dittert's conjecture in dimension 16 via a
  joint-deficit scaling lemma_, arXiv:2607.19439 (21 July 2026). Preprint,
  no DOI, not refereed.
  #h(1em) [20] Public repositories claiming Dittert cases, created
  21–25 July 2026, none refereed. The $n = 4$ certificate discussed in
  @sec-dittert is the first public claim at that dimension.
  #h(1em) [21] H. Finner, _A generalization of Hölder's inequality and some
  probability inequalities_, Ann. Probab. _20_ (1992), 1893–1901. (Used inside
  @sec-thresholds.)
  #h(1em) [22] D. C. P. Revere, _The Cheon–Hwang sub-Dittert conjecture at
  $k = 3$ and $k = 4$_ (2026). Companion paper; Theorems A, G and H are quoted
  here as stated there.
  #h(1em) [23] I. M. Wanless, _The Holens–Đoković conjecture on permanents is
  false_, Linear Algebra Appl. _286_ (1999), 273–285.
  #h(1em) [24] The mathlib Community, _The Lean mathematical library_,
  CPP 2020. (Lean 4.14.0, Mathlib `v4.14.0`.)
]
