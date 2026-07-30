"""
Do the stored H2 points reach (5,4) ANCHOR grade?

WHAT THE (5,4) ANCHOR ACTUALLY REQUIRES, read from
`results/verify_subdittert.py` and `../dittert/sos.py`, not from memory.  The
certificate is

    F(b) = sigma_0(b) + sum_p (1/n + b_p) sigma_p(b) + lambda(b) * (sum_q b_q)

and the verifier's six checks are: (1) sigma_k by two algorithms, (2) the bound
equals `2 - k!/n^k`, (3) the identity by FULL coefficient comparison over Q on
every monomial, (4) `G0` and all `n^2` multiplier Grams positive definite by
exact rational LDL^T, (5) mutation tests rejected, (6) `F(0) = 0`.

THERE IS NO POSITIVITY CONDITION ON THE MULTIPLIER COEFFICIENTS `lambda`, and
that is structural rather than an oversight: `lambda` multiplies `sum_q b_q`,
which is IDENTICALLY ZERO on `K_n`, so its value cannot affect the inequality.
`sos.py` says so in its own docstring -- "lambda a free polynomial" -- and
`sos.solve` puts `z` in no cone at all, only in the identity.  Measured on the
verified (5,4) anchor itself: of its 23751 lambda coefficients, 11750 are
POSITIVE and 12001 NEGATIVE.  Any sign or positivity criterion on lambda is
therefore refuted by the anchor that was supposed to satisfy it.

The "n^2 multiplier Grams" of check (4) are the `sigma_p` Grams, one per
position p -- in the symmetry-reduced form the single `sigma_11` Gram and its
`n^2 - 1` permutation conjugates.  So check (4) is exactly Gram definiteness,
which is what §6a.6's "ten rational functions of n" express in closed form for
k = 3, and what the 21 canonical blocks test for k = 4.

SO WHAT IS THE REAL GAP?  Two things, and neither is about lambda.

(a) `verify_pinretest.py` checks the 87 SYMMETRY-REDUCED identity rows.  The
    anchor checks every monomial, in standard-library code sharing nothing with
    the pipeline.  The two agree only if the orbit reduction is faithful.

(b) `verify_pinretest.py` proves definiteness of the 21 CANONICAL BLOCKS, each
    at most 16x16.  The anchor proves it of the ASSEMBLED `B x B` Grams.  Block
    definiteness implies assembled definiteness only if the blocks EXHAUST the
    isotypic components -- §6b.39 asserts that by multiplicity counting, and
    §9.5 records that the block-diagonalisation "is still not formalised as an
    EQUIVALENCE".  The verifier checks the bases have full COLUMN rank, which
    gives the converse direction, not this one.

This module measures (b) directly: it assembles `G0` and `sigma_11` at `B x B`
from a stored H2 point and factors them over Q.  A positive answer closes the
substantive half of the gap with a number comparable to the anchor's
`5.827857e-04` and `5.874542e-04`.  Nothing here is a re-solve; it evaluates
points that are already on disk.
"""

import json
import os
import sys
import time
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "dittert"))
sys.path.insert(0, HERE)
import sos                                                         # noqa: E402

WITNESS = os.path.join(HERE, "results", "witness")
K, DEG_BASIS = 4, 2


def load_point(n, name=None):
    name = name or f"n{n}_H2_201.json"
    doc = json.load(open(os.path.join(WITNESS, name)))
    return [F(*map(int, t.split("/"))) for t in doc["point"]], doc


def assemble(B, orbs, coeff):
    """The B x B invariant matrix named by orbit coefficients, exactly."""
    G = [[F(0)] * B for _ in range(B)]
    for vi, orb in enumerate(orbs):
        c = coeff[vi]
        if not c:
            continue
        for code in orb:
            G[code // B][code % B] = c
    return G


def ldl_min_pivot(G, out, tag, report_every=50):
    """
    Exact rational LDL^T on the upper triangle.

    `exactsd.ldl_pivots` maintains both triangles, which doubles the work at a
    size where the work is the whole question.  This keeps the upper triangle
    only -- the matrix is symmetric, checked before entry -- and reports
    progress, because at B = 702 and above the run time is itself a
    measurement worth recording.
    """
    B = len(G)
    a = [row[:] for row in G]
    t0 = time.time()
    worst = None
    for k in range(B):
        dk = a[k][k]
        if dk <= 0:
            out(f"    {tag}: NOT positive definite, pivot {k} = {dk}")
            return None, k
        worst = dk if worst is None else min(worst, dk)
        ak = a[k]
        # A[i][k] is read as a[k][i]: only the upper triangle is maintained
        # past this point, so reading a[i][k] would read a stale entry from
        # step k = 0.  That is the whole bug this comment exists to prevent.
        for i in range(k + 1, B):
            aki = ak[i]
            if aki == 0:
                continue
            f = aki / dk
            ai = a[i]
            for j in range(i, B):
                if ak[j]:
                    ai[j] -= f * ak[j]
        if report_every and (k + 1) % report_every == 0:
            out(f"    {tag}: pivot {k + 1}/{B} done, least so far "
                f"{float(worst):.6e}, {time.time() - t0:.0f} s elapsed")
    out(f"    {tag}: POSITIVE DEFINITE over Q, least pivot {worst} "
        f"= {float(worst):.6e}  ({time.time() - t0:.0f} s)")
    return worst, None


def symmetric(G):
    B = len(G)
    return all(G[i][j] == G[j][i] for i in range(B) for j in range(i + 1, B))


def run(n, out=print, name=None):
    out(f"\n=== assembled-Gram test, H2 point at n = {n} ===")
    w, doc = load_point(n, name)
    out(f"  point: {name or f'n{n}_H2_201.json'}, kind {doc['kind']}, "
        f"stored least BLOCK pivot {doc['least_ldl_pivot']}")
    t0 = time.time()
    d = sos.build_sdp(n, K, DEG_BASIS, verbose=False)
    B = d["B"]
    ng, ns = len(d["g_orbits"]), len(d["s_orbits"])
    nl = len(d["lam_orbit_reps"])
    out(f"  B = {B}; orbit split {ng} + {ns} + {nl} = {ng + ns + nl} "
        f"(sigma_0 | sigma_11 | lambda)   [{time.time() - t0:.0f} s to build]")
    if ng + ns + nl != len(w):
        raise SystemExit(f"point has {len(w)} entries, expected {ng + ns + nl}")

    x, y, z = w[:ng], w[ng:ng + ns], w[ng + ns:]
    nzp = sum(1 for t in z if t > 0)
    nzn = sum(1 for t in z if t < 0)
    out(f"  the {nl} lambda coefficients of THIS point: {nzp} positive, "
        f"{nzn} negative, {nl - nzp - nzn} zero -- mixed sign, exactly as the "
        f"(5,4) anchor's are, and unconstrained by construction")

    for tag, orbs, coeff in (("sigma_0  G0", d["g_orbits"], x),
                             ("sigma_11 H ", d["s_orbits"], y)):
        t1 = time.time()
        G = assemble(B, orbs, coeff)
        if not symmetric(G):
            out(f"    {tag}: NOT SYMMETRIC -- assembly is wrong")
            return None
        ent = max(len(str(abs(G[i][j].numerator)))
                  for i in range(B) for j in range(B))
        out(f"    {tag}: assembled {B}x{B}, symmetric, longest numerator "
            f"{ent} digits  ({time.time() - t1:.0f} s)")
        piv, bad = ldl_min_pivot(G, out, tag)
        if piv is None:
            out(f"  ==> n = {n}: the ASSEMBLED Gram is not positive definite "
                f"while its blocks are.  That would mean the block route is "
                f"unsound; report before acting.")
            return None
    out(f"  ==> n = {n}: both assembled Grams positive definite over Q. "
        f"Anchor check (4) holds at B x B, not only block-wise.")
    return True


def selftest(out=print, trials=8, size=14):
    """
    Check this file's LDL against `exactsd.ldl_pivots` before trusting it.

    A hand-rolled upper-triangle factorisation is exactly the kind of thing that
    silently reads a stale entry and reports a wrong pivot, so it is checked
    against the independent implementation the folder already trusts, on random
    rational matrices of both signs of answer.
    """
    import random
    from exactsd import ldl_pivots
    random.seed(20260729)
    agree = 0
    for t in range(trials):
        Bm = size
        L = [[F(random.randint(-6, 6), random.randint(1, 5))
              if j < i else (F(1) if j == i else F(0))
              for j in range(Bm)] for i in range(Bm)]
        dg = [F(random.randint(1, 9)) for _ in range(Bm)]
        if t % 2:
            dg[random.randrange(Bm)] = F(-random.randint(1, 9))
        G = [[sum(L[i][m] * dg[m] * L[j][m] for m in range(Bm))
              for j in range(Bm)] for i in range(Bm)]
        p1, b1 = ldl_pivots(G)
        p2, b2 = ldl_min_pivot(G, lambda *_: None, "selftest",
                               report_every=0)
        ok = ((p1 is None) == (p2 is None)) and \
             (p1 is None or min(p1) == p2)
        agree += ok
        if not ok:
            out(f"  SELFTEST DISAGREEMENT at trial {t}: exactsd "
                f"{None if p1 is None else min(p1)} vs mine {p2}")
    out(f"  selftest: {agree} of {trials} random matrices agree with "
        f"exactsd.ldl_pivots (definite and indefinite cases both present)")
    return agree == trials


if __name__ == "__main__":
    args = [a for a in sys.argv[1:] if a.isdigit()]
    if not selftest():
        raise SystemExit("LDL selftest failed -- refusing to report numbers")
    for nn in [int(a) for a in args] or [6]:
        run(nn)
