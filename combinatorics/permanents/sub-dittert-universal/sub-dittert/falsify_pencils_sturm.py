#!/usr/bin/env python3
"""Rigorous replacement for the grid scan on the pencils that matter most.

The grid-plus-refinement search in falsify_pencils.scan_interval could in
principle miss a positive lobe of p_k narrower than one grid cell.  Here that
loophole is closed exactly, by Sturm's theorem: count the real roots of p_k in
the admissible interval, and evaluate p_k exactly at one interior point of every
subinterval the roots cut out.  If p_k has no root in the open interval other
than the known one at t = 0, its sign is constant on each side and a single
exact evaluation per side decides it.  No grid, no resolution assumption.

Applied to the permutation pencil (which by section 2 of the write-up is ALL
permutation pencils) and to the other one-parameter families that came closest,
for every 5 <= k < n, n <= 12.
"""
import os
import sys
from fractions import Fraction as Q

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import falsify_pencils as fp  # noqa: E402


def pnorm(p):
    while len(p) > 1 and p[-1] == 0:
        p = p[:-1]
    return p


def prem(a, b):
    """Remainder of a divided by b, over Q."""
    a, b = pnorm(list(a)), pnorm(list(b))
    while len(a) >= len(b) and not (len(a) == 1 and a[0] == 0):
        c = a[-1] / b[-1]
        d = len(a) - len(b)
        for i in range(len(b)):
            a[i + d] -= c * b[i]
        a = pnorm(a)
        if len(a) == 1 and a[0] == 0:
            break
    return a


def sturm_chain(p):
    p = pnorm(list(p))
    chain = [p, pnorm(fp.pderiv(p))]
    while len(chain[-1]) > 1:
        r = prem(chain[-2], chain[-1])
        r = pnorm([-c for c in r])
        if len(r) == 1 and r[0] == 0:
            break
        chain.append(r)
    return chain


def sign_changes(chain, x):
    s, prev = 0, 0
    for q in chain:
        v = fp.pev(q, x)
        if v == 0:
            continue
        cur = 1 if v > 0 else -1
        if prev and cur != prev:
            s += 1
        prev = cur
    return s


def roots_in(chain, a, b):
    """Number of DISTINCT real roots in (a, b] (Sturm)."""
    return sign_changes(chain, a) - sign_changes(chain, b)


def split(chain, a, b, depth, out):
    """Recursively bisect [a,b] until each piece holds at most one root of the
    Sturm chain's polynomial.  Records ('free', u, v) for root-free pieces."""
    nr = roots_in(chain, a, b)
    if nr == 0:
        out.append(("free", a, b))
        return
    if depth == 0:
        out.append(("root" if nr == 1 else "multi", a, b))
        return
    m = (a + b) / 2
    split(chain, a, m, depth - 1, out)
    split(chain, m, b, depth - 1, out)


def decide(p, lo, hi, depth=40):
    """Exactly decide whether p > 0 anywhere on [lo, hi].

    p is evaluated at both endpoints and at an interior point of every
    root-free subinterval.  Since p has constant sign on each maximal root-free
    open subinterval, and every such region contains at least one of the pieces
    produced here, this decides the sign question with no grid assumption.
    Returns (positive_found, n_root_free_pieces, n_unresolved)."""
    p = pnorm(list(p))
    m = 0
    while m < len(p) - 1 and p[m] == 0:
        m += 1
    chain = sturm_chain(p[m:])          # nonzero part: drops the root at t=0
    pieces = []
    split(chain, lo, hi, depth, pieces)
    pos = fp.pev(p, lo) > 0 or fp.pev(p, hi) > 0
    free = unresolved = 0
    for kind, u, v in pieces:
        if kind == "free":
            free += 1
            if fp.pev(p, (u + v) / 2) > 0:
                pos = True
        elif kind == "multi":
            unresolved += 1
    return pos, free, unresolved


def main():
    bad = []
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    for n in range(6, nmax + 1):
        ks = list(range(5, n))
        fams = [("perm", fp.dir_from_B(*fp.perm_matrix(list(range(n)), n), n)),
                ("circ-all-but-0",
                 fp.dir_from_B(*fp.circulant(list(range(1, n)), n), n)),
                ("circ01", fp.dir_from_B(*fp.circulant([0, 1], n), n)),
                ("intercalate", fp.intercalate_dir(n)),
                ("blockJ:2+rest",
                 fp.dir_from_B(*fp.block_diag_J([2, n - 2], n), n))]
        for lab, (dn, dd) in fams:
            lo, hi = fp.dir_admissible(dn, dd, n)
            polys = fp.dir_polys(dn, dd, n, ks)
            for k in ks:
                p = polys[k]
                pos, free, unres = decide(p, lo, hi)
                if pos:
                    bad.append((n, k, lab))
                if unres:
                    bad.append((n, k, lab + " UNRESOLVED"))
                print(f"n={n:2d} k={k:2d} {lab:15s} t in [{lo}, {hi}]  "
                      f"root-free pieces={free} unresolved={unres}  "
                      f"p_k > 0 anywhere: {pos}", flush=True)
    print("\nfamilies with a positive value or unresolved piece:", len(bad))
    print("VERDICT:", "COUNTEREXAMPLE" if bad else
          "p_k <= 0 on the whole admissible interval, every family, "
          "no grid assumption")


if __name__ == "__main__":
    main()
