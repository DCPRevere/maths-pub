#!/usr/bin/env python3
"""Driver: scan permutation pencils and named structured matrices for a
counterexample to Phi_k(A) <= 2 - k!/n^k on K_n, for 5 <= k < n, n <= 12.

Every pencil is A(t) = J_n/n + t d with sum(d) = 0, so sum A(t) = n for all t
and K_n membership reduces to A(t) >= 0.  p_k(t) = Phi_k(A(t)) - M(n,k) is
computed EXACTLY as a polynomial of degree <= k.  A counterexample is exactly
a point where p_k(t) > 0 with t admissible.

Output: one JSON record per (family, n, k) on stdout-log, plus a summary.
"""
import itertools
import json
import math
import os
import sys
import time
from fractions import Fraction as Q

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import falsify_pencils as fp  # noqa: E402


def B(Bnum, Bden, n):
    return fp.dir_from_B(Bnum, Bden, n)


def families(n):
    """[(label, dnum, dden)] : directions d = B - J/n (or raw directions)."""
    out = []

    # ---- (1) permutation pencils -----------------------------------------
    ident = list(range(n))
    cyc = [(i + 1) % n for i in range(n)]
    inv = list(range(n))
    for i in range(0, n - 1, 2):
        inv[i], inv[i + 1] = inv[i + 1], inv[i]
    fix2 = list(range(n))                       # (n-2)-cycle, 2 fixed points
    tail = list(range(2, n))
    for a, i in enumerate(tail):
        fix2[i] = tail[(a + 1) % len(tail)]
    perms = [("perm:identity", ident), ("perm:n-cycle", cyc),
             ("perm:2-cycle-product", inv), ("perm:2fix+(n-2)cycle", fix2)]
    for lab, p in perms:
        out.append((lab,) + B(*fp.perm_matrix(p, n), n))

    # ---- (2) regular circulants (m-regular doubly stochastic) -------------
    sets = [(0, 1), (0, 2), (0, 1, 2), (0, 1, 3), (0, 2, 4), (0, 1, 2, 3)]
    if n >= 8:
        sets += [(0, 1, 4), (0, 3, 5), (0, 1, 2, 4)]
    for S in sets:
        if max(S) < n and len(S) < n:
            out.append((f"circ-reg:{'.'.join(map(str, S))}",)
                       + B(*fp.circulant(list(S), n), n))
    # complement of the identity (the (n-1)-regular circulant) and near-J
    out.append(("circ-reg:all-but-0",)
               + B(*fp.circulant(list(range(1, n)), n), n))

    # ---- (3) two- and three-symbol weighted circulants --------------------
    for w in [{0: Q(3, 4), 1: Q(1, 4)}, {0: Q(1, 4), 1: Q(3, 4)},
              {0: Q(2, 3), 1: Q(1, 3)}, {0: Q(1, 2), 2: Q(1, 2)},
              {0: Q(1, 2), 1: Q(1, 4), 2: Q(1, 4)},
              {0: Q(1, 2), 1: Q(1, 3), 2: Q(1, 6)},
              {0: Q(2, 3), 1: Q(1, 6), 2: Q(1, 6)}]:
        if max(w) < n:
            lab = "circ-wt:" + ".".join(f"{s}={v}" for s, v in w.items())
            out.append((lab,) + B(*fp.weighted_circulant(w, n), n))

    # ---- (4) block-diagonal J ---------------------------------------------
    for b in range(2, n):
        if n % b == 0:
            out.append((f"blockJ:{b}^{n // b}",)
                       + B(*fp.block_diag_J([b] * (n // b), n), n))
    if n >= 5:
        parts = [2, n - 2]
        out.append((f"blockJ:{parts[0]}+{parts[1]}",)
                   + B(*fp.block_diag_J(parts, n), n))

    # ---- (5) non-doubly-stochastic named shapes ---------------------------
    out.append(("triangular", ) + B(*fp.triangular(n), n))
    out.append(("arrow", ) + B(*fp.arrow(n), n))
    out.append(("rank1:ramp x ones",)
               + B(*fp.rank_one(list(range(1, n + 1)), [1] * n, n), n))
    out.append(("rank1:ramp x ramp",)
               + B(*fp.rank_one(list(range(1, n + 1)),
                                list(range(1, n + 1)), n), n))
    out.append(("rank1:spike x ones",)
               + B(*fp.rank_one([1] * (n - 1) + [n], [1] * n, n), n))

    # ---- (6) isotypic probe directions ------------------------------------
    w = [0] * n
    w[0], w[1] = 1, -1
    out.append(("dir:row-effect(+1,-1)", ) + fp.row_effect_dir(n, w))
    out.append(("dir:col-effect(+1,-1)", ) + fp.col_effect_dir(n, w))
    w2 = [n - 1] + [-1] * (n - 1)
    out.append(("dir:row-effect(spike)", ) + fp.row_effect_dir(n, w2))
    out.append(("dir:intercalate", ) + fp.intercalate_dir(n))
    # row-effect combined with a column-effect (rank-one-ish interaction)
    dm = [[(1 if i == 0 else -Q(1, n - 1)) * (1 if j == 0 else -Q(1, n - 1))
           for j in range(n)] for i in range(n)]
    L = (n - 1) ** 2
    out.append(("dir:outer(spike,spike)",
                [[int(x * L) for x in row] for row in dm], L))

    # ---- (7) named designs / Latin squares --------------------------------
    if n == 7:
        F7 = fp.fano_incidence()
        out.append(("design:Fano-7-3-1", ) + B(*fp.from_01(F7, 7), 7))
        out.append(("design:Fano-complement", )
                   + B(*fp.from_01(fp.complement01(F7, 7), 7), 7))
    if n == 11:
        Bp = fp.biplane_11()
        out.append(("design:biplane-11-5-2", ) + B(*fp.from_01(Bp, 11), 11))
        out.append(("design:biplane-complement", )
                   + B(*fp.from_01(fp.complement01(Bp, 11), 11), 11))
    tables = []
    if n == 6:
        tables.append(("S3", fp.s3_table()))
    if n == 8:
        tables.append(("Z2^3", fp.product_group_table([2, 2, 2])))
        tables.append(("Z4xZ2", fp.product_group_table([4, 2])))
        tables.append(("Q8", fp.q8_table()))
    if n == 9:
        tables.append(("Z3^2", fp.product_group_table([3, 3])))
    if n == 12:
        tables.append(("Z6xZ2", fp.product_group_table([6, 2])))
        tables.append(("Z2^2xZ3", fp.product_group_table([2, 2, 3])))
    for gname, tab in tables:
        for m in (2, 3):
            elts = list(range(m))
            out.append((f"latin-group:{gname}/{m}sym", )
                       + B(*fp.group_regular(elts, tab, n), n))
    if n <= 9:
        Lsq = fp.prolongation_latin(n)
        for m in (2, 3):
            out.append((f"latin-nongroup:{m}sym", )
                       + B(*fp.latin_symbol_union(Lsq, set(range(m)), n), n))

    # ---- (8) sums of unrelated permutations (non-circulant d.s.) ----------
    import random
    rng = random.Random(1000 + n)
    for r in range(2):
        acc = [[0] * n for _ in range(n)]
        ps = []
        for _ in range(3):
            p = list(range(n))
            rng.shuffle(p)
            ps.append(p)
            for i, j in enumerate(p):
                acc[i][j] += 1
        out.append((f"ds:3-perm-sum#{r}", ) + B(acc, 3, n))

    # ---- (9) generic controls --------------------------------------------
    for r in range(2):
        Mrand = [[rng.randint(1, 9) for _ in range(n)] for _ in range(n)]
        out.append((f"control:random#{r}", ) + B(*fp.from_01(Mrand, n), n))

    return out


def main():
    nmin = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    nmax = int(sys.argv[2]) if len(sys.argv) > 2 else 12
    recs = []
    hits = []
    t0 = time.time()
    for n in range(nmin, nmax + 1):
        ks = list(range(5, n))
        if not ks:
            continue
        fam = families(n)
        print(f"### n={n}  k in {ks}  families={len(fam)}", flush=True)
        for lab, dnum, dden in fam:
            if sum(sum(r) for r in dnum) != 0:
                print(f"  SKIP {lab}: direction sum != 0", flush=True)
                continue
            lo, hi = fp.dir_admissible(dnum, dden, n)
            nrm = fp.dir_norm2(dnum, dden, n)
            try:
                polys = fp.dir_polys(dnum, dden, n, ks)
            except AssertionError as e:
                print(f"  SKIP {lab}: {e}", flush=True)
                continue
            for k in ks:
                p = polys[k]
                assert p[0] == 0, "p_k(0) must vanish: J/n attains the bound"
                order, c = fp.low_order(p)
                M = fp.bound(n, k)
                vmax, targ = fp.scan_interval(p, lo, hi)
                # value at the named endpoint t=1 when admissible
                v1 = fp.pev(p, Q(1)) if lo <= 1 <= hi else None
                rec = dict(n=n, k=k, family=lab,
                           t_lo=str(lo), t_hi=str(hi),
                           lead_order=order, lead_coeff=str(c),
                           lead_rayleigh=str(c / nrm) if nrm else "0",
                           max_p=str(vmax), argmax=str(targ),
                           ratio_max=str(1 + vmax / M),
                           ratio_t1=(str(1 + v1 / M) if v1 is not None
                                     else None))
                recs.append(rec)
                if vmax > 0:
                    hits.append(rec)
                    print("  *** HIT ***", json.dumps(rec), flush=True)
        print(f"    [n={n} done, {time.time() - t0:.1f}s]", flush=True)

    outp = os.path.join(HERE, "results", "falsify_pencils_records.json")
    with open(outp, "w") as f:
        json.dump(recs, f)
    print(f"\nrecords={len(recs)}  hits={len(hits)}")

    # top by ratio at the named endpoint t=1 (the structured matrix itself)
    ep = [r for r in recs if r["ratio_t1"] is not None]
    ep.sort(key=lambda r: Q(r["ratio_t1"]), reverse=True)
    print("\nTOP-10 named structured POINTS (t=1) by Phi_k/M:")
    for r in ep[:10]:
        print(f"  {float(Q(r['ratio_t1'])):.9f}  n={r['n']} k={r['k']} "
              f"{r['family']}   exact={r['ratio_t1']}")

    # top by how close the pencil comes to escaping (largest p on the interval,
    # i.e. least negative), excluding the trivial t -> 0 limit
    recs.sort(key=lambda r: Q(r["max_p"]), reverse=True)
    print("\nTOP-10 pencil maxima of p_k(t) over admissible t (0 = the bound):")
    for r in recs[:10]:
        print(f"  p_max={r['max_p']}  at t={r['argmax']}  n={r['n']} "
              f"k={r['k']} {r['family']}")

    # top by leading Rayleigh quotient (closest to a degenerate direction)
    recs.sort(key=lambda r: Q(r["lead_rayleigh"]), reverse=True)
    print("\nTOP-10 directions by leading coefficient / ||d||^2 "
          "(closest to degeneracy):")
    for r in recs[:10]:
        print(f"  ord={r['lead_order']} c/||d||^2={r['lead_rayleigh']}  n={r['n']}"
              f" k={r['k']} {r['family']}")

    print("\nVERDICT:", "COUNTEREXAMPLE CANDIDATES" if hits else
          "no point with Phi_k > 2 - k!/n^k found")
    return 0


if __name__ == "__main__":
    sys.exit(main())
