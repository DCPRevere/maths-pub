"""
Closed form in n for the last six blocks -- the two-index-weight contractions.

§6b.26 needed one identity, `sum_{v != v'} w_v w_v' = -q(w)`, from sum-zeroness.
A two-index weight `W` with `W_aa = 0`, `W_ba = eps W_ab` and the TRACE
CONDITION `sum_b W_ab = 0` needs a small table instead.  Writing
`S = <W,W> = sum_{a,b} W_ab^2` and summing over assignments of DISTINCT values
to the groups, with s's weight `W_{alpha beta}` and t's `W_{gamma delta}`:

    mu = {i->i, k->k}   alpha,beta = gamma,delta         S            R = 2
    mu = {i->k, k->i}   crossed                          eps S        R = 2
    mu = {i->i}         alpha = gamma                    -S           R = 3
    mu = {k->k}         beta  = delta                    -S           R = 3
    mu = {i->k}         alpha = delta                    -eps S       R = 3
    mu = {k->i}         beta  = gamma                    -eps S       R = 3
    mu = {}             disjoint                         (1+eps) S    R = 4

DERIVATION of the R = 3 row: fixing v1, v2 and summing the free index v3 over
everything outside {v1, v2} gives `-W_{v1 v1} - W_{v1 v2} = -W_{v1 v2}` by the
trace condition and the zero diagonal, and the result contracts against
`W_{v1 v2}` to give `-S`.  For R = 4 the same inclusion-exclusion leaves only
the both-indices-inside term, `(1 + eps) W_{v1 v2}`.  **So for an ANTISYMMETRIC
weight every disjoint merge pattern contributes nothing** -- `1 + eps = 0` --
which is the same cancellation that killed four of the six candidate templates
for `Ind(1|(m-2,1,1))` in §6b.31.

`S` divides out of every term exactly as `q(w)` did, and the unweighted or
vector-weighted side contributes its §6b.26 factor unchanged.

THE TABLE IS SELF-TESTED, not asserted: `check_contractions` evaluates each of
the seven sums directly over all distinct assignments at several m and compares
against the coefficient times `S`.
"""

import itertools
import os
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "dittert"))
sys.path.insert(0, HERE)
import k4_ind16 as i16                                            # noqa: E402
import k4_ind16_closed as c16                                     # noqa: E402
import k4_system as k4                                            # noqa: E402
import k4_tail as tail                                            # noqa: E402
import k4_vv14 as vv                                              # noqa: E402
from general_k3 import falling, padd, peval, pmul, pstr, pzero    # noqa: E402
from k4_blocks import _shift_by                                   # noqa: E402


def contraction_coeff(mu, eps):
    """The table above, keyed by the partial injection mu on (i, k)."""
    if len(mu) == 2:
        return 1 if mu.get("i") == "i" else eps
    if len(mu) == 1:
        (src, dst), = mu.items()
        return -1 if src == dst else -eps
    return 1 + eps


def check_contractions(ms=(5, 6, 7), verbose=True):
    """Evaluate all seven sums directly and compare with the table."""
    ok = True
    for m in ms:
        for anti in (False, True):
            eps = -1 if anti else 1
            W, dim = tail.two_index_weight(m, anti, 20260729 + m)
            if dim == 0:
                continue
            S = sum(W[(a, b)] ** 2 for a in range(1, m + 1)
                    for b in range(1, m + 1))
            for mu in c16.partial_injections(["i", "k"], ["i", "k"]):
                grs, grt, R = c16._groups(["i", "k"], ["i", "k"], mu)
                direct = 0
                for vals in itertools.permutations(range(1, m + 1), R):
                    a, b = vals[grs["i"]], vals[grs["k"]]
                    c, d = vals[grt["i"]], vals[grt["k"]]
                    direct += W[(a, b)] * W[(c, d)]
                want = contraction_coeff(mu, eps) * S
                if direct != want:
                    ok = False
                    print(f"    m={m} anti={anti} mu={mu}: direct {direct} "
                          f"vs table {want}   *** MISMATCH ***")
            if verbose:
                print(f"    m = {m}, {'antisymmetric' if anti else 'symmetric'}"
                      f" (dim {dim}, S = {S}): all 7 contractions match")
    return ok


def _side_factor(kind, mu, groups_s, groups_t, D, eps):
    """
    Polynomial factor for one side (rows or columns) of a merge pattern.

    triv       [n-1]_D                      -- every group freely assigned
    vec        6b.26:  +[n-2]_{D-1} merged,  -[n-3]_{D-2} not
    sym/asym   the contraction table -- an INTEGER, no falling factorial,
               because the weight consumes every group on that side
    """
    if kind == "triv":
        return _shift_by(falling(D), 0)
    if kind == "vec":
        key = "i" if "i" in groups_s else None
        same = groups_s[key] == groups_t[key]
        if same:
            return _shift_by(falling(D - 1), 1)
        return [-x for x in _shift_by(falling(D - 2), 2)]
    return [F(contraction_coeff(mu, eps))]


def block_closed(name, rowtype, coltype, kept, sidx):
    """Ntilde[s][t] = {class index: polynomial in n} over the kept templates."""
    ns = len(kept)
    eps_r = -1 if rowtype == "asym" else 1
    eps_c = -1 if coltype == "asym" else 1
    N = [[dict() for _ in range(ns)] for _ in range(ns)]
    for s in range(ns):
        cs = kept[s]
        Sr = [x for x in ("i", "k") if any(r == x for r, _ in cs)]
        Sc = [x for x in ("a", "b") if any(c == x for _, c in cs)]
        for t in range(ns):
            ct = kept[t]
            Tr = [x for x in ("i", "k") if any(r == x for r, _ in ct)]
            Tc = [x for x in ("a", "b") if any(c == x for _, c in ct)]
            acc = {}
            for mu in c16.partial_injections(Sr, Tr):
                grs, grt, R = c16._groups(Sr, Tr, mu)
                frow = _side_factor(rowtype, mu, grs, grt, R, eps_r)
                if not frow:
                    continue
                for nu in c16.partial_injections(Sc, Tc):
                    gcs, gct, C = c16._groups(Sc, Tc, nu)
                    # the column table is keyed by (i,k); rename a,b -> i,k
                    nu_ik = {("i" if k2 == "a" else "k"):
                             ("i" if v == "a" else "k") for k2, v in nu.items()}
                    gcs_ik = {("i" if k2 == "a" else "k"): v
                              for k2, v in gcs.items()}
                    gct_ik = {("i" if k2 == "a" else "k"): v
                              for k2, v in gct.items()}
                    fcol = _side_factor(coltype, nu_ik, gcs_ik, gct_ik, C,
                                        eps_c)
                    if not fcol:
                        continue
                    u = tuple(sorted((0 if r == "0" else grs[r] + 1,
                                      0 if cc == "0" else gcs[cc] + 1)
                                     for r, cc in cs))
                    v = tuple(sorted((0 if r == "0" else grt[r] + 1,
                                      0 if cc == "0" else gct[cc] + 1)
                                     for r, cc in ct))
                    key = sidx[k4.canon_pair(u, v, True)]
                    acc[key] = padd(acc.get(key, pzero()), pmul(frow, fcol))
            N[s][t] = {cl: p for cl, p in acc.items() if p}
    return N


def verify(ns=(5, 6)):
    print("contraction table, checked directly against the defining sums:")
    tok = check_contractions()
    print(f"  table verified: {tok}\n")
    if not tok:
        return False

    svars = i16.svars_cached()
    sidx = {k: i for i, k in enumerate(svars)}
    allok = tok
    for name, rt, ct, mult, dimf in tail.BLOCKS:
        cand = tail.candidates(rt, ct)
        # the kept set is n-independent (measured identical at n = 5 and 6),
        # but take it at the SMALLER n and use it at both, so a drift would show
        n0 = ns[0]
        m0 = n0 - 1
        wr = (None if rt == "triv" else
              (i16.sum_zero(n0, 20260729) if rt == "vec"
               else tail.two_index_weight(m0, rt == "asym", 20260729)[0]))
        wc = (None if ct == "triv" else
              (i16.sum_zero(n0, 20260729 + 57) if ct == "vec"
               else tail.two_index_weight(m0, ct == "asym", 20260729 + 57)[0]))
        vecs = [tail.realise(c, n0, rt, ct, wr, wc) for c in cand]
        kept_i, _, _ = tail.independent_subset(vecs)
        kept = [cand[t] for t in kept_i]
        Nc = block_closed(name, rt, ct, kept, sidx)
        degs = [len(p) - 1 for a in range(len(kept)) for b in range(len(kept))
                for p in Nc[a][b].values()] or [0]
        used = set()
        for a in range(len(kept)):
            for b in range(len(kept)):
                used |= set(Nc[a][b])
        print(f"  {name}: {len(kept)} shapes, {len(used)} classes, "
              f"degrees {min(degs)}..{max(degs)}, symmetric "
              f"{all(Nc[a][b] == Nc[b][a] for a in range(len(kept)) for b in range(len(kept)))}")

        for n in ns:
            m = n - 1
            wr = (None if rt == "triv" else
                  (i16.sum_zero(n, 20260729) if rt == "vec"
                   else tail.two_index_weight(m, rt == "asym", 20260729)[0]))
            wc = (None if ct == "triv" else
                  (i16.sum_zero(n, 20260729 + 57) if ct == "vec"
                   else tail.two_index_weight(m, ct == "asym", 20260729 + 57)[0]))
            q = tail.wnorm(rt, wr, m) * tail.wnorm(ct, wc, m)
            basis = k4.basis_of(n)
            B = len(basis)
            index = {mo: t for t, mo in enumerate(basis)}
            E = [{index[mo]: c for mo, c in
                  tail.realise(cc, n, rt, ct, wr, wc).items()} for cc in kept]
            cls, _ = i16.direct_class_array(n, basis, sidx)
            Nn = vv.block_by_class(E, cls, B)
            mism = 0
            for a in range(len(kept)):
                for b in range(len(kept)):
                    conc = {cl: F(x, q) for cl, x in Nn[a][b].items() if x}
                    clsd = {cl: peval(p, n) for cl, p in Nc[a][b].items()}
                    clsd = {cl: x for cl, x in clsd.items() if x}
                    if conc != clsd:
                        mism += 1
            print(f"      n={n}: closed form vs concrete -> {mism} mismatched "
                  f"of {len(kept) ** 2}")
            allok = allok and mism == 0
    return allok


if __name__ == "__main__":
    ns = [int(a) for a in sys.argv[1:]] or [5, 6]
    print("Closed form in n for the last six blocks -- NOTES §6b.31\n")
    ok = verify(tuple(ns))
    print(f"\nall six closed forms verified: {ok}")
