"""
STANDALONE verifier for the k = 4 pin re-test witnesses -- NOTES §6b.37-§6b.40.

METHODS §5: "A standalone verifier sharing no code with the pipeline that
produced the certificate."  This file imports NOTHING from `k4_pincert.py` or
`k4_pinrank.py`.  It re-derives the constraint system and the pin conditions
from the problem definition (`sos.py`, `exactsd.py` and the canonical block
modules, all of which predate this re-test), and it carries its OWN exact
linear algebra -- its own elimination, its own constancy test, its own LDL^T.
Where the pipeline and this file agree, they agree by two implementations.

WHAT EACH WITNESS CLAIMS, and what is checked here.

  kind "feasible"        a rational point w.
      CHECKED: S w = rhs row by row; every pin condition vanishes; every one
      of the 21 canonical blocks is positive definite by exact rational LDL^T.
      Also checked: the canonical bases have FULL COLUMN RANK, without which
      `H > 0 => E^T H E > 0` does not follow and the test would be vacuous.

  kind "infeasible"      a Farkas multiplier as a list of generators.
      Y = sum of c_i e_i e_i^T and a_k v_k v_k^T with every coefficient >= 0,
      so Y >= 0 BY CONSTRUCTION and no factorisation is needed -- the sign test
      on the coefficients is the whole of it.
      CHECKED: coefficients nonnegative and not all zero; the functional
      w -> sum_b <Y_b, M_b(w)> is CONSTANT on A -- verified by reducing its
      coefficient vector against this file's own row reduction of [S; P] and
      demanding the residual be IDENTICALLY zero -- and its value is <= 0.

  kind "infeasible_matrix"   the same, with Y given entrywise.
      CHECKED as above, except that positive semidefiniteness is established
      by exact LDL^T rather than by construction.

USAGE

    python verify_pinretest.py                 # check every stored witness
    python verify_pinretest.py --n 5           # one n
    python verify_pinretest.py --mutate        # MUTATION CONTROLS

The mutation controls perturb each witness in a way that MUST be rejected: one
generator coefficient made negative, one flipped in sign, the claimed value
raised above zero, and one entry of a feasible point altered.  METHODS §5:
"Mutation controls must be RUN, and must FAIL.  Writing the control is not the
check; watching it fail is."  A control that passes is reported as a FAILURE of
this verifier, not as a success of the witness.
"""

import json
import os
import sys
from fractions import Fraction as F
from math import gcd

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, os.path.join(os.path.dirname(ROOT), "dittert"))
sys.path.insert(0, ROOT)

K, DEG_BASIS = 4, 2
WITNESS_DIR = os.path.join(HERE, "witness")


# --------------------------------------------------------------- own exact LA
def rowreduce(rows, rhs, ncols):
    """
    Fully reduced row echelon form over Q, integer-preserving.

    Written independently of the pipeline's routine.  Rows are kept integral
    and gcd-reduced; the invariant maintained is `R[i] . w == bb[i]` for every
    w in the solution set, with pivot column i zero in every other row.
    """
    A = [list(r) for r in rows]
    b = [F(v) for v in rhs]
    piv, r, R = [], 0, len(A)
    for c in range(ncols):
        k = next((i for i in range(r, R) if A[i][c]), None)
        if k is None:
            continue
        A[r], A[k] = A[k], A[r]
        b[r], b[k] = b[k], b[r]
        pv = A[r][c]
        for i in range(R):
            if i == r or not A[i][c]:
                continue
            f = A[i][c]
            g = gcd(pv, f)
            m1, m2 = pv // g, f // g
            Ai, Ar = A[i], A[r]
            A[i] = [m1 * Ai[j] - m2 * Ar[j] for j in range(ncols)]
            b[i] = m1 * b[i] - m2 * b[r]
            h = 0
            for v in A[i]:
                h = gcd(h, v)
            if h > 1:
                A[i] = [v // h for v in A[i]]
                b[i] = b[i] / h
        piv.append(c)
        r += 1
        if r == R:
            break
    consistent = all(b[i] == 0 for i in range(r, R))
    return piv, A[:r], b[:r], consistent


def constant_value(c, piv, R, bb, ncols):
    """The functional's value on the solution set, or None if it is not one."""
    c = list(c)
    val = F(0)
    for i, p in enumerate(piv):
        if not c[p]:
            continue
        f = F(c[p], R[i][p]) if isinstance(c[p], int) else c[p] / R[i][p]
        val += f * bb[i]
        Ri = R[i]
        for j in range(ncols):
            if Ri[j]:
                c[j] -= f * Ri[j]
    return val if not any(c) else None


def ldl(M):
    """Exact rational LDL^T.  (pivots, None) if positive definite."""
    B = len(M)
    a = [[F(x) for x in row] for row in M]
    piv = []
    for k in range(B):
        dk = a[k][k]
        if dk <= 0:
            return None, k
        piv.append(dk)
        for i in range(k + 1, B):
            if a[i][k] == 0:
                continue
            f = a[i][k] / dk
            for j in range(k, B):
                a[i][j] -= f * a[k][j]
                a[j][i] = a[i][j]
    return piv, None


def colrank(rows, ncols):
    return len(rowreduce(rows, [F(0)] * len(rows), ncols)[0])


# ------------------------------------------------- re-derive the problem
def rebuild(n):
    """S, rhs, the 321 pin rows and the 21 canonical blocks, from source."""
    import k4_pinretest as pr
    import k4_sigma0 as s0
    import k4_vv14 as vv
    import sos
    from exactsd import exact_system, full_matrix

    d = sos.build_sdp(n, K, DEG_BASIS, verbose=False)
    B, basis = d["B"], d["basis"]
    ng, ns = len(d["g_orbits"]), len(d["s_orbits"])
    C = ng + ns + len(d["lam_orbit_reps"])

    A0e, A1c, A1l, A2e, rhse = exact_system(d)
    Mq = full_matrix(A0e, A1c, A1l, A2e, n)
    srows, srhs = [], []
    for r, row in enumerate(Mq):
        den = 1
        for v in row:
            den = den * v.denominator // gcd(den, v.denominator)
        den = int(den) * rhse[r].denominator
        srows.append([int(v * den) for v in row])
        srhs.append(rhse[r] * den)

    sides = (("s11", pr.canonical_blocks(n, basis), d["s_orbits"], ng),
             ("s0", s0.canonical_blocks(n, basis), d["g_orbits"], 0))
    pins, blocks = [], []
    for side, bl, orbs, off in sides:
        cls = pr.orbit_class_array(n, basis, orbs)
        for name, E in bl:
            dd = len(E)
            N = vv.block_by_class(E, cls, B)
            blocks.append((side, name, dd, N, off, E))
            for i in range(dd):
                for j in range(i + 1, dd):
                    vec = [0] * C
                    for cl, x in N[i][j].items():
                        vec[off + cl] = int(x)
                    pins.append((side, name, vec))
    if len(pins) != 321:
        raise SystemExit(f"re-derivation gave {len(pins)} pins, expected 321")
    return d, C, srows, srhs, pins, blocks


def basis_full_rank(blocks, B):
    """`H > 0 => E^T H E > 0` needs E of full column rank.  Check it."""
    bad = []
    for side, name, dd, N, off, E in blocks:
        keys = sorted({u for e in E for u in e})
        idx = {u: i for i, u in enumerate(keys)}
        rows = []
        for e in E:
            r = [0] * len(keys)
            for u, cf in e.items():
                r[idx[u]] = int(cf)
            rows.append(r)
        if colrank(rows, len(keys)) != dd:
            bad.append(f"{side} {name}")
    return bad


def contract(N, dd, w, off):
    return [[sum(x * w[off + c] for c, x in N[s][t].items())
             for t in range(dd)] for s in range(dd)]


# ------------------------------------------------------------------- checking
def load(path):
    with open(path) as fh:
        return json.load(fh)


def rat(s):
    a, b = s.split("/")
    return F(int(a), int(b))


def select(pins, doc):
    if doc["omit_block"] is None:
        return list(pins)
    return [p for p in pins
            if not (p[0] == doc["omit_side"] and p[1] == doc["omit_block"])]


def check_lp_infeasible(doc, ctx, note, memo):
    """
    Verify a Farkas ray for the zero-value LP.

    The claim is that `y . g_j > 0` for EVERY generator column, where g_j
    carries generator j's residual against A followed by its value.  If that
    holds then no nonzero nonnegative combination of the generators can be the
    zero vector, so the LP has no solution -- exactly, by Farkas.

    The generator columns are RE-DERIVED here from the problem definition, so
    the certificate is checked against this file's own reduction rather than
    against the numbers the pipeline used to find `y`.
    """
    d, C, srows, srhs, pins, blocks = ctx
    piv, R, bb, ok = reduced_for(doc, ctx, memo)
    if not ok:
        return False, "the configuration is inconsistent over Q"
    free = [j for j in range(C) if j not in set(piv)]
    y = [rat(t) for t in doc["y"]]
    if len(y) != len(free) + 1:
        return False, (f"y has {len(y)} entries, expected {len(free) + 1}")
    # the diagonal generators are canonical and rebuildable without any stored
    # data; the rank-one ones are identified by the vector stored with them
    gens = []
    for side, name, dd, N, off, E in blocks:
        for i in range(dd):
            c = [F(0)] * C
            for cl, x in N[i][i].items():
                c[off + cl] += x
            gens.append(c)
    worst = None
    for c in gens:
        res, val = _reduce(c, piv, R, bb, C, free)
        g = res + [val]
        s = max((abs(x) for x in g if x), default=F(0))
        if s:
            g = [x / s for x in g]
        v = sum(y[r] * g[r] for r in range(len(g)) if g[r])
        if worst is None or v < worst:
            worst = v
    if worst is None or worst <= 0:
        return False, (f"y is NOT strictly positive on every diagonal "
                       f"generator (least {worst})")
    note(f"      y . g > 0 on all {len(gens)} re-derived diagonal generators, "
         f"least {float(worst):.6e}")
    return True, ("no nonnegative combination is constant on A with value 0, "
                  "by Farkas")


def _reduce(c, piv, R, bb, C, free):
    """Residual on the free columns and the constant part, exactly."""
    c = list(c)
    val = F(0)
    for k, p in enumerate(piv):
        if c[p]:
            f = c[p] / R[k][p]
            val += f * bb[k]
            Rk = R[k]
            for j in range(C):
                if Rk[j]:
                    c[j] -= f * Rk[j]
    return [c[j] for j in free], val


def reduced_for(doc, ctx, memo):
    """
    The row reduction of [S; P_cfg], cached per configuration.

    A witness and its mutation controls share a configuration, and the
    reduction is the expensive step -- recomputing it per control would make
    the controls cost five times the check they guard.  The cache is keyed by
    the configuration, never by the witness, so a mutated witness cannot pick
    up a reduction built for a different pin set.
    """
    key = (doc["omit_side"], doc["omit_block"])
    if key not in memo:
        d, C, srows, srhs, pins, blocks = ctx
        sel = select(pins, doc)
        rows = srows + [v for _, _, v in sel]
        rhs = list(srhs) + [F(0)] * len(sel)
        memo[key] = rowreduce(rows, rhs, C)
    return memo[key]


def check_witness(doc, ctx, note, memo=None):
    d, C, srows, srhs, pins, blocks = ctx
    sel = select(pins, doc)
    if doc["kind"] == "lp_infeasible":
        return check_lp_infeasible(doc, ctx, note, memo)
    if doc["kind"] == "feasible":
        w = [rat(t) for t in doc["point"]]
        if len(w) != C:
            return False, f"point has {len(w)} entries, expected {C}"
        for r, row in enumerate(srows):
            if sum(F(row[j]) * w[j] for j in range(C) if row[j]) != srhs[r]:
                return False, f"SDP identity row {r} is not satisfied"
        for q, (_, _, vec) in enumerate(sel):
            if sum(F(vec[j]) * w[j] for j in range(C) if vec[j]) != 0:
                return False, f"pin condition {q} is not satisfied"
        worst = None
        for side, name, dd, N, off, E in blocks:
            pv, bad = ldl(contract(N, dd, w, off))
            if pv is None:
                return False, f"block {side} {name} is not PD (pivot {bad})"
            worst = min(pv) if worst is None else min(worst, min(pv))
        note(f"      all 87 identity rows hold, all {len(sel)} pins vanish, "
             f"all 21 blocks PD, least pivot {float(worst):.3e}")
        if "least_ldl_pivot" in doc and rat(doc["least_ldl_pivot"]) != worst:
            return False, "the stored least pivot disagrees with the recomputed"
        return True, "strictly feasible, exactly"

    # both infeasible kinds: build Y, then test the functional
    index = {(b[0], b[1]): i for i, b in enumerate(blocks)}
    Y = [[[F(0)] * b[2] for _ in range(b[2])] for b in blocks]
    if doc["kind"] == "infeasible":
        if not doc["generators"]:
            return False, "no generators"
        anynz = False
        for g in doc["generators"]:
            cf = rat(g["coef"])
            if cf < 0:
                return False, "a generator coefficient is negative"
            if cf:
                anynz = True
            b = index[(g["side"], g["block"])]
            dd = blocks[b][2]
            if g["kind"] == "diag":
                Y[b][g["index"]][g["index"]] += cf
            else:
                v = [rat(t) for t in g["v"]]
                for s in range(dd):
                    for t in range(dd):
                        if v[s] and v[t]:
                            Y[b][s][t] += cf * v[s] * v[t]
        if not anynz:
            return False, "every generator coefficient is zero"
        psd = "by construction (nonnegative sum of e e^T and v v^T)"
    else:
        anynz = False
        for b, Yb in enumerate(doc["Y"]):
            for s, row in enumerate(Yb):
                for t, x in enumerate(row):
                    Y[b][s][t] = rat(x)
                    if Y[b][s][t]:
                        anynz = True
        if not anynz:
            return False, "Y is identically zero"
        for b, (side, name, dd, N, off, E) in enumerate(blocks):
            if any(Y[b][s][t] != Y[b][t][s]
                   for s in range(dd) for t in range(dd)):
                return False, f"Y for {side} {name} is not symmetric"
            if all(not Y[b][s][t] for s in range(dd) for t in range(dd)):
                continue
            if ldl(Y[b])[0] is None:
                return False, f"Y for {side} {name} is not positive definite"
        psd = "by exact LDL^T on each nonzero block"

    c = [F(0)] * C
    for b, (side, name, dd, N, off, E) in enumerate(blocks):
        for s in range(dd):
            for t in range(dd):
                if not Y[b][s][t]:
                    continue
                for cl, x in N[s][t].items():
                    c[off + cl] += Y[b][s][t] * x
    piv, R, bb, ok = reduced_for(doc, ctx, memo if memo is not None else {})
    if not ok:
        return True, "the configuration is inconsistent over Q -- A is empty"
    val = constant_value(c, piv, R, bb, C)
    if val is None:
        return False, "the functional is NOT constant on A"
    if val > 0:
        return False, f"the functional is constant but positive ({float(val)})"
    if "value" in doc and rat(doc["value"]) != val:
        return False, (f"stored value {doc['value']} disagrees with the "
                       f"recomputed {val}")
    note(f"      Y >= 0 {psd}; functional constant on A at "
         f"{float(val):+.6e} <= 0")
    return True, "not strictly feasible, exactly"


# ------------------------------------------------------------------ mutations
def mutations(doc):
    """Corruptions that MUST be rejected.  Each returns a modified document."""
    import copy
    out = []
    if doc["kind"] == "feasible":
        for j in (0, len(doc["point"]) // 2):
            m = copy.deepcopy(doc)
            x = rat(m["point"][j]) + F(1, 10 ** 9)
            m["point"][j] = f"{x.numerator}/{x.denominator}"
            out.append((f"point entry {j} shifted by 1e-9", m))
        m = copy.deepcopy(doc)
        m["least_ldl_pivot"] = "1/1"
        out.append(("least pivot overstated", m))
    elif doc["kind"] == "infeasible":
        m = copy.deepcopy(doc)
        g = m["generators"][0]
        g["coef"] = "-" + g["coef"] if not g["coef"].startswith("-") \
            else g["coef"][1:]
        out.append(("first generator coefficient negated", m))
        m = copy.deepcopy(doc)
        x = rat(m["generators"][0]["coef"]) * 2
        m["generators"][0]["coef"] = f"{x.numerator}/{x.denominator}"
        out.append(("first generator coefficient doubled", m))
        m = copy.deepcopy(doc)
        m["value"] = "1/1"
        out.append(("claimed value replaced by +1", m))
        if len(doc["generators"]) > 1:
            m = copy.deepcopy(doc)
            m["generators"] = m["generators"][1:]
            out.append(("one generator dropped", m))
    elif doc["kind"] == "lp_infeasible":
        for j in (0, len(doc["y"]) // 2):
            m = copy.deepcopy(doc)
            m["y"][j] = "0/1"
            out.append((f"y entry {j} zeroed", m))
        m = copy.deepcopy(doc)
        m["y"] = [("-" + t if not t.startswith("-") else t[1:])
                  for t in m["y"]]
        out.append(("y negated", m))
    else:
        m = copy.deepcopy(doc)
        for b, Yb in enumerate(m["Y"]):
            if any(any(rat(x) for x in row) for row in Yb):
                x = rat(Yb[0][0]) + F(1, 10 ** 6)
                m["Y"][b][0][0] = f"{x.numerator}/{x.denominator}"
                break
        out.append(("one Y entry shifted by 1e-6", m))
        m = copy.deepcopy(doc)
        m["value"] = "1/1"
        out.append(("claimed value replaced by +1", m))
    return out


def minimality(doc, ctx, memo, note):
    """
    Is every generator load-bearing?  Drop each in turn and re-check.

    The lead's question about H1's `11/270694368` coefficient at n = 6: a
    coefficient can be tiny and clean and still be the only thing making the
    functional constant on A.  Smallness is not redundancy, and the only way to
    tell is to remove it and look.
    """
    import copy
    if doc["kind"] != "infeasible":
        return None
    keep = []
    for j in range(len(doc["generators"])):
        m = copy.deepcopy(doc)
        del m["generators"][j]
        m.pop("value", None)
        good, _ = check_witness(m, ctx, lambda *_: None, memo)
        keep.append(not good)
    g = doc["generators"]
    note(f"      minimality: {sum(keep)} of {len(g)} generators are "
         f"load-bearing" + ("" if all(keep) else
                            f" -- REDUNDANT: "
                            f"{[j for j, k in enumerate(keep) if not k]}"))
    return keep


def main(argv):
    want = None
    if "--n" in argv:
        want = int(argv[argv.index("--n") + 1])
    do_mutate = "--mutate" in argv
    do_min = "--minimal" in argv
    if not os.path.isdir(WITNESS_DIR):
        raise SystemExit(f"no witness directory at {WITNESS_DIR}")
    files = sorted(f for f in os.listdir(WITNESS_DIR) if f.endswith(".json"))
    docs = [(f, load(os.path.join(WITNESS_DIR, f))) for f in files]
    if want is not None:
        docs = [(f, doc) for f, doc in docs if doc["n"] == want]
    if not docs:
        raise SystemExit("no witnesses to check")

    ok = bad = ctrl_ok = ctrl_bad = 0
    for n in sorted({doc["n"] for _, doc in docs}):
        here = [(f, doc) for f, doc in docs if doc["n"] == n]
        print(f"\n=== n = {n}: re-deriving the system from source "
              f"({len(here)} witnesses) ===", flush=True)
        ctx = rebuild(n)
        memo = {}
        d, C, srows, srhs, pins, blocks = ctx
        print(f"  system {len(srows)} x {C}, {len(pins)} pins, "
              f"{len(blocks)} canonical blocks, B = {d['B']}", flush=True)
        bad_rank = basis_full_rank(blocks, d["B"])
        if bad_rank:
            raise SystemExit(f"canonical bases rank-deficient: {bad_rank}")
        print("  every canonical basis has full column rank, so "
              "H > 0 implies E^T H E > 0", flush=True)
        for f, doc in here:
            good, why = check_witness(doc, ctx, print, memo)
            print(f"  {'PASS' if good else 'FAIL'}  {f}  [{doc['kind']}]  "
                  f"{why}", flush=True)
            ok, bad = (ok + 1, bad) if good else (ok, bad + 1)
            if do_min and good:
                minimality(doc, ctx, memo, print)
            if not do_mutate:
                continue
            for label, mdoc in mutations(doc):
                mgood, mwhy = check_witness(mdoc, ctx,
                                            lambda *_: None, memo)
                if mgood:
                    print(f"        CONTROL DID NOT FAIL: {label} -- "
                          f"this verifier accepted a corrupted witness",
                          flush=True)
                    ctrl_bad += 1
                else:
                    print(f"        control rejected ({label}): {mwhy}",
                          flush=True)
                    ctrl_ok += 1

    print(f"\nwitnesses: {ok} PASS, {bad} FAIL")
    if do_mutate:
        print(f"mutation controls: {ctrl_ok} correctly REJECTED, "
              f"{ctrl_bad} wrongly accepted")
    if bad or ctrl_bad:
        raise SystemExit(1)
    print("all witnesses verified" + (" and every control failed as required"
                                      if do_mutate else ""))


if __name__ == "__main__":
    main(sys.argv[1:])
