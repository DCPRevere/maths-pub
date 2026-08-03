"""
BAND 1 (deg_basis = 1, k <= TOPDEG = 3): the positivity half, closed.

PARAMETRIC.md solves the IDENTITY half of the certificate machine for a whole
band at once (Lemma 1: the cone does not see k; Theorem 2: the rhs is closed
form in (k, n); Theorem 4: the collapse).  What it leaves open is positivity --
"the free parameters as explicit functions of (n, k)" (PARAMETRIC.md section 10
item 1, ATLAS.md section 6 item 4).  This module closes that for the smallest
band, where the free parameters number 8 rather than 354.

WHAT IS HERE

  * the band system, built ONCE and k-free: 12 rows, 19 unknowns, rank 11 over
    Q(n), so an 8-dimensional affine family (NOTES section 6a.5);
  * every rhs of the band carried through the SAME elimination -- k = 1, 2, 3
    and the six Theorem-2 vectors c^[d], e^[d], d = 1, 2, 3 -- so Theorem 4's
    collapse is checkable symbolically in n rather than at integer n;
  * ONE parameter law, law B1 below, linear in k, valid at every k of the band;
  * the resulting 19 certificate variables as exact rational functions of
    (n, k), and the ten UPP positivity quantities they produce.

LAW B1 (the answer).  Write the four essential free coordinates in the
beta = f * n^3 scaling of NOTES section 6a.8c, and put e = k - 2 (so e = 0 at
k = 2 and e = 1 at k = 3 -- the band index of NOTES-ALLK).  Then

    beta9  = (k - 1)/2
    beta6  = 2 beta9 + x/n ,        x = (3 - k)/2 + 8 e (n + 1)/n^2
    beta12 = 2 beta9 - e + y/n ,    y = -5 e
    beta11 = 2 beta12 + 2 e + z/n^2 ,   z the unique solution of theta_2 = D

and the four gauge coordinates f15..f18 are supplied by the closed-form gauge of
NOTES section 6a.8c (theta_0 = 1/n, A = diag(1/n^3, T^T A T)), which adds no
positivity requirement.  z is SOLVED, never fitted: theta_2 and D are affine in
z with opposite-sign coefficients of size n^2 and the window between them has
width O(n^-2), so a fit could not hold it.

Only three numbers are chosen in the whole band: the coefficients 1/2, 8 and -5
of the k-linear laws for beta9, x and y.  Everything else is forced.

Companion verifier: graded_verify_band1.py.  Record: POSITIVITY.md, NOTES
section 36.
"""

import os
import sys
from fractions import Fraction as F
from math import factorial

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "dittert"))
sys.path.insert(0, HERE)

import blocks as bl                                               # noqa: E402
import general_k3 as g                                            # noqa: E402
import recession as rc                                            # noqa: E402
import sturm                                                      # noqa: E402
from general_k3 import RF                                         # noqa: E402

ZERO = RF([])
ONE = RF([F(1)])
TWO = RF([F(2)])
N = RF([F(0), F(1)])

TOPDEG = 3
BAND_K = (2, 3)                       # the k this band certifies (k = 1 is the
                                      # degenerate row, see POSITIVITY.md)
NFREE = 8
ESS = [6, 9, 11, 12]                  # beta order: beta6, beta9, beta11, beta12
GAUGE = [15, 16, 17, 18]
QNAMES = ["G0.theta0", "G0.theta1", "G0.theta2", "H.A minor1", "H.A minor2",
          "H.A minor3", "H.B", "H.C minor1", "H.C minor2", "H.D"]


# ------------------------------------------------------------- the band system
def falling_poly(d):
    p = [F(1)]
    for i in range(d):
        p = g.pmul(p, [F(-i), F(1)])
    return p


class Band:
    """The k-free band-1 system over Q(n), with every rhs of the band."""

    def __init__(self):
        self.sym = g.build_symbolic_system(TOPDEG)
        rows = self.sym["rows"]
        svars = self.sym["svars"]
        npoly = [F(0), F(1)]
        M = []
        for r in range(len(rows)):
            row = [RF(p) for p in self.sym["A0"][r]]
            row += [RF(self.sym["A1c"][r][j], npoly) + RF(self.sym["A1l"][r][j])
                    for j in range(len(svars))]
            row += [RF(p) for p in self.sym["A2"][r]]
            M.append(row)
        self.M = M
        self.labels, rhss = [], []
        for k in (1, 2, 3):
            self.labels.append(("k", k))
            rhss.append([g._rhs_rf(key, k) for key in rows])
        cvec, evec = self._ce_vectors()
        for tag, vecs in (("c", cvec), ("e", evec)):
            for d in (1, 2, 3):
                self.labels.append((tag, d))
                rhss.append(vecs[d])
        self.A, self.B, self.piv, self.free, self.rank = self._reduce(rhss)
        self.idx = {lab: i for i, lab in enumerate(self.labels)}
        assert self.free == [6, 9, 11, 12, 15, 16, 17, 18], self.free
        self.ess_i = [self.free.index(c) for c in ESS]
        self.lin = rc.lineality_free()
        self.svar_idx = bl.svar_index()

    def _ce_vectors(self):
        rows = self.sym["rows"]
        c = {d: [ZERO] * len(rows) for d in (1, 2, 3)}
        e = {d: [ZERO] * len(rows) for d in (1, 2, 3)}
        for i, key in enumerate(rows):
            d = len(key)
            if d == 0:
                continue
            S = RF(g.orbit_size_poly(key, False))
            nd = RF(falling_poly(d))
            dr = len(set(r for r, _ in key)) == d
            dc = len(set(cc for _, cc in key)) == d
            c[d][i] = RF([F(-(int(dr) + int(dc)))]) * S / nd
            if dr and dc:
                c_ = RF([F(0)] * d + [F(1)])
                e[d][i] = S * c_ / (nd * nd)
        return c, e

    def _reduce(self, rhss):
        M = self.M
        nR, ncol = len(M), len(M[0])
        A = [row[:] for row in M]
        Bv = [list(v) for v in rhss]
        piv, r = [], 0
        for c in range(ncol):
            p = next((i for i in range(r, nR) if A[i][c]), None)
            if p is None:
                continue
            A[r], A[p] = A[p], A[r]
            for v in Bv:
                v[r], v[p] = v[p], v[r]
            pv = A[r][c]
            A[r] = [t / pv for t in A[r]]
            for v in Bv:
                v[r] = v[r] / pv
            for i in range(nR):
                if i != r and A[i][c]:
                    f = A[i][c]
                    A[i] = [A[i][j] - f * A[r][j] for j in range(ncol)]
                    for v in Bv:
                        v[i] = v[i] - f * v[r]
            piv.append(c)
            r += 1
            if r == nR:
                break
        free = [c for c in range(ncol) if c not in piv]
        return A, Bv, piv, free, r

    # -------------------------------------------------------------- solutions
    def consistent(self, lab):
        b = self.B[self.idx[lab]]
        return all(not b[i] for i in range(self.rank, len(b)))

    def particular(self, lab):
        v = [ZERO] * 19
        b = self.B[self.idx[lab]]
        for i, c in enumerate(self.piv):
            v[c] = b[i]
        return v

    def vals19(self, lab, fs):
        vals = [None] * 19
        for t, c in enumerate(self.free):
            vals[c] = fs[t]
        b = self.B[self.idx[lab]]
        for i, c in enumerate(self.piv):
            v = b[i]
            for t, fc in enumerate(self.free):
                a = self.A[i][fc]
                if a:
                    v = v - a * fs[t]
            vals[c] = v
        return vals

    def collapse(self, k):
        """Theorem 4's X(n,k) with all free parameters zero, over Q(n)."""
        gk = RF([F(factorial(k))]) / RF([F(0)] * k + [F(1)])
        acc = [ZERO] * 19
        for d in (1, 2, 3):
            kd = F(1)
            for i in range(d):
                kd *= (k - i)
            if kd == 0:
                continue
            kdr = RF([kd])
            Yd, Zd = self.particular(("c", d)), self.particular(("e", d))
            for j in range(19):
                acc[j] = acc[j] + kdr * (Yd[j] + gk * Zd[j])
        return acc

    # ------------------------------------------------------- the ten quantities
    def entries(self, lab, fs):
        vals = self.vals19(lab, fs)
        a, b, c = vals[0], vals[1], vals[2]
        m = N - ONE
        A, B, C, D = bl.blocks_rational_generic(N, vals[3:14], self.svar_idx,
                                                one=ONE)
        theta = [a + b * TWO * m + c * m * m,
                 a + b * (N - TWO) - c * m,
                 a - b * TWO + c]
        return vals, theta, A, B, C, D

    def quantities(self, lab, fs):
        _, theta, A, B, C, D = self.entries(lab, fs)
        return [(QNAMES[0], theta[0]), (QNAMES[1], theta[1]),
                (QNAMES[2], theta[2]),
                (QNAMES[3], A[0][0]),
                (QNAMES[4], A[0][0] * A[1][1] - A[0][1] * A[0][1]),
                (QNAMES[5], sturm._det3(A)),
                (QNAMES[6], B),
                (QNAMES[7], C[0][0]),
                (QNAMES[8], C[0][0] * C[1][1] - C[0][1] * C[0][1]),
                (QNAMES[9], D)]

    def balanced(self, lab, fs):
        """The ten design entries in the Theta(1) congruence of exact_design."""
        vals, theta, A, B, C, D = self.entries(lab, fs)
        m = N - ONE
        T = [[ZERO - TWO * m, ZERO - m * m], [ONE, ZERO], [ZERO, ONE]]
        TA = [[sum((T[p][i] * A[p][q] * T[q][j] for p in range(3)
                    for q in range(3)), ZERO) for j in range(2)]
              for i in range(2)]
        e = [theta[1], theta[2], B, D, C[0][0], C[0][1], C[1][1],
             TA[0][0], TA[0][1], TA[1][1]]
        n2 = N * N
        n3, n4, n5, n6 = n2 * N, n2 * n2, n2 * n2 * N, n2 * n2 * n2
        c11, c12, c22 = e[4], e[5], e[6]
        t11, t12, t22 = e[7], e[8], e[9]
        return [e[0] * N, e[1] * n5, e[2] * N, e[3] * n6,
                c11 * n3,
                c12 * n3 - c11 * n4,
                c11 * n5 - c12 * TWO * n4 + c22 * n3,
                t11 * N,
                t12 * N - t11 * n2,
                t11 * n3 - t12 * TWO * n2 + t22 * N]

    # -------------------------------------------------------------- law B1
    def beta_law(self, k, coeffs=(F(1, 2), F(8), F(-5))):
        """Law B1: (beta6, beta9, beta11-without-z, beta12) and the z column."""
        h, cx, cy = coeffs
        e = F(k - 2)
        b9 = RF([h * F(k - 1)])
        x = RF([F(3 - k, 2)]) + RF([cx * e]) * (N + ONE) / (N * N)
        y = RF([cy * e])
        b6 = TWO * b9 + x / N
        b12 = TWO * b9 - RF([e]) + y / N
        b11_0 = TWO * b12 + RF([F(2) * e])
        return b6, b9, b11_0, b12

    def fs_from_beta(self, beta):
        fs = [ZERO] * NFREE
        n3 = N * N * N
        for j in range(4):
            fs[self.ess_i[j]] = beta[j] / n3
        return fs

    def solve_z(self, lab, k, coeffs=(F(1, 2), F(8), F(-5))):
        """The unique z with theta_2 = D, exactly over Q(n)."""
        b6, b9, b11_0, b12 = self.beta_law(k, coeffs)
        n2 = N * N

        def gap(zrf):
            beta = [b6, b9, b11_0 + zrf / n2, b12]
            bal = self.balanced(lab, self.fs_from_beta(beta))
            return bal[1] - bal[3]                      # theta2 - D, balanced

        g0 = gap(ZERO)
        g1 = gap(ONE)
        slope = g1 - g0
        if not slope:
            raise RuntimeError("theta_2 - D does not involve z")
        return ZERO - g0 / slope

    def apply_gauge(self, lab, fs, gamma, tau):
        vals = self.vals19(lab, fs)
        a, b, c = vals[0], vals[1], vals[2]
        m = N - ONE
        theta0 = a + b * TWO * m + c * m * m
        A, _, _, _ = bl.blocks_rational_generic(N, vals[3:14], self.svar_idx,
                                                one=ONE)
        p1 = A[0][1] - A[0][0] * TWO * m
        p2 = A[0][2] - A[0][0] * m * m
        w1 = (gamma - A[0][0]) / TWO
        w2 = (ZERO - p1) + w1 * TWO * m
        w3 = (ZERO - p2) + w1 * m * m
        vK, vR, vI = w1, w2 / (TWO * m), w3 / (m * m)
        mu = (tau - theta0) / (N * N)
        out = list(fs)
        for coef, gen in zip((mu, vK, vR, vI), self.lin):
            for t in range(NFREE):
                if gen[t]:
                    out[t] = out[t] + coef * gen[t]
        return out

    def build(self, k, coeffs=(F(1, 2), F(8), F(-5))):
        """The eight free coordinates of law B1 at this k, over Q(n)."""
        lab = ("k", k)
        z = self.solve_z(lab, k, coeffs)
        b6, b9, b11_0, b12 = self.beta_law(k, coeffs)
        beta = [b6, b9, b11_0 + z / (N * N), b12]
        fs = self.fs_from_beta(beta)
        fs = self.apply_gauge(lab, fs, ONE / (N * N * N), ONE / N)
        return fs, beta, z


# ------------------------------------------------------------- positivity tools
def shift_to_m(poly, shift):
    out, acc = [], [F(1)]
    for i, co in enumerate(poly):
        if i:
            acc = g.pmul(acc, [F(shift), F(1)])
        out = g.padd(out, g.pscale(acc, co))
    return g.ptrim(out)


def sign_ge(poly, n0):
    p = shift_to_m(poly, n0)
    if not p:
        return 0
    if all(c >= 0 for c in p) and p[0] > 0:
        return 1
    if all(c <= 0 for c in p) and p[0] < 0:
        return -1
    ok, _ = sturm.positive_on_nonneg(p)
    if ok:
        return 1
    ok, _ = sturm.positive_on_nonneg(g.pscale(p, F(-1)))
    return -1 if ok else 0


def sturm_verdict(qs, n0, verbose=True):
    """Decide positivity of every quantity on n >= n0.  Complete, not merely
    sufficient (Sturm on the squarefree part)."""
    allok = True
    for name, rf in qs:
        sd = sign_ge(rf.den, n0)
        if sd == 0:
            allok = False
            if verbose:
                print(f"  {name:<12s} DENOMINATOR not sign-definite on "
                      f"n >= {n0}")
            continue
        ok, detail = sturm.positive_on_nonneg(
            shift_to_m(g.pscale(rf.num, F(sd)), n0))
        allok = allok and ok
        if verbose:
            print(f"  {name:<12s} {'POSITIVE' if ok else '*** NOT POSITIVE'}"
                  f"  on n >= {n0}   [{detail}]")
    return allok


def snc_threshold(rf, lo=1, hi=80):
    """PARAMETRIC section 7.2's shifted-coefficient certificate: the least n1
    with every coefficient of the shifted numerator >= 0 and the constant > 0."""
    for n1 in range(lo, hi + 1):
        sd = sign_ge(rf.den, n1)
        if sd == 0:
            continue
        p = shift_to_m(g.pscale(rf.num, F(sd)), n1)
        if p and p[0] > 0 and all(c >= 0 for c in p):
            return n1
    return None


N0 = {2: 3, 3: 4}                      # the certified range of each k


# ------------------------------------------------------------------- export
def export_cell(n, k, path=None):
    """Write one cell of law B1 as SELF-CONTAINED JSON for the trusted
    verifier results/verify_subdittert.py (first-acceptance path).  The format
    is export.py's: dense G0, dense G[p] for every p, lambda as a monomial
    dictionary, so the verifier needs nothing but rational arithmetic."""
    import json
    from exactsd import assemble
    from sos import build_sdp, transporters
    from symmetry import monomials as _mons

    bd = Band()
    fs, _, _ = bd.build(k)
    vals = [v.at(F(n)) for v in bd.vals19(("k", k), fs)]
    d = build_sdp(n, k, 1, verbose=False)
    B, Nv = d["B"], n * n
    basis = d["basis"]
    gvars, svars, lvars = bd.sym["gvars"], bd.sym["svars"], bd.sym["lvars"]

    def pair_key(orb, fix):
        u, v = divmod(orb[0], B)
        return g.canon(g.cells_of(basis[u] + basis[v], n), fix)

    xq = [vals[gvars.index(pair_key(o, False))] for o in d["g_orbits"]]
    yq = [vals[len(gvars) + svars.index(pair_key(o, True))]
          for o in d["s_orbits"]]
    lam_mons = _mons(Nv, d["TOPDEG"] - 1)
    zq = [vals[len(gvars) + len(svars)
               + lvars.index(g.canon(g.cells_of(lam_mons[m[0]], n)))]
          for m in d["lam_orbit_reps"]]

    G0 = assemble(B, d["g_orbits"], xq)
    H = assemble(B, d["s_orbits"], yq)
    trans = transporters(n, (0, 0))
    bindex = {m: u for u, m in enumerate(basis)}
    Gp = []
    for p in range(Nv):
        gp = trans[p]
        perm = [bindex[tuple(sorted(gp[t] for t in m))] for m in basis]
        M = [[F(0)] * B for _ in range(B)]
        for u in range(B):
            for v in range(B):
                if H[u][v]:
                    M[perm[u]][perm[v]] += H[u][v]
        Gp.append(M)
    lam = {}
    for vi, members in enumerate(d["lam_orbit_reps"]):
        co = zq[vi]
        if not co:
            continue
        for t in members:
            key = ",".join(str(x) for x in lam_mons[t])
            lam[key] = str(F(lam[key]) + co) if key in lam else str(co)

    def smat(M):
        return [[str(x) for x in row] for row in M]

    out = dict(problem="Cheon-Hwang sub-Dittert",
               statement="E_k(r) + E_k(c) - P_k(A) <= 2 - k!/n^k on K_n, "
                         "equality only at J_n/n",
               source="band-1 law B1 (band1_certificate.py)",
               n=n, k=k, N=Nv, bound_M=str(d["M"]),
               basis=[list(m) for m in basis],
               G0=smat(G0), Gp=[smat(M) for M in Gp], lam=lam,
               identity="F(b) = sum_uv G0[u][v] m_u m_v + sum_p (1/n + b_p) "
                        "sum_uv Gp[p][u][v] m_u m_v + lam(b) * sum_q b_q")
    path = path or os.path.join(HERE, "results",
                                f"band1_n{n}k{k}_certificate.json")
    with open(path, "w") as fh:
        json.dump(out, fh, indent=1)
    print(f"wrote {path}  ({B}x{B} G0, {Nv} multiplier Grams, "
          f"{len(lam)} lambda monomials)")
    return path


def main():
    bd = Band()
    print("=== BAND 1: the system ===")
    print(f"  rows {len(bd.sym['rows'])}, unknowns 19, rank over Q(n) "
          f"{bd.rank}, free {bd.free}")
    for lab in bd.labels:
        assert bd.consistent(lab), lab
    print(f"  all {len(bd.labels)} band right-hand sides consistent over Q(n)")

    print("\n=== Theorem 4 collapse, symbolically in n ===")
    for k in (1, 2, 3):
        direct, coll = bd.particular(("k", k)), bd.collapse(k)
        bad = sum(1 for j in range(19) if direct[j] != coll[j])
        print(f"  k = {k}: X(n,k) = sum_d (k)_d (Y_d + (k!/n^k) Z_d): "
              f"{bad} mismatches over 19 coordinates of Q(n)")

    for k in BAND_K:
        print(f"\n=== LAW B1 at k = {k} ===")
        fs, beta, z = bd.build(k)
        for nm, v in zip(("beta6", "beta9", "beta11", "beta12"), beta):
            print(f"  {nm:<7s} = {v}")
        print(f"  z       = {z}")
        print("  the eight free coordinates:")
        for c, v in zip(bd.free, fs):
            print(f"    f{c:<3d} = {v}")
        qs = bd.quantities(("k", k), fs)
        print(f"  Sturm on n >= {N0[k]}:")
        ok = sturm_verdict(qs, N0[k])
        print(f"  ALL TEN POSITIVE on n >= {N0[k]}: {ok}")
        print("  shifted-coefficient (SNC) thresholds, and the Sturm answer:")
        worst = 0
        for name, rf in qs:
            n1 = snc_threshold(rf)
            worst = max(worst, n1 or 0)
            print(f"    {name:<12s} SNC n1 = {n1}")
        print(f"  WORST SNC threshold over the ten: n >= {worst}")
        print("  the 19 certificate variables:")
        for i, v in enumerate(bd.vals19(("k", k), fs)):
            nm = (f"sigma0[{i}]" if i < 3 else
                  (f"sigma11[{i-3}]" if i < 14 else f"lambda[{i-14}]"))
            print(f"    {nm:<12s} = {v}")


if __name__ == "__main__":
    main()
