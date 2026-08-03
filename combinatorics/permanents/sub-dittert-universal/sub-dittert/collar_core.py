"""
CORE of the uniform-in-k collar assembly.

Everything here is exact over QQ.  No floating point enters any decision.

The object.  On the collar we split  B = A - J/n = L + z  with
L_ij = x_i + y_j  (sum x = sum y = 0)  and z doubly centred.  Theorem C makes
the deficit a t_d-weighted sum of sigma_d(B), and the sub-permanent expansion

    sigma_d(z + L) = sum_{j=0}^{d} sum_{|S|=|T|=j} per(z[S|T]) sigma_{d-j}(L^(S,T))

splits each layer into  j = 0 (pure line),  j = d (pure centred)  and the
CROSS parts  1 <= j <= d-1.  This module computes the cross parts three ways:

  cross_brute   the definition, term by term (ground truth)
  cross_general the closed reduction of Theorem X1 below
  theta         the deleted-index moments the reduction is written in

THEOREM X1 (the general cross term).  With m = d - j and

    c(m,p,N) = p! (m-p)! C(N-p, m-p) C(N-m+p, p),
    Theta_j[r,r'] = sum_{|S|=|T|=j} per(z[S|T]) h_r(x_S) h_{r'}(y_T),

one has, identically in x, y, z and for every n, d, j,

    X_{d,j} = sum_{r,r'} kappa^{(d,j)}_{r,r'} Theta_j[r,r'],
    kappa^{(d,j)}_{r,r'} = (-1)^{r+r'} sum_{u+v = m-r-r'} c(m, r+u, n-j)
                                        e_u(x) e_v(y).

k enters ONLY through t_d.  The invariants Theta_j[r,r'] depend on (j,r,r')
alone -- not on d and not on k -- which is what makes the assembly uniform.

THEOREM X2 (survivors).  kappa^{(d,j)}_{r,r'} Theta_j[r,r'] is not identically
zero exactly when

    (S-a)  r + r' <= m                      [degree]
    (S-b)  r + r' != m - 1                  [e_1(x) = e_1(y) = 0]
    (S-c)  j >= 2, or (j = 1 and r,r' >= 1) [the line sums of z vanish]

and the number of survivors is

    |S(j,m)| = C(m,2) - max(0, m-2)         for j = 1,
    |S(j,m)| = C(m+2,2) - m                 for j >= 2,

so layer d carries  N(d) = (d^3 - 7d + 12)/6  cross invariants for d >= 3,
and N(1) = N(2) = 0 -- the d = 2 cross part vanishes identically, which the
paper records at k = 4 as an observation and which is here a corollary.

Usage:  imported by collar_verify.py and graded_verify_collar.py.
"""

from fractions import Fraction as Fr
from itertools import combinations, permutations, product
from math import comb, factorial, isqrt

# --------------------------------------------------------------- primitives


def per(M):
    m = len(M)
    if m == 0:
        return Fr(1)
    tot = Fr(0)
    for p in permutations(range(m)):
        pr = Fr(1)
        for i in range(m):
            pr *= M[i][p[i]]
        tot += pr
    return tot


def sigma_of(M, d):
    """Sum of all d x d sub-permanents of M.  Brute force; ground truth."""
    n = len(M)
    if d == 0:
        return Fr(1)
    if d > n:
        return Fr(0)
    tot = Fr(0)
    for R in combinations(range(n), d):
        for C in combinations(range(n), d):
            tot += per([[M[i][j] for j in C] for i in R])
    return tot


def elem(v, d):
    """e_d of a list."""
    if d < 0:
        return Fr(0)
    e = [Fr(0)] * (d + 1)
    e[0] = Fr(1)
    for t in v:
        for i in range(min(d, len(v)), 0, -1):
            e[i] += e[i - 1] * t
    return e[d]


def homog(v, r):
    """h_r of a list (complete homogeneous)."""
    if r < 0:
        return Fr(0)
    h = [Fr(0)] * (r + 1)
    h[0] = Fr(1)
    for t in v:
        for i in range(1, r + 1):
            h[i] += h[i - 1] * t
    return h[r]


def lmat(x, y, n):
    return [[x[i] + y[j] for j in range(n)] for i in range(n)]


def delete(M, S, T, n):
    rs = [i for i in range(n) if i not in S]
    cs = [j for j in range(n) if j not in T]
    return [[M[i][j] for j in cs] for i in rs]


# ------------------------------------- the line block: sigma_m of x_i + y_j


def c_coef(m, p, N):
    """c(m,p,N) = p!(m-p)! C(N-p,m-p) C(N-m+p,p).

    This is the coefficient of e_p(x_I) e_{m-p}(y_J) in sigma_m of the N x N
    line matrix (x_i + y_j)_{i in I, j in J}.  At N = n it is the (S4) closed
    form of pincer_line.py; the content here is that the SAME formula holds on
    every deleted index pair, with N = n - j.
    """
    if p < 0 or p > m or N - p < m - p or N - m + p < p:
        return 0
    return (factorial(p) * factorial(m - p)
            * comb(N - p, m - p) * comb(N - m + p, p))


def sigma_line(xI, yJ, m):
    """sigma_m of the line matrix on index sets I, J with |I| = |J| = N."""
    N = len(xI)
    assert len(yJ) == N
    tot = Fr(0)
    for p in range(m + 1):
        c = c_coef(m, p, N)
        if c:
            tot += c * elem(xI, p) * elem(yJ, m - p)
    return tot


# ---------------------------------------------- the deleted-index moments


def theta(x, y, z, j, r, rp, n):
    """Theta_j[r,r'] = sum_{|S|=|T|=j} per(z[S|T]) h_r(x_S) h_{r'}(y_T)."""
    tot = Fr(0)
    for S in combinations(range(n), j):
        hx = homog([x[i] for i in S], r)
        if hx == 0:
            continue
        for T in combinations(range(n), j):
            pz = per([[z[i][t] for t in T] for i in S])
            if pz:
                tot += pz * hx * homog([y[t] for t in T], rp)
    return tot


# ------------------------------------------------- the cross terms, 3 ways


def cross_brute(x, y, z, d, j, n):
    """sum_{|S|=|T|=j} per(z[S|T]) sigma_{d-j}(L^(S,T)).  The definition."""
    L = lmat(x, y, n)
    tot = Fr(0)
    for S in combinations(range(n), j):
        for T in combinations(range(n), j):
            pz = per([[z[i][t] for t in T] for i in S])
            if pz:
                tot += pz * sigma_of(delete(L, set(S), set(T), n), d - j)
    return tot


def survivors(j, m):
    """The (r,r') admitted by Theorem X2, in a fixed order."""
    out = []
    for tot in range(m + 1):
        if tot == m - 1:
            continue
        for r in range(tot + 1):
            rp = tot - r
            if j == 1 and (r == 0 or rp == 0):
                continue
            out.append((r, rp))
    return out


def survivor_count(j, m):
    """The closed form of Theorem X2, computed from the formula not the list."""
    if m < 0:
        return 0
    if j == 1:
        return comb(m, 2) - max(0, m - 2)
    return comb(m + 2, 2) - (m if m >= 1 else 0)


def layer_count(d):
    """N(d) = total number of cross invariants at layer d."""
    return sum(survivor_count(j, d - j) for j in range(1, d))


def kappa(x, y, d, j, r, rp, n):
    """kappa^{(d,j)}_{r,r'} of Theorem X1."""
    m = d - j
    rest = m - r - rp
    if rest < 0:
        return Fr(0)
    tot = Fr(0)
    for u in range(rest + 1):
        v = rest - u
        c = c_coef(m, r + u, n - j)
        if c:
            tot += c * elem(x, u) * elem(y, v)
    return Fr(-1) ** (r + rp) * tot


def cross_general(x, y, z, d, j, n, use_survivors=True):
    """X_{d,j} by Theorem X1.  With use_survivors=False the full (r,r') range
    is summed, which must give the same number -- that equality IS Theorem X2.
    """
    m = d - j
    idx = (survivors(j, m) if use_survivors
           else [(r, rp) for t in range(m + 1) for r in range(t + 1)
                 for rp in [t - r]])
    tot = Fr(0)
    for (r, rp) in idx:
        kap = kappa(x, y, d, j, r, rp, n)
        if kap:
            tot += kap * theta(x, y, z, j, r, rp, n)
    return tot


# ----------------------------------------------- decorated-graph atoms

# An atom is  I(G,alpha,beta) = sum over an assignment of a free index to each
# vertex of  prod_edges z_{s_u t_v} prod_rows x^alpha prod_cols y^beta.
# G is a bipartite multigraph; alpha, beta are vertex decorations.


def atom_eval(nr, nc, edges, alpha, beta, x, y, z, n):
    """Evaluate I(G,alpha,beta) by variable elimination.  Exact."""
    # factors: list of (vars tuple, dict from value tuple to Fr)
    factors = []
    for (u, v) in edges:
        tab = {}
        for s in range(n):
            for t in range(n):
                if z[s][t]:
                    tab[(s, t)] = z[s][t]
        factors.append(((u, nr + v), tab))
    for u in range(nr):
        if alpha[u]:
            factors.append(((u,), {(s,): x[s] ** alpha[u] for s in range(n)
                                   if x[s]}))
    for v in range(nc):
        if beta[v]:
            factors.append(((nr + v,), {(t,): y[t] ** beta[v]
                                        for t in range(n) if y[t]}))
    live = set(range(nr + nc))
    scalar = Fr(1)
    while live:
        # greedy: eliminate the variable with the smallest resulting scope
        best, bestscope = None, None
        for w in live:
            sc = set()
            for (vs, _) in factors:
                if w in vs:
                    sc |= set(vs)
            if best is None or len(sc) < len(bestscope):
                best, bestscope = w, sc
        w = best
        touch = [f for f in factors if w in f[0]]
        rest = [f for f in factors if w not in f[0]]
        outvars = tuple(sorted(v for v in bestscope if v != w))
        acc = {}
        for val in range(n):
            # partial tables restricted to var w = val
            parts = []
            for (vs, tab) in touch:
                pos = vs.index(w)
                sub = {}
                for key, c in tab.items():
                    if key[pos] == val:
                        sub[tuple(k for i, k in enumerate(key) if i != pos)] = c
                parts.append((tuple(v for v in vs if v != w), sub))
            cur = {(): Fr(1)}
            curvars = ()
            for (vs, tab) in parts:
                new = {}
                for k1, c1 in cur.items():
                    for k2, c2 in tab.items():
                        merged = dict(zip(curvars, k1))
                        ok = True
                        for vv, kk in zip(vs, k2):
                            if vv in merged and merged[vv] != kk:
                                ok = False
                                break
                            merged[vv] = kk
                        if not ok:
                            continue
                        nv = tuple(sorted(merged))
                        key = tuple(merged[v] for v in nv)
                        new[key] = new.get(key, Fr(0)) + c1 * c2
                curvars = tuple(sorted(set(curvars) | set(vs)))
                cur = new
                if not cur:
                    break
            for k, c in cur.items():
                key = tuple(k[curvars.index(v)] for v in outvars)
                acc[key] = acc.get(key, Fr(0)) + c
        acc = {k: c for k, c in acc.items() if c}
        live.discard(w)
        if outvars:
            factors = rest + [(outvars, acc)]
        else:
            factors = rest
            scalar *= acc.get((), Fr(0))
            if scalar == 0:
                return Fr(0)
    for (_, tab) in factors:
        scalar *= tab.get((), Fr(0))
    return scalar


def set_partitions(s):
    s = list(s)
    if not s:
        yield []
        return
    first, rest = s[0], s[1:]
    for p in set_partitions(rest):
        for i in range(len(p)):
            yield p[:i] + [[first] + p[i]] + p[i + 1:]
        yield [[first]] + p


def mob(p):
    """mu(0-hat, pi) on the partition lattice."""
    o = 1
    for b in p:
        o *= (-1) ** (len(b) - 1) * factorial(len(b) - 1)
    return o


def theta_atoms(j, r, rp):
    """Theta_j[r,r'] as a Z-combination of decorated-graph atoms.

    Returns a dict  key -> coefficient  with
        key = (nr, nc, sorted edges, alpha, beta).
    Atoms carrying an UNDECORATED LEAF are dropped: they are annihilated by
    the vanishing line sums of z.  That drop is the content of the
    organising principle, and collar_verify.py checks that keeping them
    changes nothing.
    """
    out = {}
    parts = list(set_partitions(range(j)))
    alphas = [a for a in product(range(r + 1), repeat=j) if sum(a) == r]
    betas = [b for b in product(range(rp + 1), repeat=j) if sum(b) == rp]
    for pi in parts:
        mpi = mob(pi)
        rowof = {}
        for bi, b in enumerate(pi):
            for a in b:
                rowof[a] = bi
        for rho in parts:
            mrho = mob(rho)
            colof = {}
            for bi, b in enumerate(rho):
                for a in b:
                    colof[a] = bi
            edges = tuple(sorted((rowof[a], colof[a]) for a in range(j)))
            rdeg = [0] * len(pi)
            cdeg = [0] * len(rho)
            for (u, v) in edges:
                rdeg[u] += 1
                cdeg[v] += 1
            for al in alphas:
                A = [0] * len(pi)
                for a in range(j):
                    A[rowof[a]] += al[a]
                if any(rdeg[u] == 1 and A[u] == 0 for u in range(len(pi))):
                    continue
                for be in betas:
                    Bv = [0] * len(rho)
                    for a in range(j):
                        Bv[colof[a]] += be[a]
                    if any(cdeg[v] == 1 and Bv[v] == 0
                           for v in range(len(rho))):
                        continue
                    key = (len(pi), len(rho), edges, tuple(A), tuple(Bv))
                    out[key] = out.get(key, Fr(0)) + Fr(mpi * mrho, 1)
    fac = Fr(1, factorial(j))
    return {k: v * fac for k, v in out.items() if v}


def theta_atoms_raw(j, r, rp):
    """theta_atoms without the leaf drop -- for the control that the drop is
    exactly the vanishing set."""
    out = {}
    parts = list(set_partitions(range(j)))
    alphas = [a for a in product(range(r + 1), repeat=j) if sum(a) == r]
    betas = [b for b in product(range(rp + 1), repeat=j) if sum(b) == rp]
    for pi in parts:
        mpi = mob(pi)
        rowof = {a: bi for bi, b in enumerate(pi) for a in b}
        for rho in parts:
            mrho = mob(rho)
            colof = {a: bi for bi, b in enumerate(rho) for a in b}
            edges = tuple(sorted((rowof[a], colof[a]) for a in range(j)))
            for al in alphas:
                A = [0] * len(pi)
                for a in range(j):
                    A[rowof[a]] += al[a]
                for be in betas:
                    Bv = [0] * len(rho)
                    for a in range(j):
                        Bv[colof[a]] += be[a]
                    key = (len(pi), len(rho), edges, tuple(A), tuple(Bv))
                    out[key] = out.get(key, Fr(0)) + Fr(mpi * mrho, 1)
    fac = Fr(1, factorial(j))
    return {k: v * fac for k, v in out.items() if v}


def eval_atoms(atoms, x, y, z, n):
    tot = Fr(0)
    for (nr, nc, edges, A, Bv), c in atoms.items():
        tot += c * atom_eval(nr, nc, edges, A, Bv, x, y, z, n)
    return tot


def atom_name(key):
    nr, nc, edges, A, Bv = key
    e = ",".join(f"r{u}c{v}" for (u, v) in edges)
    dec = []
    for u in range(nr):
        if A[u]:
            dec.append(f"x[r{u}]^{A[u]}")
    for v in range(nc):
        if Bv[v]:
            dec.append(f"y[c{v}]^{Bv[v]}")
    return f"<{nr}x{nc}|{e}" + ("|" + "*".join(dec) if dec else "") + ">"


# ------------------------------------------------------------ collar data


def split(A, n):
    """A -> (x, y, z) with the line part L_ij = x_i + y_j, z doubly centred."""
    B = [[A[i][j] - Fr(1, n) for j in range(n)] for i in range(n)]
    R = [sum(B[i][j] for j in range(n)) for i in range(n)]
    C = [sum(B[i][j] for i in range(n)) for j in range(n)]
    x = [Fr(t, n) for t in R]
    y = [Fr(t, n) for t in C]
    z = [[B[i][j] - x[i] - y[j] for j in range(n)] for i in range(n)]
    return x, y, z


def u_max_k(n, k):
    """Confinement: mu + nu <= (n-1) k! / n^(k+1).  Written here rather than
    imported because graded_y_bounds.rho2 hard-codes k = 3, 4 only."""
    return Fr((n - 1) * factorial(k), n ** (k + 1))


def collar_sample(n, k, rng, want=3, share=Fr(1, 2)):
    """Points ON the collar at (n,k): A >= 0, sum A = n, and the line block
    inside the confinement ball mu + nu <= u_max(n,k).

    Built rather than rejection-sampled.  At k >= 5 the ball has radius of
    order k!/n^k and rejection sampling from a random non-negative matrix
    essentially never lands in it, which is why graded_y_bounds.generic_collar
    returns an empty list there.
    """
    out = []
    um = u_max_k(n, k)
    for _ in range(want):
        xr = [Fr(rng.randint(-9, 9), rng.randint(1, 5)) for _ in range(n - 1)]
        xr.append(-sum(xr))
        yr = [Fr(rng.randint(-9, 9), rng.randint(1, 5)) for _ in range(n - 1)]
        yr.append(-sum(yr))
        nrm = sum(t * t for t in xr) + sum(t * t for t in yr)
        if nrm == 0:
            xr[0], xr[-1] = Fr(1), xr[-1] - 1
            nrm = sum(t * t for t in xr) + sum(t * t for t in yr)
        # scale so that mu + nu = share * u_max exactly
        sc2 = share * um / nrm
        sc = Fr(isqrt(sc2.numerator * 10 ** 24 // sc2.denominator), 10 ** 12)
        x = [t * sc for t in xr]
        y = [t * sc for t in yr]
        _, _, zr = rand_split(n, rng)
        # shrink z until A >= 0
        lam = Fr(1)
        for _ in range(200):
            A = [[Fr(1, n) + x[i] + y[j] + lam * zr[i][j] for j in range(n)]
                 for i in range(n)]
            if min(A[i][j] for i in range(n) for j in range(n)) >= 0:
                break
            lam /= 2
        out.append((x, y, [[lam * zr[i][j] for j in range(n)]
                           for i in range(n)]))
    return out


def collar_saturated(n, k):
    """The collar point that SATURATES the per-entry bound at one cell.

    A_11 = 0 with x_1, y_1 > 0, so z_11 = -(1/n + x_1 + y_1) is strictly below
    -1/n and the slice estimate p_3(z) >= -Q/n is FALSE here while the collar
    estimate p_3(z) >= -Q/n - Xi holds.  This is the separating witness the
    merge control needs: without it, charging Xi at the wrong coefficient
    cannot be detected."""
    um = u_max_k(n, k)
    # c as large as confinement allows: mu + nu = 2 c^2 n/(n-1) <= u_max.
    # Halving instead would land an octave short and the witness would stop
    # separating at some (n,k) -- it did, at (12,5).
    c2 = um * Fr(n - 1, 2 * n)
    c = Fr(isqrt(c2.numerator * 10 ** 24 // c2.denominator), 10 ** 12)
    assert 2 * c * c * Fr(n, n - 1) <= um
    b2 = (1 - Fr(1, n)) ** 2
    t = -(Fr(1, n) + 2 * c) / b2
    x = [c] + [-c / (n - 1)] * (n - 1)
    y = [c] + [-c / (n - 1)] * (n - 1)
    z = [[t * ((1 if i == 0 else 0) * (1 if j == 0 else 0)
               - (1 if i == 0 else 0) * Fr(1, n)
               - (1 if j == 0 else 0) * Fr(1, n) + Fr(1, n * n))
          for j in range(n)] for i in range(n)]
    return x, y, z


def rand_split(n, rng, spread=6, den=5):
    """A random (x, y, z) of the right shape: sum x = sum y = 0, z doubly
    centred.  Used where only the ALGEBRAIC identities are at stake, so the
    point need not sit on the collar; genericity is what matters there."""
    x = [Fr(rng.randint(-spread, spread), rng.randint(1, den))
         for _ in range(n - 1)]
    x.append(-sum(x))
    y = [Fr(rng.randint(-spread, spread), rng.randint(1, den))
         for _ in range(n - 1)]
    y.append(-sum(y))
    w = [[Fr(rng.randint(-spread, spread), rng.randint(1, den))
          for _ in range(n)] for _ in range(n)]
    rm = [sum(w[i]) for i in range(n)]
    cm = [sum(w[i][j] for i in range(n)) for j in range(n)]
    tot = sum(rm)
    z = [[w[i][j] - Fr(rm[i], n) - Fr(cm[j], n) + Fr(tot, n * n)
          for j in range(n)] for i in range(n)]
    return x, y, z
