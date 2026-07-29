"""
Export the sub-Dittert certificate as SELF-CONTAINED JSON.

The point of this file is to remove every trace of the machinery that produced
the certificate.  What comes out is:

  * n, k, and the bound M = 2 - k!/n^k, as exact rationals;
  * the Gram matrix G0 of sigma_0, written out densely;
  * the Gram matrix G[p] of EVERY multiplier sigma_p, p = 0..n^2-1, written out
    densely -- not one matrix plus a group action, because then the verifier
    would have to re-implement the group and could inherit a bug from it;
  * the multiplier polynomial lambda as an explicit monomial dictionary.

A verifier reading this file needs nothing but rational arithmetic.  It does not
need orbits, transporters, stabilisers, block structure, or an SDP solver.  It
checks

    F(b) = sum_uv G0[u][v] b_u b_v
         + sum_p (1/n + b_p) sum_uv G[p][u][v] b_u b_v
         + lambda(b) * (sum_q b_q)

as an identity of polynomials, and checks that G0 and every G[p] are positive
definite -- from which F >= 0 on K_n and uniqueness at b = 0 both follow.
"""

import json
import os
import pickle
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "dittert"))
sys.path.insert(0, HERE)  # HERE must win the name `expand` (see sos.py)
from exactsd import assemble                                      # noqa: E402
from sos import transporters                                      # noqa: E402
from symmetry import monomials                                    # noqa: E402


def export(n, k, deg_basis=1):
    tag = f"n{n}k{k}d{deg_basis}"
    src = os.path.join(HERE, "results", f"subdittert_{tag}.pkl")
    with open(src, "rb") as fh:
        c = pickle.load(fh)
    basis = c["basis"]
    B = len(basis)
    N = n * n
    # The Gram basis is exported explicitly, as a list of monomials, so the
    # verifier never has to reconstruct it.  Degree 1 gives basis[u] = (u,);
    # degree 2 also carries the quadratic monomials.  Either way the constant
    # monomial is EXCLUDED, so every sigma vanishes at b = 0 automatically.
    assert all(1 <= len(m) <= deg_basis for m in basis), "unexpected Gram basis"

    G0 = assemble(B, c["g_orbits"], c["xq"])
    H = assemble(B, c["s_orbits"], c["yq"])

    # sigma_p(b) = sigma_11(g_p^{-1} b): move the Gram by the transporter.
    trans = transporters(n, (0, 0))
    bindex = {m: u for u, m in enumerate(basis)}
    Gp = []
    for p in range(N):
        g = trans[p]                       # g permutes the VARIABLES
        # induced permutation of the Gram basis
        perm = [bindex[tuple(sorted(g[t] for t in m))] for m in basis]
        M = [[F(0)] * B for _ in range(B)]
        for u in range(B):
            for v in range(B):
                if H[u][v]:
                    M[perm[u]][perm[v]] += H[u][v]
        Gp.append(M)

    # lambda as an explicit monomial dictionary
    lam_mons = monomials(N, c["TOPDEG"] - 1)
    lam = {}
    for vi, members in enumerate(c["lam_orbit_reps"]):
        co = c["zq"][vi]
        if not co:
            continue
        for t in members:
            key = ",".join(str(x) for x in lam_mons[t])
            lam[key] = str(F(lam[key]) + co) if key in lam else str(co)

    def smat(M):
        return [[str(x) for x in row] for row in M]

    out = dict(
        problem="Cheon-Hwang sub-Dittert",
        statement="E_k(r) + E_k(c) - P_k(A) <= 2 - k!/n^k on K_n, "
                  "equality only at J_n/n",
        n=n, k=k, N=N,
        bound_M=str(c["M"]),
        gram_basis_note="basis[u] is a monomial in the variables b_0..b_{N-1}, "
                        "given as a list of variable indices with repetition; "
                        "variable u corresponds to matrix position "
                        "(u // n, u % n).  The constant monomial is EXCLUDED, "
                        "so every sigma vanishes at b = 0 automatically",
        basis=[list(m) for m in basis],
        G0=smat(G0),
        Gp=[smat(M) for M in Gp],
        lam=lam,
        identity="F(b) = sum_uv G0[u][v] m_u m_v + sum_p (1/n + b_p) "
                 "sum_uv Gp[p][u][v] m_u m_v + lam(b) * sum_q b_q, "
                 "where m_u is the monomial basis[u]",
    )
    dst = os.path.join(HERE, "results", f"subdittert_{tag}_certificate.json")
    with open(dst, "w") as fh:
        json.dump(out, fh, indent=1)
    ncoef = 1 + B * B + N * B * B + len(lam)
    print(f"wrote {dst}")
    print(f"  {B}x{B} G0, {N} multiplier Grams, {len(lam)} lambda monomials")
    print(f"  file size {os.path.getsize(dst)} bytes")
    return dst


if __name__ == "__main__":
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    k = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    db = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    export(n, k, db)
