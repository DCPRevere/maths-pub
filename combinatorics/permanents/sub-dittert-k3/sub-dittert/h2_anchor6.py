"""
n = 6 to ANCHOR GRADE by the legitimate route -- option 1 of the recorded ruling.

The two-Gram shortcut is only acceptable if the conjugacy is PROVED rather than
assumed.  NOTES §6 forbids "fixing" the cost by skipping matrices; it does not
forbid deducing the skipped factorisations from an explicitly verified group
action.  This module supplies that deduction, and it is cheap because it needs
no factorisation at all.

WHAT MAKES THE DEDUCTION VALID, stated before it is used.  The certificate
DEFINES `sigma_p = sigma_11 o g_p^{-1}` for an explicit transporter `g_p`
carrying `(0,0)` to `p` (`sos.transporters`).  Two facts make that definition
sound and make PD of the other `n^2 - 1` Grams a consequence rather than a
hope:

  (A1)  the transporter's action carries the Gram BASIS to itself bijectively,
        so the transport is a permutation `pi_p` of the B basis monomials and
        `G_p = P_p H P_p^T` for the corresponding permutation matrix.  A
        permutation conjugate of a positive definite matrix is positive
        definite, so one factorisation settles all `n^2`.

  (A2)  `H` is invariant under `Stab((0,0))`.  Without this `sigma_p` depends
        on WHICH transporter is chosen and is not well defined at all --
        `sos.transporters` says so in its own docstring.  This is the check
        that would catch a wrong `H`, and no log in the folder had stated it.

Both are exact: (A1) is a bijection test on `B` monomial images per position,
(A2) is an entry-by-entry rational equality over `B^2` entries.  Neither reads
a float and neither factorises anything.

WHAT THIS DOES NOT DO.  It does not establish the identity.  Check [3] --
full-monomial coefficient comparison in code independent of the pipeline -- is
the remaining half, and its cost is measured here rather than guessed, because
the dense anchor export at n = 6 would be about 355 MB (the (5,4) one is 61 MB
at `B = 350`, `N = 25`) and 37 exact LDLs at `B = 702` would be about 11
CPU-hours.  If (A1) or (A2) fails, or if [3] is not run, the correct label is
"two-Gram grade, conjugacy unverified" and NOT anchor grade.
"""

import os
import sys
import time
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "dittert"))
sys.path.insert(0, HERE)
import sos                                                         # noqa: E402
import h2_anchor as ha                                             # noqa: E402

K, DEG_BASIS = 4, 2


def induced(basis, index, g):
    """The permutation of basis monomials induced by a variable permutation."""
    out = []
    for mono in basis:
        img = tuple(sorted(g[v] for v in mono))
        j = index.get(img)
        if j is None:
            return None, img
        out.append(j)
    return out, None


def check_conjugations(n, out=print, d=None):
    """
    `d` may be a prebuilt system, so a caller that already has one (or that
    must avoid `build_sdp`'s degree-TOPDEG monomial table at large n) can pass
    it in.  Default None reproduces the original behaviour exactly.
    """
    t0 = time.time()
    d = d if d is not None else sos.build_sdp(n, K, DEG_BASIS, verbose=False)
    B, N = d["B"], n * n
    basis = d["basis"]
    index = {tuple(m): i for i, m in enumerate(basis)}
    out(f"  n = {n}: B = {B}, N = {N} variables, {len(basis)} basis monomials "
        f"({time.time() - t0:.0f} s to build)")

    w, doc = ha.load_point(n)
    ng, ns = len(d["g_orbits"]), len(d["s_orbits"])
    H = ha.assemble(B, d["s_orbits"], w[ng:ng + ns])
    out(f"  sigma_11 Gram H assembled {B}x{B} from the stored point")

    # ---- (A1) every transporter permutes the Gram basis, bijectively
    trans = sos.transporters(n, (0, 0))
    bad = []
    perms = {}
    for p in range(N):
        pi, missing = induced(basis, index, trans[p])
        if pi is None:
            bad.append((p, missing))
            continue
        if len(set(pi)) != B:
            bad.append((p, "not injective"))
            continue
        perms[p] = pi
    if bad:
        out(f"  (A1) FAILED for {len(bad)} of {N} positions, e.g. {bad[0]}")
        return False, None
    out(f"  (A1) all {N} transporters induce a BIJECTION of the {B} basis "
        f"monomials, so every G_p = P_p H P_p^T exactly")
    out(f"       => positive definiteness of H implies it for all {N} "
        f"multiplier Grams.  {N - 1} factorisations DEDUCED, none skipped.")

    # ---- (A2) H is invariant under Stab((0,0)); without this sigma_p is
    # not even well defined, and the choice of transporter would matter.
    gens = sos.stab_generators(n, (0, 0))
    out(f"  (A2) checking H against {len(gens)} generators of Stab((0,0)) "
        f"over {B * B} entries each")
    for gi, g in enumerate(gens):
        pi, missing = induced(basis, index, g)
        if pi is None:
            out(f"  (A2) FAILED: stabiliser generator {gi} moves a basis "
                f"monomial off the basis ({missing})")
            return False, None
        for u in range(B):
            Hu, Hpu = H[u], H[pi[u]]
            for v in range(B):
                if Hpu[pi[v]] != Hu[v]:
                    out(f"  (A2) FAILED: generator {gi} at entry ({u},{v})")
                    return False, None
    out(f"  (A2) H is EXACTLY invariant under Stab((0,0)): sigma_p is well "
        f"defined and independent of which transporter is used")
    out(f"  conjugation verification complete in {time.time() - t0:.0f} s")
    return True, (d, H, perms)


def identity_cost(n, out=print):
    """
    Measure, not guess, what check [3] costs at this n.

    The anchor expands `sum_{u,v} G0[u][v] m_u m_v` plus the same for each of
    the `n^2` multiplier Grams.  That is `(1 + n^2) B^2` monomial products.  The
    rate is measured on a real slice of the work rather than assumed.
    """
    d = sos.build_sdp(n, K, DEG_BASIS, verbose=False)
    B, N = d["B"], n * n
    basis = d["basis"]
    t0 = time.time()
    trials = 0
    rhs = {}
    for u in range(min(B, 40)):
        for v in range(B):
            m = tuple(sorted(basis[u] + basis[v]))
            rhs[m] = rhs.get(m, F(0)) + F(1)
            trials += 1
    rate = trials / max(time.time() - t0, 1e-9)
    total = (1 + N) * B * B
    out(f"  check [3] cost at n = {n}: {total:,} monomial products at a "
        f"measured {rate:,.0f}/s = {total / rate / 3600:.1f} hours")
    out(f"     (the anchor's own route; using the verified conjugations of "
        f"(A1) to relabel one expansion instead cuts it to about "
        f"{(B * B + N * len(rhs) * B // 40) / rate / 3600:.1f} hours)")
    out(f"  the dense anchor export at n = {n} would be about "
        f"{(1 + N) * B * B * 12 / 1e6:.0f} MB of JSON")
    return total / rate


def main(ns):
    for n in ns:
        print(f"\n=== n = {n} to anchor grade: conjugation verification ===",
              flush=True)
        ok, payload = check_conjugations(n)
        print(f"  ==> (A1) and (A2): {'BOTH HOLD' if ok else 'FAILED'}",
              flush=True)
        if ok:
            print(f"\n=== n = {n}: measured cost of check [3] ===", flush=True)
            identity_cost(n)


if __name__ == "__main__":
    main([int(a) for a in sys.argv[1:]] or [6])
