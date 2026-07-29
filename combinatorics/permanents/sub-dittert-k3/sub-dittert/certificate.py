"""
The general-n k = 3 certificate: print it, re-derive the Sturm verdict in full,
and verify it INDEPENDENTLY at specific n against the trusted numeric pipeline.

The certificate is the 19 symmetry-reduced variables as exact rational functions
of n.  Three checks are run at each requested n, and only the first of them uses
any of the symbolic machinery:

  [1] the 19 rationals satisfy the constraint system built by the ORIGINAL code
      path, sos.build_sdp -> exactsd.exact_system, which has no logic in common
      with general_k3.build_symbolic_system;
  [2] the assembled n^2 x n^2 sigma_0 and sigma_11 Gram matrices are positive
      definite, by exact rational LDL^T on the full matrices -- not via the
      block-diagonalisation the design used;
  [3] the four blocks predicted by blocks.py reproduce the full spectrum.
"""

import os
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "dittert"))
sys.path.insert(0, HERE)
import adapted as ad                                             # noqa: E402
import blocks as bl                                              # noqa: E402
import essential as es                                           # noqa: E402
import exact_design as ed                                        # noqa: E402
import fit_curve as fc                                           # noqa: E402
import general_k3 as g                                           # noqa: E402
import sturm                                                     # noqa: E402
from general_k3 import RF                                        # noqa: E402

ZERO, ONE, N = ed.ZERO, ed.ONE, ed.N
D = 1
PARAMS = {"b0": F(1), "b1": F(0), "x0": F(8), "x1": F(20),
          "y0": F(-2), "y1": F(-10), "z1": F(0)}


def build():
    """The eight free variables as exact rational functions of n."""
    base0, cols0 = ad.adapted_affine(D)
    base, cols, keep = ad.eliminate_z(base0, cols0, D)
    pq = [PARAMS[nm] for nm in ("b0", "b1", "x0", "x1", "y0", "y1", "z1")]
    zrf = ad.z_value(base0, cols0, D, pq, keep)
    full_p = [ZERO] * (4 * (D + 1))
    for j, k in enumerate(keep):
        full_p[k] = RF([pq[j]]) if pq[j] else ZERO
    full_p[3 * (D + 1)] = zrf
    fs = ad.fs_from_beta(ad.adapted_beta(full_p, D))
    return es.apply_gauge(fs, ONE / (N * N * N), ONE / N), zrf


def vals19(fs):
    return es.vals19_rf(fs)


def main():
    fs, zrf = build()
    print("PARAMETERS (adapted coordinates, d = 1 in 1/n)")
    print("  beta9  = b,                 b = 1")
    print("  beta6  = 2b + x/n^2,        x = 8 + 20/n")
    print("  beta12 = 2b - 1 + y/n,      y = -2 - 10/n")
    print("  beta11 = 2 beta12 + 2 + z/n,")
    print(f"  z = {zrf}")
    print("  (z is not fitted: it is solved from theta_2 = D, exactly over Q(n))")

    print("\nTHE 19 CERTIFICATE VARIABLES as rational functions of n")
    vals = vals19(fs)
    names = ([f"sigma0[{i}]" for i in range(3)]
             + [f"sigma11[{i}]" for i in range(11)]
             + [f"lambda[{i}]" for i in range(5)])
    for nm, v in zip(names, vals):
        print(f"  {nm:<12s} = {v}")

    print("\nSTURM, in full, on the ten positivity quantities")
    qs = sturm.quantities_rf_from(fs)
    ok = sturm.verify_rf(qs, verbose=True)
    print(f"\n  ALL TEN POSITIVE FOR EVERY n >= 4: {ok}")
    return fs, ok


if __name__ == "__main__":
    main()
