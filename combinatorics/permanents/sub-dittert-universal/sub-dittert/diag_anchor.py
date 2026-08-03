"""
Anchor-grade verification of the diagonal witnesses, through the TRUSTED route.

WHY THIS FILE EXISTS.  `diag_solve.py` decides positive definiteness of the 21
CANONICAL BLOCKS using a system it built itself.  §6b.83 lesson 3: "a verifier
that reuses the producer's way round a wall is not a verifier."  So the witness
is re-checked here by the route of record --

    results/verify_subdittert.py     builds F(b) from the 1992 definition,
                                     loaded BY PATH and NOT EDITED, and it is
                                     already k-general (`build_F(n, k)`,
                                     `direct_sigma_k(A, n, k)`,
                                     `ryser_sigma_k(A, n, k)`)
    anchor_check3.py                 checks [1] [2] [3] [5] [6] and the
                                     (A1)/(A2) conjugacy

-- neither of which reads `diag_core`'s orbit system at all.  The identity is
compared monomial by monomial over Q against an F this pipeline did not build.

WHAT MAKES THE k = 5 RUN LEGITIMATE.  `anchor_check3.K` is a module global read
at CALL time everywhere it matters (checks [1], [2], [3] and the control), so
setting it to 5 changes the problem and nothing else.  Two things are k = 4
constants and are handled explicitly rather than left to fail quietly:

  * `EXPECT_BOUND` -- the typed-in `2 - k!/n^k` table.  The k = 5 entries are
    typed in HERE, computed by hand and not by the pipeline, so the check keeps
    its property of comparing two independent sources:
        n = 5:  2 - 120/3125  =  1226/625     <- see the note below
        n = 6:  2 - 120/7776  =   643/324
        n = 7:  2 - 120/16807 = 33494/16807

    A THIRD COLLISION, found while typing that table.  `2 - gamma(5,5)` and
    `2 - gamma(5,4)` are BOTH 1226/625, because 120/3125 = 24/625.  NOTES §6
    records two such collisions already ("the second collision", n = 4 and
    n = 5, checked by `validate.py`); this is another, and it means the n = 5
    bound cannot distinguish k = 4 from k = 5 and must never be used as
    evidence that a k = 5 run really ran at k = 5.  The n = 6 entry is not
    degenerate (643/324 against k = 4's 107/54) and is the one this file uses.
  * `control()` -- the streamed-vs-dense positive control runs against the
    STORED DENSE (5,4) certificate, so it is a k = 4 object.  It is run FIRST,
    at K = 4, and it validates the EXPANSION ENGINE, which carries no k at all
    (it multiplies Gram entries by monomials and relabels by transporters).
    Only then is K moved to 5.  Running it at K = 5 would compare a k = 5
    expansion against a k = 4 certificate and fail for the wrong reason.

THE SECOND POSITIVE CONTROL, and it is the one that tests THIS pipeline.
`diag_solve.py` also produced a (k = 4, n = 6) point from scratch.  That point
is put through the identical anchor run at K = 4.  If `diag_core`'s orbit
indexing were permuted, or `recover_lambda` wrong, or the rounding subtly
damaging, the (4,6) run would fail -- against a cell whose true answer is known
independently.  So a k = 5 PASS cannot be a coincidence of a broken pipeline.
"""

import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "dittert"))
sys.path.insert(0, HERE)
import anchor_check3 as ac                                          # noqa: E402
import h2_anchor as ha                                              # noqa: E402

BOUND_K5 = {5: "1226/625", 6: "643/324", 7: "33494/16807"}

# `h2_anchor6.check_conjugations` calls `ha.load_point(n)` with no name, so it
# assembles H from the DEFAULT stored witness while `build_claim` assembles it
# from the one under test; `anchor_check3.run` then aborts with "the two
# assemblies of H disagree".  That is a NAME mismatch and not a mathematical
# failure -- it fired on the (k = 4, n = 6) control too, whose point is known
# good.  The fix is to make the default resolve to the witness under test for
# the duration of the run, and it is done by wrapping rather than by editing
# `h2_anchor.py`, which other runs share.
_REAL_LOAD = ha.load_point


def _pin_witness(name):
    def load_point(n, nm=None):
        return _REAL_LOAD(n, nm if nm is not None else name)
    ha.load_point = load_point


def _unpin():
    ha.load_point = _REAL_LOAD


def main(argv):
    out = lambda s: print(s, flush=True)                        # noqa: E731
    vs = ac.load_trusted()
    out("trusted verifier results/verify_subdittert.py loaded by path, "
        "unmodified")

    do_control = "--no-control" not in argv
    if do_control:
        t0 = time.time()
        assert ac.K == 4, "the streamed/dense control is a k = 4 object"
        if not ac.control(vs, out):
            out("ENGINE CONTROL FAILED -- nothing below would mean anything")
            return 1
        out(f"  engine control complete ({time.time() - t0:.0f} s)")

    jobs = []
    for a in argv:
        if a.count(",") == 2:
            nn, kk, name = a.split(",")
            jobs.append((int(nn), int(kk), name))
    if not jobs:
        jobs = [(6, 4, "diag_n6_k4.json"), (6, 5, "diag_n6_k5.json")]

    verdicts = {}
    for n, k, name in jobs:
        old = ac.K
        ac.K = k
        if k == 5:
            ac.EXPECT_BOUND = dict(BOUND_K5)
        t0 = time.time()
        out(f"\n########## ANCHOR RUN: (k = {k}, n = {n}) witness {name}")
        _pin_witness(name)
        try:
            res = ac.run(n, vs, out=out, witness=name)
        finally:
            ac.K = old
            _unpin()
        allok = bool(res) and all(res.values())
        verdicts[(n, k, name)] = (allok, res)
        out(f"\n{'=' * 70}")
        out(f"(k = {k}, n = {n}) witness {name}: "
            f"{'ALL CHECKS PASS' if allok else 'FAILURES PRESENT'} "
            f"({time.time() - t0:.0f} s)")
        for key, val in res.items():
            out(f"    {'PASS' if val else 'FAIL'}  {key}")

    out(f"\n{'=' * 70}\nSUMMARY")
    for (n, k, name), (allok, _) in verdicts.items():
        out(f"  (k = {k}, n = {n})  {name:24s}  "
            f"{'ALL CHECKS PASS' if allok else 'FAILURES PRESENT'}")
    return 0 if all(v[0] for v in verdicts.values()) else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
