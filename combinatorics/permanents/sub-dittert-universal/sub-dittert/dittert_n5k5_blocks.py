"""
The 21 canonical blocks of the `(k = 5, n = 5)` Dittert anchor, for the kernel.

WHY THIS CELL AND NOT `(4,4)`.  `.verification/lean-ldl-cost-2026-08-03.txt`
measures the Lean congruence instrument at `time ~ s^2.85`, `memory ~ s^2.34` in
the block side.  `n = 5` keeps the 21-block design, so the largest object the
kernel ever sees is a `48 x 48` `C_b` -- about 5 GB and minutes.  `n = 4` breaks
the design (`D45.md` §2) and leaves two dense `152 x 152` forms at about 77 GB
apiece, which no amount of patience fixes.  So `B = 350` is the cheap cell and
`B = 152` the expensive one.  That inversion is the whole reason this file is
`n5k5` and not `n4k4`.

THE ONE NEW CODE PATH, AND ITS CONTROL.  `anchor_cb_measure.build_cb` gained a
`name` argument so that it can be pointed at a `k = n` witness; everything else
in the chain is untouched.  `SOLVER.md` §S.6 forbids a certificate being the
first user of a new code path, so `control()` runs `build_cb(5, out)` with
`name=None` -- the historical default -- and compares the result to the stored
`leanproj/congruence_blocks_n5.json` block by block, entry by entry, exactly
over Q.  Only if that reproduces does `dump()` run at `diag_n5_k5.json`.

WHAT THIS FILE DOES *NOT* CLAIM.  It does not prove Dittert at `n = 5`.  It
produces the objects whose positive definiteness is the `[4]` half of the
`D45.md` six-check standard, in a form the Lean kernel can check.  The other
half -- the exact identity over 14,005 monomials -- is a separate item and is
not touched here.  `D45.md` §3.2 already decided `[4]` outside Lean; what moves
is the layer it is decided on.

Run under `guard.sh`.
"""

import json
import os
import sys
import time
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import anchor_cb_measure as cb                                      # noqa: E402

LEANDIR = os.path.join(os.path.dirname(HERE), "leanproj")
STORED = os.path.join(LEANDIR, "congruence_blocks_n5.json")
OUT = os.path.join(LEANDIR, "congruence_blocks_n5k5.json")

N = 5
WITNESS = "diag_n5_k5.json"


def _rows(sides):
    """Flatten build_cb's per-side output to the stored JSON's row shape."""
    out = []
    for label, rows in sides:
        for name, d, e, hb, C in rows:
            out.append(dict(side=label, name=name, d=d, e=e,
                            h=[[[x.numerator, x.denominator] for x in r]
                               for r in hb],
                            C=[[[x.numerator, x.denominator] for x in r]
                               for r in C]))
    return out


def control(out):
    """`build_cb` with the new argument at its default must reproduce the
    stored `(k = 4, n = 5)` blocks exactly.  Anything less and nothing here is
    reportable."""
    out("=" * 74)
    out("CONTROL: build_cb(5, out) at the DEFAULT witness, against the stored")
    out(f"  {STORED}")
    out("=" * 74)
    ok, sides, secs = cb.build_cb(N, out)
    if not ok:
        out("  *** build_cb reported a failure at the default witness")
        return False
    got = _rows(sides)
    want = json.load(open(STORED))["blocks"]
    if len(got) != len(want):
        out(f"  *** block count {len(got)} against stored {len(want)}")
        return False
    for a, b in zip(got, want):
        for key in ("side", "name", "d", "e", "h", "C"):
            if a[key] != b[key]:
                out(f"  *** block {a['name']} differs in {key}")
                return False
    out(f"  {len(got)} blocks IDENTICAL to the stored (k = 4, n = 5) set, "
        f"entry for entry over Q ({secs:.0f} s)")
    out("  ==> the `name` argument does not disturb the historical path")
    return True


def dump(out):
    out("")
    out("=" * 74)
    out(f"BUILD: build_cb(5, out, name={WITNESS!r})  --  the k = n cell")
    out("=" * 74)
    t0 = time.time()
    ok, sides, secs = cb.build_cb(N, out, name=WITNESS)
    if not ok:
        out("  *** the congruence FAILED to re-assert on the built objects")
        return False
    rows = _rows(sides)

    # THE FINDING, and the two controls it turns into.  `C_b` is the matrix of
    # SLICE SCALARS of the design's intertwiners and is therefore a property of
    # the invariant subspace, NOT of the point: by Schur, `S_i G S_j^T` and
    # `h_b` are images of the same invariant vector under intertwiners into the
    # same irreducible component, so they are proportional with a factor that
    # does not see `w`.  Measured here, at two witnesses that differ in every
    # entry.  Consequences: (i) all 21 `C_b` must reproduce the stored (k = 4,
    # n = 5) set exactly -- a positive control on the design; (ii) at least one
    # `h_b` must MOVE -- otherwise the k = n witness never reached the
    # assembly.  Both are checked, and each catches a different failure.
    want = json.load(open(STORED))["blocks"]
    sameC = sum(1 for a, b in zip(rows, want) if a["C"] == b["C"])
    sameH = sum(1 for a, b in zip(rows, want) if a["h"] == b["h"])
    out(f"  C_b reproducing the stored design: {sameC} of {len(rows)}")
    out(f"  h_b unchanged from (5,4):          {sameH} of {len(rows)}")
    if sameC != len(rows):
        out("  *** a C_b moved with the witness.  The design is not what the "
            "Schur argument says it is; refusing to write.")
        return False
    if sameH == len(rows):
        out("  *** every h_b is unchanged -- the k = 5 witness did not reach "
            "the assembly.  Refusing to write.")
        return False
    out("  ==> C_b belongs to the DESIGN and is already kernel-checked in "
        "CongruenceBlocksN5/;")
    out("      only the 21 h_b are new at this cell, and they are the SMALL "
        "factors.")

    sides_seen = sorted({r["side"] for r in rows})
    big = max(r["e"] for r in rows)
    bigh = max(r["d"] for r in rows)
    out(f"  {len(rows)} blocks over sides {sides_seen}; "
        f"largest C_b {big}x{big}, largest h_b {bigh}x{bigh}")

    pd_ok = True
    for r in rows:
        C = [[F(a, b) for a, b in row] for row in r["C"]]
        h = [[F(a, b) for a, b in row] for row in r["h"]]
        okc, ic = cb.ldl_pd(C)
        okh, ih = cb.ldl_pd(h)
        pd_ok = pd_ok and okc and okh
        out(f"    {r['name']:26s} h_b {r['d']:3d} {'PD' if okh else 'NOT PD'}"
            f"   C_b {r['e']:3d} {'PD' if okc else 'NOT PD'}"
            + (f"   least pivot {float(ic):.6e}" if okc else ""))
    if not pd_ok:
        out("  *** some block is NOT positive definite; refusing to write")
        return False

    with open(OUT, "w") as f:
        json.dump(dict(n=N, k=5, witness=WITNESS, seconds=secs, blocks=rows), f)
    out(f"  wrote {OUT}: {len(rows)} blocks, build {secs:.0f} s, "
        f"total {time.time() - t0:.0f} s")
    return True


def main():
    out = lambda s: print(s, flush=True)                       # noqa: E731
    if not control(out):
        return 1
    if not dump(out):
        return 1
    out("\nALL PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
