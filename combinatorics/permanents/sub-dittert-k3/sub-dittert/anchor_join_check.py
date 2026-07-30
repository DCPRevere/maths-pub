"""
The JOIN between PART 1 and the congruence assertion, as a stored artefact.

WHY THIS EXISTS SEPARATELY.  Check [4] closes at a given n by composing two runs
that used DIFFERENT BASES of the same isotypic components:

  * `anchor_wtest.py` PART 1 built each component with `close_component` and
    proved the components span and are pairwise H-orthogonal over Q;
  * `anchor_cb_measure.py` built each component with `slice_closure`, as whole
    translated slices, and proved each component Gram is `C_b (x) h_b`.

Both are closures of the same seed `E_b` under the same group action to the same
rank, so both span the full G-span of `E_b`, and H-orthogonality of SUBSPACES is
basis-independent -- so the two results compose.  That argument is sound and it is
also exactly the kind of join where a mismatch would go unnoticed, because each
run passes on its own terms.  The concrete check is that the two runs agree on
every component's DIMENSION: `d_b * e_b` from the C_b table must equal PART 1's
component dimension, for all 21 blocks, on both sides.

WHY IT IS A FILE AND NOT A PARAGRAPH.  The first version of this comparison was
run inline and reported `ALL 21 AGREE` while having parsed ZERO PART 1 rows -- the
section split landed past the final verdict line, the loop body never executed,
and the "no mismatches" branch fired.  The verdict it printed happened to be true,
which is what made it dangerous.  So the parsed COUNTS are asserted against a
typed-in 21 before any comparison, both counts are printed beside the verdict, and
the run exits non-zero on any mismatch.  A cited witness must be stored, and a
check that can pass vacuously is not a check.

PROVENANCE.  The log file each number came from is printed, because these are
readings of other runs' artefacts rather than fresh computations.
"""

import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
RESULTS = os.path.join(HERE, "results")

EXPECT_BLOCKS = 21                      # 11 sigma_11 + 10 sigma_0, every n
EXPECT_B = {5: 350, 6: 702, 7: 1274, 8: 2144, 9: 3402}

PART1_ROW = re.compile(
    r"^\s{4}(\S.*?)\s+block size\s+(\d+)\s+->\s+component dim\s+(\d+)\s*$", re.M)
CB_ROW = re.compile(
    r"^\s{4}(\S.*?)\s+h_b\s+(\d+)x(\d+)\s+(PD|NOT PD)\s+"
    r"C_b\s+(\d+)x(\d+)\s+(PD|NOT PD)", re.M)


def part1_section(n):
    """The PART 1 block listing for this n, and the log it came from."""
    hdr = (f"PART 1 (exact over Q): span and H-orthogonality, (k = 4, n = {n})")
    best = None
    for name in sorted(os.listdir(RESULTS)):
        if not (name.startswith("anchor_wtest") and name.endswith(".log")):
            continue
        path = os.path.join(RESULTS, name)
        text = open(path).read()
        if hdr not in text:
            continue
        sec = text[text.index(hdr) + len(hdr):]
        # stop before the next PART header, so a multi-n log cannot bleed
        cut = min([i for i in (sec.find("\n--- PART"), sec.find("--- why there"))
                   if i >= 0] or [len(sec)])
        sec = sec[:cut]
        rows = PART1_ROW.findall(sec)
        if best is None or len(rows) > len(best[1]):
            best = (path, rows)
    return best


def cb_table(n):
    path = os.path.join(RESULTS, f"anchor_cb_measure_n{n}.log")
    if not os.path.exists(path):
        return None
    return path, CB_ROW.findall(open(path).read())


def check(n, out):
    out(f"\n=== JOIN CHECK at (k = 4, n = {n}) ===")
    p1 = part1_section(n)
    cb = cb_table(n)
    if p1 is None:
        out(f"  no PART 1 log found for n = {n}")
        return False
    if cb is None:
        out(f"  no anchor_cb_measure_n{n}.log found")
        return False
    p1path, p1rows = p1
    cbpath, cbrows = cb
    out(f"  PART 1 component dims from: {os.path.relpath(p1path, HERE)}")
    out(f"  C_b / h_b table from:       {os.path.relpath(cbpath, HERE)}")

    # NON-VACUITY, asserted before anything is compared
    out(f"  parsed {len(p1rows)} PART 1 rows and {len(cbrows)} C_b rows "
        f"(both must be {EXPECT_BLOCKS})")
    if len(p1rows) != EXPECT_BLOCKS or len(cbrows) != EXPECT_BLOCKS:
        out(f"  *** REFUSING a vacuous comparison: expected "
            f"{EXPECT_BLOCKS} rows on each side")
        return False

    dims = {k.strip(): (int(d), int(dim)) for k, d, dim in p1rows}
    ed = {}
    for k, d1, d2, pdh, e1, e2, pdc in cbrows:
        ed[k.strip()] = (int(d1), int(e1), pdh, pdc)
    if len(dims) != EXPECT_BLOCKS or len(ed) != EXPECT_BLOCKS:
        out(f"  *** duplicate block names: {len(dims)} and {len(ed)} distinct "
            f"keys from {EXPECT_BLOCKS} rows")
        return False

    bad, total = [], 0
    for name in sorted(dims):
        d, dim = dims[name]
        if name not in ed:
            bad.append((name, "absent from the C_b table"))
            out(f"    {name:28s} *** absent from the C_b table")
            continue
        d2, e, pdh, pdc = ed[name]
        total += dim
        why = None
        if d != d2:
            why = f"block size {d} vs {d2}"
        elif d * e != dim:
            why = f"d*e = {d}*{e} = {d * e} vs component dim {dim}"
        elif pdh != "PD" or pdc != "PD":
            why = f"h_b {pdh}, C_b {pdc}"
        if why:
            bad.append((name, why))
        out(f"    {name:28s} d={d:3d}  e={e:4d}  d*e={d * e:5d}  "
            f"PART1 dim={dim:5d}  h_b {pdh:6s} C_b {pdc:6s}  "
            f"{'OK' if not why else '*** ' + why}")

    B = EXPECT_B.get(n)
    want = 2 * B if B else None
    out(f"  total component dimension {total} "
        + (f"against 2 x B = 2 x {B} = {want}  "
           f"{'OK' if total == want else '*** MISMATCH'}" if want else ""))
    if want is not None and total != want:
        bad.append(("total", f"{total} vs {want}"))
    ok = not bad
    out(f"  ==> (k = 4, n = {n}): "
        + ("the two runs describe the SAME components; all "
           f"{EXPECT_BLOCKS} blocks agree and every h_b and C_b is PD"
           if ok else f"JOIN FAILS: {bad}"))
    return ok


def main(argv):
    ns = [int(a) for a in argv if a.isdigit()] or [5, 6, 7]
    out = lambda s: print(s, flush=True)                       # noqa: E731
    out("=" * 74)
    out("JOIN between PART 1 and the congruence assertion -- stored artefact")
    out("=" * 74)
    out("Composing check [4] uses two runs with DIFFERENT bases of the same")
    out("components.  H-orthogonality of subspaces is basis-independent, so they")
    out("compose -- but the dimensions must agree, and this is the check whose")
    out("first inline version passed while parsing ZERO rows.  Counts are")
    out("therefore asserted against a typed-in 21 before any comparison.")
    out("=" * 74)
    allok = True
    for n in ns:
        allok = check(n, out) and allok
    out("\n" + "=" * 74)
    out("ALL JOINS VERIFIED" if allok else "AT LEAST ONE JOIN FAILED")
    return 0 if allok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
