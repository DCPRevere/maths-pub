#!/usr/bin/env python3
"""Run every graded verifier in this folder and print one green/red table.

One command re-verifies every displayed claim of the campaign:

    ./guard.sh python3 verify_all.py            # or under mathsguard.slice

Discovers graded_verify_*.py plus bern_verify.py, runs each in sequence in
this directory, and reports PASS/FAIL per verifier from its exit code, with
the final verdict lines quoted. Exits 0 iff every verifier passes. The
trusted first-acceptance verifier (results/verify_subdittert.py) and the
fast layer (modverify.py, anchor_check3_fast.py) are per-cell tools with
their own drivers and are not run here.
"""

import glob
import subprocess
import sys
import time

HERE = __file__.rsplit("/", 1)[0] if "/" in __file__ else "."


def main() -> int:
    names = sorted(glob.glob(HERE + "/graded_verify_*.py"))
    names += sorted(glob.glob(HERE + "/bern_verify.py"))
    if not names:
        print("no verifiers found", file=sys.stderr)
        return 2

    rows = []
    worst = 0
    for path in names:
        name = path.rsplit("/", 1)[-1]
        t0 = time.time()
        proc = subprocess.run(
            [sys.executable, path],
            cwd=HERE,
            capture_output=True,
            text=True,
        )
        dt = time.time() - t0
        tail = [
            line
            for line in proc.stdout.splitlines()
            if "TOTAL" in line or "VERDICT" in line or "PASS" in line
        ][-2:]
        status = "PASS" if proc.returncode == 0 else "FAIL"
        if proc.returncode != 0:
            worst = 1
        rows.append((name, status, dt, " | ".join(t.strip() for t in tail)))
        print(f"[{status}] {name}  ({dt:.0f} s)  {rows[-1][3]}", flush=True)

    print()
    print("=" * 72)
    npass = sum(1 for r in rows if r[1] == "PASS")
    print(f"VERIFIERS: {npass}/{len(rows)} pass")
    print("OVERALL: " + ("ALL VERIFIERS PASS" if worst == 0 else "FAILURES PRESENT"))
    print("=" * 72)
    return worst


if __name__ == "__main__":
    sys.exit(main())
