"""
THE DECIDING QUESTION: how the (k = 4) honest column rides on Lemma B's constant.

The slice constant r_i <= 1 - 1/n is now known FALSE on the collar — pincer
constructed an exact violation on the confinement boundary, 1.63x the slice value
at (k = 4, n = 10) and 1.58x at n = 11, from a permutation with one reweighted
row. That configuration is exactly where my sampler never went, which is the
five-times-flagged bias turning into a proven miss rather than a caveat. The
near-slice hypothesis is dead, and this file replaces it with a parametrised
answer.

WRITE  M_z = c * (1 - 1/n)  and vary c.  Three scenarios are reported:
    c = 1                  the slice value.  FALSE on the collar; reference only.
    c = 1.63               the real-geometry floor, i.e. the largest violation
                           actually constructed.  Hypothetical-sharp: a Lemma B
                           collar form could not do better than this.
    c = 2.34 and c = 2.53  pincer's committed collar cap, bracketing.
    c = my own substitute  (1+rho+e)(1+sqrt2 rho) + e sqrt2 rho - 1/n over
                           (1 - 1/n), for comparison.  It is worse than the cap
                           but only modestly at the n that matter: 2.76 at
                           n = 10 against the cap's 2.34-2.53, not the large gap
                           I assumed when I called it a pessimistic placeholder.

WHERE THE CONSTANT ENTERS, and with what power.  Three of my budget lines use a
bound on the row squared norms of z, and only one is linear:
    core4 = t_4 (3/2) M_z / (t_2/2)                    LINEAR in M_z
    y3q, y3l   the Y_3 AM-GM split has delta = sqrt(lam M_z/(2 t_2)), so
               y3q ~ M_z/delta ~ sqrt(M_z) and y3l ~ delta ~ sqrt(M_z)
                                                       SQUARE ROOT in M_z
Everything else is independent of it: the Xinv bound uses V <= 2Q^2(1-1/n) via
M <= Q, not Lemma B; Y_2 uses sum|H| <= (n-1)Q/2; Y_1 uses the operator norm.
So the honest column's exposure is one linear term plus two square-root terms.
The linear term is NOT dominant, though: measured, core4 is 0.379 of the column
at n = 10 and the total Lemma-B exposure 0.488.  About half the column is
insulated from the constant entirely, which is why PART 4's answer comes out the
way it does.

A CORRECTNESS FIX MADE HERE.  My earlier budget used M_c, the bound on the row
norms of B, inside Y_3's terms, where the quantity that actually appears is the
row norm of z.  They are close because b_line is small, but they are not the
same, and the Lemma B question is about z.  This file uses M_z consistently in
all three places.

Usage:  GUARD_MEM=8G GUARD_CPUS=250% GUARD_THREADS=2 ../guard.sh \
            python3 -u graded_lemmaB.py
"""

import sys
from fractions import Fraction as Fr

from graded_y_bounds import collar_consts, sq
from pincer_line import lam_line, line_margin, t_coef, u_max

OUT = []


def log(*a):
    s = " ".join(str(x) for x in a)
    print(s)
    OUT.append(s)


def my_substitute_c(n, k=4):
    """My own crude collar bound on r_i(z), as a multiple of the slice value."""
    c = collar_consts(n, k)
    rho, e = c["rho"], sq(2 * c["um"])
    Mz = ((1 + rho + e) * (1 + sq(Fr(2)) * rho) + e * sq(Fr(2)) * rho
          - Fr(1, n))
    return Mz / (1 - Fr(1, n))


def budget(n, cscale, k=4, cond=False):
    """cscale: M_z = cscale * (1 - 1/n).  Returns (Q total, LINE total, parts)."""
    c = collar_consts(n, k)
    t2, t3, t4 = t_coef(n, k, 2), t_coef(n, k, 3), t_coef(n, k, 4)
    qb, lam = t2 / 2, lam_line(n, k) / 2
    um, Qc, bz, Op = c["um"], c["Q"], c["beta"], c["Op"]
    Mz = cscale * (1 - Fr(1, n))
    core3 = t3 * Fr(2, 3 * n) / qb
    core4 = t4 * (Fr(1, 32) if cond else Fr(3, 2) * Mz) / qb
    xin = (Fr(3 * n - 4, 3) * sq(2 * um) * sq(1 - Fr(1, n))
           * 2 * t3 / t2)
    K3 = t4 * Fr(n - 3) * (2 * bz + Op)
    delta = sq(lam * Mz / (2 * t2))
    y3q = K3 * Mz / (2 * delta) / qb
    y3l = K3 * delta / lam
    marg = line_margin(n, k, True)
    tail = Fr(1) / Fr(marg).limit_denominator(10 ** 9)
    x1 = t3 * Fr((n - 2) ** 2, 2) * sq(Qc) / lam
    y1 = t4 * Fr((n - 2) * (n - 3) ** 2) * Op * sq(um) / lam
    y2 = t4 * Qc * Fr((n - 2) * (n - 3) * (n - 1) + (n - 3) ** 2) / lam
    return (core3 + core4 + xin + y3q, tail + x1 + y1 + y2 + y3l,
            dict(core3=core3, core4=core4, xinv=xin, y3q=y3q, tail=tail,
                 x1=x1, y1=y1, y2=y2, y3l=y3l))


def threshold(cscale, cond=False, nmax=400):
    for n in range(5, nmax):
        cs = cscale(n) if callable(cscale) else Fr(cscale)
        q, l, _ = budget(n, cs, cond=cond)
        if q < 1 and l < 1:
            return n
    return None


def main():
    log("=" * 74)
    log("THE (k = 4) HONEST COLUMN AS A FUNCTION OF LEMMA B's CONSTANT")
    log("=" * 74)
    log("")
    log("PART 0.  GLOBAL, NOT PATCHED: a line-by-line scaling audit.")
    log("  The violation occurs from (k = 3, n = 4) upward at perturbations as")
    log("  small as t = 1/60, so the slice constant is globally unavailable and")
    log("  the re-run must parametrise EVERY line that uses it, not two cells.")
    log("  Audit: recompute every line at c and at 2c and report the ratio.")
    log("  1.000 = independent of the constant, 1.414 = square root, 2.000 =")
    log("  linear.  The c-dependent set must be exactly {core4, y3q, y3l}.")
    log("")
    log("   line   |  ratio at n=10 |  ratio at n=16 | reading")
    _, _, d1 = budget(10, Fr(163, 100))
    _, _, d2 = budget(10, Fr(326, 100))
    _, _, e1 = budget(16, Fr(163, 100))
    _, _, e2 = budget(16, Fr(326, 100))
    dep = set()
    for kk in ("core3", "core4", "xinv", "y3q", "tail", "x1", "y1", "y2",
               "y3l"):
        r10 = d2[kk] / d1[kk] if d1[kk] else Fr(1)
        r16 = e2[kk] / e1[kk] if e1[kk] else Fr(1)
        if r10 != 1:
            dep.add(kk)
        rd = ("linear" if abs(float(r10) - 2) < 1e-9 else
              "sqrt" if abs(float(r10) - 2 ** 0.5) < 1e-6 else
              "independent" if r10 == 1 else "other")
        log(f"   {kk:6s} | {float(r10):14.6f} | {float(r16):14.6f} | {rd}")
    ok = (dep == {"core4", "y3q", "y3l"})
    log("")
    log(f"  c-dependent lines: {sorted(dep)}   expected"
        f" ['core4', 'y3l', 'y3q']   match {ok}")
    assert ok, f"c-dependence is not where it should be: {sorted(dep)}"
    log("")
    log("  TWO FACTS I DO NOT INHERIT, checked rather than assumed:")
    log("  (i) the xinv line contains a factor sqrt(1 - 1/n) that LOOKS like the")
    log("      slice constant but is not: it comes from V <= 2Q(M - Q/n) with")
    log("      M <= Q, and M <= Q is unconditional since M = max_i r_i <=")
    log("      sum_i r_i = Q.  The audit above confirms xinv does not scale")
    log("      with c, so it is correctly left fixed.")
    log("  (ii) the ENTRY bound is a separate fact and I never use its slice")
    log("      form.  My m = 3 line uses the PER-ENTRY bound")
    log("      z_ij >= -(1/n + x_i + y_j), which follows from A >= 0 alone, and")
    log("      carries the Xinv correction through the merge with total")
    log("      coefficient (3n-4)/3.  So the entry-bound question, refuted or")
    log("      not, does not touch this column.")
    log("")
    log("PART 1.  EXPOSURE: what fraction of the honest column rides on M_z,")
    log("         and with what power, at each n.")
    log("  core4 is LINEAR in M_z; y3q and y3l ride on sqrt(M_z); core3, Xinv,")
    log("  tail, X_1, Y_1, Y_2 are independent of it.")
    log("")
    log("   n | Q total | core4 (linear) | y3q (sqrt) | linear share | any-B share")
    for n in (8, 9, 10, 11, 12, 14, 16, 20):
        q, l, d = budget(n, Fr(163, 100))
        lin = d["core4"] / q
        anyb = (d["core4"] + d["y3q"]) / q
        log(f"  {n:2d} | {float(q):7.4f} | {float(d['core4']):14.4f} |"
            f" {float(d['y3q']):10.4f} | {float(lin):12.4f} |"
            f" {float(anyb):11.4f}")
    log("")
    log("  MEASURED, not asserted: at n = 10 the LINEAR share is 0.379 and the")
    log("  total Lemma-B exposure 0.488 -- about a third linear and about half in")
    log("  total, falling to 0.311 and 0.341 by n = 20.  (An earlier draft of")
    log("  this line said 'roughly three quarters', which the table does not")
    log("  support; the numbers above are the numbers.)  So the constant matters")
    log("  to about half the column, not to almost all of it -- which is already")
    log("  a hint at PART 4's answer.")
    log("")
    log("PART 2.  THRESHOLDS AT EACH SCENARIO.")
    log("")
    log("   scenario                              | c        | honest | cond")
    rows = [
        ("slice value (FALSE on the collar)", Fr(1)),
        ("real-geometry floor, low end (n = 11)", Fr(158, 100)),
        ("real-geometry floor, high end (n = 10)", Fr(163, 100)),
        ("pincer collar cap, low end", Fr(234, 100)),
        ("pincer collar cap, high end", Fr(253, 100)),
    ]
    for lab, cs in rows:
        th = threshold(cs)
        tc = threshold(cs, cond=True)
        log(f"   {lab:37s} | {float(cs):8.2f} | {str(th):6s} | {tc}")
    th = threshold(my_substitute_c)
    tc = threshold(my_substitute_c, cond=True)
    log(f"   {'my own crude substitute':37s} | {'varies':>8s} |"
        f" {str(th):6s} | {tc}")
    log("")
    log("  my substitute's c, for comparison with pincer's 2.34-2.53:")
    log("   n  |  c (mine)")
    for n in (8, 10, 11, 12, 16, 20):
        log(f"  {n:2d}  | {float(my_substitute_c(n)):9.4f}")
    log("")
    log("PART 3.  THE TABLE AT PINCER'S CAP AND AT THE FLOOR.")
    log("")
    log("   n | Q (c=1.63 floor) | Q (c=2.34) | Q (c=2.53) | LINE   | 1.63 | 2.53")
    for n in range(9, 21):
        q1, l1, _ = budget(n, Fr(163, 100))
        q2, _, _ = budget(n, Fr(234, 100))
        q3, _, _ = budget(n, Fr(253, 100))
        log(f"  {n:2d} | {float(q1):16.4f} | {float(q2):10.4f} |"
            f" {float(q3):10.4f} | {float(l1):6.4f} |"
            f" {str(q1 < 1 and l1 < 1):4s} | {q3 < 1 and l1 < 1}")
    log("")
    log("PART 4.  WHAT A SHARPER LEMMA B WOULD BUY.")
    log("   c    | honest threshold")
    for cs in (Fr(1), Fr(125, 100), Fr(150, 100), Fr(163, 100), Fr(2),
               Fr(234, 100), Fr(253, 100), Fr(3), Fr(4)):
        log(f"  {float(cs):5.2f} | {threshold(cs)}")
    log("")
    log("  THE ANSWER TO THE DECIDING QUESTION.  The honest threshold is FLAT at")
    log("  n >= 10 across the entire admissible range 1.63 <= c <= 2.53.  Since")
    log("  the real geometry forces c >= 1.63, and my own crude substitute")
    log("  (c = 2.76 at n = 10) already lands on 10, sharpening Lemma B buys")
    log("  NOTHING for the honest column.  Only c <= 1.5 would give 9, and the")
    log("  constructed violation rules that out.")
    log("  BUT IT DOES HELP THE CONDITIONAL COLUMN: 9 with my substitute, 8 with")
    log("  pincer's cap.  The conditional core4 uses the parked eps and so is")
    log("  Lemma-B-free, but y3q and y3l still ride on sqrt(M_z), and at n = 8")
    log("  my substitute's c = 3.41 against the cap's 2.53 is the whole")
    log("  difference.  So the cap is worth one step, on the conditional route")
    log("  only.")
    log("")
    with open("results/graded_lemmaB.log", "w") as fh:
        fh.write("\n".join(OUT) + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
