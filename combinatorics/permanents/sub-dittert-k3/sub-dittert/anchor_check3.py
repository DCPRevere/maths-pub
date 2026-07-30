"""
Check [3] and the rest of the anchor standard at (k = 4, n), from an H2 witness.

WHAT IS MISSING AND WHY THIS FILE EXISTS.  `verify_pinretest.py` proves an H2
201-pin witness satisfies the 87 SYMMETRY-REDUCED identity rows and that all 21
canonical blocks are positive definite.  `h2_anchor.py` closes the assembled
`B x B` half of check [4] and `h2_anchor6.py` proves the conjugacy (A1)/(A2)
that deduces the other `n^2 - 1` factorisations.  What no file has run at
n >= 6 is the anchor's check [3]: the identity by FULL coefficient comparison
over Q, every monomial, against an F built from the 1992 definition by code
that shares nothing with the pipeline.  Plus [1], [2], [5] and [6], which are
cheap and were never run either.

WHERE THE INDEPENDENCE LIVES, stated precisely.  `results/verify_subdittert.py`
is the trusted standalone verifier: standard library only, no pipeline imports,
and it is the file that certified (5,4).  It is loaded here BY PATH AND NOT
EDITED, and every expectation in this run comes from its functions:

    F           <- vs.build_F(n, k)            the 1992 objective, from scratch
    sigma_k     <- vs.direct_sigma_k / vs.ryser_sigma_k    two algorithms
    LDL         <- vs.ldl_positive_definite    (used only in the n = 5 control)
    bound       <- vs.factorial                2 - k!/n^k

The CLAIM side -- the Gram matrices -- is built from the stored witness with the
pipeline's own orbit and transporter machinery.  That asymmetry is the point:
the claim may use the group, the expectation may not.

THE ONE PLACE A GROUP BUG COULD HIDE, and why it cannot.  `G_p` is built by
relabelling `H` through the transporter rather than read from a dense export of
`n^2` matrices, because at n = 7 that export is over a gigabyte.  This is NOT
the circularity it looks like: a WRONG relabelling produces a wrong `G_p` and
therefore a FAILED identity.  Check [3] is the test of the relabelling, not an
assumption about it.  The relabelling is assumed only for PD of `G_p`, and that
assumption is discharged separately and combinatorially by (A1), which reads no
Gram entry at all.

POSITIVE CONTROL FIRST, and the run refuses to report n >= 6 without it.  At
n = 5 this file's streamed right-hand side is compared, monomial for monomial,
against `vs.certificate_polynomial` applied to the stored 61 MB dense
certificate that the (5,4) anchor was verified from -- the route with no group
theory in it whatsoever.  If the streamed and dense routes disagree, the
streaming is wrong and nothing else in the file means anything.

MEMORY.  The intermediate right-hand side carries degree-TOPDEG monomials that
CANCEL in the final identity, and there are far more of those than of F's own.
At n = 9 that is tens of millions of dictionary entries, so the expansion is
run in passes over a partition of the monomials by leading variable; each pass
holds one part.  Cost multiplies by the number of passes, memory divides by it.
"""

import importlib.util
import json
import os
import sys
import time
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "dittert"))
sys.path.insert(0, HERE)          # HERE must win the name `expand` (see sos.py)
import sos                                                         # noqa: E402
from symmetry import generators, monomials, orbits                 # noqa: E402
import h2_anchor as ha                                             # noqa: E402
import h2_anchor6 as ha6                                           # noqa: E402

K, DEG_BASIS = 4, 2


# ---------------------------------------------------------------------------
# The lean assembler, and why it exists.
#
# `sos.build_sdp` enumerates every monomial of degree <= TOPDEG and builds an
# `orbit_of` dictionary over them, because it has to: those are the constraint
# ROWS of the SDP it was written to solve.  Nothing here solves an SDP.  The
# checks need only the Gram basis, the two pair-orbit structures and lambda's
# orbits -- and the monomial table is the ONLY thing that makes large n
# impossible:
#
#     monomials of degree <= 5 :   n = 7   3,162,510
#                                  n = 8  11,238,513
#                                  n = 9  34,826,302     ~10-14 GB with orbit_of
#
# At (k = 4, n = 9) that table killed the H2 solve outright (EXIT=137, cgroup
# OOM at 6G).  Skipping it is not an approximation: A0, A1, A2, rhs and
# orbit_of are simply never read by any check in this file, by h2_anchor or by
# h2_anchor6.
#
# THE RISK THIS CARRIES, and how it is discharged.  The witness's 440
# coefficients are indexed BY ORBIT POSITION, so a lean build that produced the
# same orbits in a different ORDER would silently certify a permuted point.
# `validate_lean` therefore requires the lean and full builds to agree entry for
# entry -- basis, both orbit lists in order, lambda's orbits, B and TOPDEG -- at
# the n where both fit, and the lean path refuses to run if they do not.
# ---------------------------------------------------------------------------
LEAN_KEYS = ("B", "basis", "g_orbits", "s_orbits", "lam_orbit_reps", "TOPDEG")


def lean_sdp(n, k=K, deg_basis=DEG_BASIS):
    """Exactly the fields the anchor checks read, and nothing that needs the
    degree-TOPDEG monomial table."""
    N = n * n
    basis = monomials(N, deg_basis, mindeg=1)
    TOPDEG = 2 * deg_basis + 1
    gens = generators(n)
    g_orbits = sos.sym_pair_orbits(basis, gens)
    s_orbits = sos.sym_pair_orbits(basis, sos.stab_generators(n, (0, 0)))
    lreps, _ = orbits(monomials(N, TOPDEG - 1), gens)
    return dict(n=n, k=k, deg_basis=deg_basis, B=len(basis), basis=basis,
                g_orbits=g_orbits, s_orbits=s_orbits,
                lam_orbit_reps=[m for _, m in lreps.items()], TOPDEG=TOPDEG)


def validate_lean(ns, out):
    """The lean build must equal the full one, in order, wherever both fit."""
    for n in ns:
        full = sos.build_sdp(n, K, DEG_BASIS, verbose=False)
        lean = lean_sdp(n)
        for key in LEAN_KEYS:
            a, b = full[key], lean[key]
            if key == "basis":
                a = [tuple(m) for m in a]
                b = [tuple(m) for m in b]
            if a != b:
                out(f"  LEAN VALIDATION FAILED at n = {n}: {key} differs")
                return False
        out(f"  lean build agrees with sos.build_sdp at (k = {K}, n = {n}) on "
            f"all of {', '.join(LEAN_KEYS)} -- same objects, same ORDER")
    return True

# ---------------------------------------------------------------------------
# Independent expectations.  These are TYPED IN from NOTES.md §6.1a and from
# results/h2anchor_n{5,6}.log -- they are not recomputed here, so a change in
# the pipeline cannot move them.  Verifier and claim must not share a source.
# ---------------------------------------------------------------------------
EXPECT_B = {5: 350, 6: 702, 7: 1274, 8: 2144, 9: 3402}
EXPECT_BOUND = {5: "1226/625", 6: "107/54", 7: "4778/2401",
                8: "1021/512", 9: "4366/2187"}
EXPECT_F_MONOMIALS = {5: 7875}          # NOTES §6.1a check [3], (5,4) anchor
EXPECT_LAM_COEFFS = {5: 23751}          # NOTES §6b.44, the (5,4) anchor's count
CONTROL_N = 5
CONTROL_CERT = os.path.join(HERE, "results",
                            "subdittert_n5k4d2_certificate.json")


def load_trusted():
    """Load results/verify_subdittert.py by path, unmodified, as a module."""
    path = os.path.join(HERE, "results", "verify_subdittert.py")
    spec = importlib.util.spec_from_file_location("trusted_vs", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    for name in ("build_F", "direct_sigma_k", "ryser_sigma_k",
                 "ldl_positive_definite", "certificate_polynomial",
                 "factorial", "binom"):
        if not hasattr(mod, name):
            raise SystemExit(f"the trusted verifier has no {name}")
    return mod


# ------------------------------------------------------------ the claim side
def build_claim(n, out, witness=None, d=None):
    """G0, H, lam and the basis, from the stored witness."""
    t0 = time.time()
    d = d if d is not None else sos.build_sdp(n, K, DEG_BASIS, verbose=False)
    B, N = d["B"], n * n
    if B != EXPECT_B.get(n):
        raise SystemExit(f"B = {B}, expected {EXPECT_B.get(n)} at n = {n}")
    w, doc = ha.load_point(n, witness)
    ng, ns = len(d["g_orbits"]), len(d["s_orbits"])
    nl = len(d["lam_orbit_reps"])
    if ng + ns + nl != len(w):
        raise SystemExit(f"witness has {len(w)} entries, expected "
                         f"{ng + ns + nl}")
    G0 = ha.assemble(B, d["g_orbits"], w[:ng])
    H = ha.assemble(B, d["s_orbits"], w[ng:ng + ns])

    lam_mons = monomials(N, d["TOPDEG"] - 1)
    lam = {}
    for vi, members in enumerate(d["lam_orbit_reps"]):
        co = w[ng + ns + vi]
        if not co:
            continue
        for t in members:
            key = tuple(lam_mons[t])
            lam[key] = lam.get(key, F(0)) + co
    lam = {m: c for m, c in lam.items() if c}
    out(f"  claim built from {doc.get('kind')} witness: B = {B}, "
        f"orbit split {ng} + {ns} + {nl}, {len(lam)} nonzero lambda "
        f"coefficients  ({time.time() - t0:.0f} s)")
    if n in EXPECT_LAM_COEFFS and len(lam) != EXPECT_LAM_COEFFS[n]:
        out(f"  NOTE lambda coefficient count {len(lam)} against the recorded "
            f"{EXPECT_LAM_COEFFS[n]} (zeros are dropped here)")
    return d, G0, H, lam


# ------------------------------------------------- the expansion, in passes
def part_of(m, passes):
    """Which pass owns monomial `m`.  The constant monomial belongs to pass 0."""
    return (m[0] % passes) if m else 0


def expand_part(n, d, G0, H, lam, perms, part, passes):
    """
    One part of the certificate's right-hand side, exactly.

    Mirrors `vs.certificate_polynomial` term for term -- sigma_0, then each
    multiplier with its `1/n + b_p` factor, then lambda times `sum_q b_q` --
    except that `G_p` is streamed through the transporter permutation instead
    of being materialised, and that only the monomials belonging to `part` are
    retained.  The partition is on the LEADING variable, decided before the
    coefficient is stored, so the parts we are not building cost only the
    modulo.

    Retaining a part is sound because the identity is checked coefficient by
    coefficient: no term of one part can cancel a term of another.
    """
    B, N = d["B"], n * n
    basis = [tuple(m) for m in d["basis"]]
    inv = F(1, n)
    rhs = {}
    one = passes == 1
    get = rhs.get

    def add(m, c):
        if not one and part_of(m, passes) != part:
            return
        v = get(m, None)
        v = c if v is None else v + c
        if v:
            rhs[m] = v
        else:
            rhs.pop(m, None)

    # sigma_0(b) = sum_uv G0[u][v] m_u m_v
    for u in range(B):
        bu, G0u = basis[u], G0[u]
        for v in range(B):
            c = G0u[v]
            if c:
                add(tuple(sorted(bu + basis[v])), c)

    # sum_p (1/n + b_p) sigma_p(b),  with G_p[pi[u]][pi[v]] = H[u][v]
    for p in range(N):
        pi = perms[p]
        for u in range(B):
            Hu = H[u]
            bpu = basis[pi[u]]
            for v in range(B):
                c = Hu[v]
                if not c:
                    continue
                base = tuple(sorted(bpu + basis[pi[v]]))
                add(base, c * inv)
                add(tuple(sorted(base + (p,))), c)

    # lambda(b) * sum_q b_q
    for mono, c in lam.items():
        for q in range(N):
            add(tuple(sorted(mono + (q,))), c)

    return rhs


def identity_holds(n, d, G0, H, lam, perms, Fclean, passes, out,
                   label="[3]", quiet=False):
    """
    FULL coefficient comparison over Q, part by part, freeing each part.

    Returns (ok, total_certificate_monomials).  Every monomial of F and every
    monomial the certificate produces is compared -- the partition changes the
    ORDER of the comparison and its peak memory, never its extent.
    """
    t0 = time.time()
    Fpart = {}
    for m, c in Fclean.items():
        Fpart.setdefault(part_of(m, passes), {})[m] = c
    total, allbad = 0, []
    for part in range(passes):
        rhs = expand_part(n, d, G0, H, lam, perms, part, passes)
        total += len(rhs)
        fp = Fpart.get(part, {})
        bad = [m for m in set(rhs) | set(fp)
               if rhs.get(m, F(0)) != fp.get(m, F(0))]
        allbad.extend(bad[:3])
        if not quiet:
            out(f"      part {part + 1}/{passes}: {len(rhs):,} certificate "
                f"monomials, {len(fp):,} of F, "
                f"{'match' if not bad else f'{len(bad)} DIFFER'}"
                f"  ({time.time() - t0:.0f} s)")
        del rhs
        if bad and quiet:
            return False, total
    ok = not allbad
    if not quiet:
        out(f"  {label} identity by FULL coefficient comparison over Q: "
            f"certificate {total:,} monomials, F {len(Fclean):,} monomials -> "
            f"{'IDENTICAL' if ok else '*** MISMATCH ***'}")
        if allbad:
            out(f"      differing monomials include {allbad[:3]}")
    return ok, total


# ---------------------------------------------------------- the n = 5 control
def control(vs, out):
    """
    The streamed expansion against the dense, group-free one at (k = 4, n = 5).

    This is the check that catches the streaming being wrong.  The dense route
    is `vs.certificate_polynomial` on the stored 61 MB certificate the (5,4)
    anchor was verified from; it never sees a transporter.
    """
    out(f"\n=== POSITIVE CONTROL at (k = 4, n = {CONTROL_N}) ===")
    if not os.path.exists(CONTROL_CERT):
        out(f"  MISSING {CONTROL_CERT} -- the control cannot run")
        return False
    t0 = time.time()
    with open(CONTROL_CERT) as fh:
        raw = json.load(fh)
    cert = dict(n=raw["n"], k=raw["k"], N=raw["N"], M=F(raw["bound_M"]))
    cert["basis"] = [tuple(m) for m in raw["basis"]]
    cert["G0"] = [[F(x) for x in row] for row in raw["G0"]]
    cert["Gp"] = [[[F(x) for x in row] for row in Mx] for Mx in raw["Gp"]]
    lam = {}
    for key, val in raw["lam"].items():
        mono = tuple(int(t) for t in key.split(",")) if key else ()
        lam[mono] = F(val)
    cert["lam"] = lam
    out(f"  dense (5,4) certificate loaded, {len(cert['Gp'])} multiplier "
        f"Grams of size {len(cert['G0'])}  ({time.time() - t0:.0f} s)")

    t1 = time.time()
    dense = vs.certificate_polynomial(cert)
    out(f"  dense route (no group theory): {len(dense):,} monomials "
        f"({time.time() - t1:.0f} s)")

    ok_a1, payload = ha6.check_conjugations(CONTROL_N, out=out)
    if not ok_a1:
        out("  CONTROL ABORTED: (A1)/(A2) failed at the control n")
        return False
    d, H, perms = payload
    d2, G0, H2, lam2 = build_claim(CONTROL_N, out)
    if H2 != H:
        out("  CONTROL FAILED: the two assemblies of H disagree")
        return False
    t2 = time.time()
    streamed = expand_part(CONTROL_N, d2, G0, H2, lam2, perms, 0, 1)
    out(f"  streamed route (transporter relabelling): {len(streamed):,} "
        f"monomials ({time.time() - t2:.0f} s)")

    if streamed != dense:
        keys = set(streamed) | set(dense)
        bad = [m for m in keys
               if streamed.get(m, F(0)) != dense.get(m, F(0))]
        out(f"  CONTROL FAILED: {len(bad)} monomials differ between the "
            f"streamed and dense routes, e.g. {bad[:3]}")
        return False
    out("  CONTROL PASSED: streamed and dense expansions are IDENTICAL over Q")

    # and the streamed route must reproduce the anchor's own recorded [3]
    Fpoly, M, _ = vs.build_F(CONTROL_N, K)
    Fclean = {m: c for m, c in Fpoly.items() if c}
    if len(Fclean) != EXPECT_F_MONOMIALS[CONTROL_N]:
        out(f"  CONTROL FAILED: F has {len(Fclean)} monomials, NOTES §6.1a "
            f"records {EXPECT_F_MONOMIALS[CONTROL_N]}")
        return False
    if streamed != Fclean:
        out("  CONTROL FAILED: the streamed identity does not hold at n = 5, "
            "where the anchor says it does")
        return False
    out(f"  CONTROL PASSED: identity holds at (k = 4, n = 5) over all "
        f"{len(Fclean)} monomials, the count NOTES §6.1a records")

    # a control that never rejects proves nothing: perturb and require failure
    G0m = [row[:] for row in G0]
    G0m[0][0] += F(1, 10 ** 6)
    mutated = expand_part(CONTROL_N, d2, G0m, H2, lam2, perms, 0, 1)
    if mutated == Fclean:
        out("  CONTROL FAILED: a perturbed G0 still satisfies the identity")
        return False
    out("  control rejected (G0[0][0] shifted by 1e-6): identity broken, "
        "as required")

    # the partitioned route must reach the same verdict as the whole-dict one,
    # or the partition is silently testing less than it prints
    okp, totp = identity_holds(CONTROL_N, d2, G0, H2, lam2, perms, Fclean,
                               3, out, quiet=True)
    if not okp or totp != len(streamed):
        out(f"  CONTROL FAILED: the 3-part route gave ok={okp}, "
            f"{totp} monomials against {len(streamed)} whole")
        return False
    out(f"  CONTROL PASSED: the 3-part partition reproduces the same "
        f"{totp} monomials and the same verdict")
    return True


# --------------------------------------------------------------- the anchor run
def run(n, vs, out=print, passes=1, witness=None, lean=False):
    out(f"\n=== (k = {K}, n = {n}) anchor checks [1] [2] [3] [5] [6] ==="
        + ("   [lean assembler]" if lean else ""))
    ok = {}
    dbuilt = lean_sdp(n) if lean else None

    # ---- [2] the bound
    Mexp = F(2) - F(vs.factorial(K), n ** K)
    typed = F(EXPECT_BOUND[n])
    ok["[2] bound"] = (Mexp == typed)
    out(f"  [2] bound 2 - {K}!/{n}^{K} = {Mexp} against the typed-in "
        f"{typed}: {'MATCH' if Mexp == typed else 'MISMATCH'}")

    # ---- [1] sigma_k by two structurally different algorithms
    t0 = time.time()
    trials = [
        [[F(i * 3 + j * 5 + 1, 7) for j in range(n)] for i in range(n)],
        [[F(1, n) for _ in range(n)] for _ in range(n)],
        [[F((i + 1) * (j + 2), 11) for j in range(n)] for i in range(n)],
        [[F(1 if i == j else 0) for j in range(n)] for i in range(n)],
    ]
    agree = all(vs.direct_sigma_k(A, n, K) == vs.ryser_sigma_k(A, n, K)
                for A in trials)
    ok["[1] sigma_k two algorithms"] = agree
    out(f"  [1] sigma_k, direct subpermanents vs Ryser on per(A+xJ), "
        f"{len(trials)} matrices: {'AGREE' if agree else 'DISAGREE'} "
        f"({time.time() - t0:.0f} s)")

    # ---- (A1)/(A2): the conjugacy that makes the streamed G_p legitimate
    ok_conj, payload = ha6.check_conjugations(n, out=out, d=dbuilt)
    ok["(A1)/(A2) conjugacy"] = ok_conj
    if not ok_conj:
        out("  ABORT: without (A1) the multiplier Grams are not permutation "
            "conjugates and nothing below is meaningful")
        return ok
    d, H, perms = payload
    d2, G0, H2, lam = build_claim(n, out, witness, d=dbuilt)
    if H2 != H:
        out("  ABORT: the two assemblies of H disagree")
        ok["H assembly agrees"] = False
        return ok

    # ---- [3] the identity
    t0 = time.time()
    out(f"  [3] building F(b) from the 1992 definition (trusted verifier)")
    Fpoly, M2, _ = vs.build_F(n, K)
    if M2 != Mexp:
        out("  ABORT: the trusted F's bound disagrees with 2 - k!/n^k")
        ok["[3] identity"] = False
        return ok
    Fclean = {m: c for m, c in Fpoly.items() if c}
    out(f"      F built: {len(Fclean):,} monomials "
        f"({time.time() - t0:.0f} s)")
    if n in EXPECT_F_MONOMIALS and len(Fclean) != EXPECT_F_MONOMIALS[n]:
        out(f"  ABORT: F has {len(Fclean)} monomials, the typed-in "
            f"expectation is {EXPECT_F_MONOMIALS[n]}")
        ok["[3] identity"] = False
        return ok
    t1 = time.time()
    good, total = identity_holds(n, d2, G0, H2, lam, perms, Fclean,
                                 passes, out)
    ok["[3] identity"] = good
    out(f"      certificate expanded and compared in {time.time() - t1:.0f} s"
        + (f" over {passes} parts" if passes > 1 else ""))

    # ---- [6] F(0) = 0 and the certificate vanishes at b = 0
    # The certificate cannot carry a constant term: the Gram basis EXCLUDES the
    # constant monomial, so every m_u m_v has degree >= 2, and lambda's term
    # carries a factor b_q.  That is structural, so it is asserted on the basis
    # rather than read off an expansion.
    noconstF = Fpoly.get((), F(0)) == 0
    nobasis0 = all(1 <= len(tuple(m)) <= DEG_BASIS for m in d2["basis"])
    ok["[6] F(0) = 0"] = noconstF and nobasis0
    out(f"  [6] F(0) = 0: F constant term {Fpoly.get((), F(0))}; constant "
        f"monomial excluded from all {len(d2['basis'])} Gram basis entries: "
        f"{nobasis0}")

    # ---- [5] mutation tests
    out(f"  [5] mutation tests (each must BREAK the identity)")
    G0m = [row[:] for row in G0]
    G0m[0][0] += F(1, 10 ** 6)
    Hm = [row[:] for row in H2]
    Hm[0][0] += F(1, 10 ** 6)
    lamm = dict(lam)
    kk = sorted(lamm)[0]
    lamm[kk] = lamm[kk] + F(1, 10 ** 6)
    muts = [
        ("G0[0][0] shifted by 1e-6", G0m, H2, lam),
        ("H[0][0] shifted by 1e-6 (moves all n^2 multipliers)", G0, Hm, lam),
        (f"lambda coefficient at {kk} shifted by 1e-6", G0, H2, lamm),
    ]
    rejected = 0
    for label, g, h, lm in muts:
        mok, _ = identity_holds(n, d2, g, h, lm, perms, Fclean, passes, out,
                                quiet=True)
        if mok:
            out(f"      *** NOT REJECTED: {label} left the identity intact")
        else:
            rejected += 1
            out(f"      control rejected ({label})")
    ok["[5] mutations"] = (rejected == len(muts))
    out(f"      {rejected} of {len(muts)} mutation controls correctly rejected")

    return ok


def main(argv):
    ns = [int(a) for a in argv if a.isdigit()]
    passes = 1
    for a in argv:
        if a.startswith("--passes="):
            passes = int(a.split("=")[1])
    skip_control = "--no-control" in argv
    lean = "--lean" in argv

    vs = load_trusted()
    print("trusted verifier results/verify_subdittert.py loaded by path, "
          "unmodified", flush=True)

    if lean:
        print("\n=== LEAN ASSEMBLER VALIDATION (against sos.build_sdp) ===",
              flush=True)
        if not validate_lean([5, 6], out=lambda s: print(s, flush=True)):
            raise SystemExit("LEAN VALIDATION FAILED -- refusing to use it")

    if not skip_control:
        if not control(vs, out=lambda s: print(s, flush=True)):
            raise SystemExit("POSITIVE CONTROL FAILED -- refusing to report "
                             "any other n")
    else:
        print("\n*** control SKIPPED by flag: results below are not reportable",
              flush=True)

    verdicts = {}
    for n in ns or [6]:
        verdicts[n] = run(n, vs, out=lambda s: print(s, flush=True),
                          passes=passes, lean=lean)

    print("\n" + "=" * 70, flush=True)
    for n, ok in verdicts.items():
        bad = [key for key, v in ok.items() if not v]
        print(f"(k = {K}, n = {n}): "
              + ("ALL CHECKS PASS" if not bad else f"FAILED {bad}"),
              flush=True)
        for key, v in ok.items():
            print(f"    {'PASS' if v else 'FAIL'}  {key}", flush=True)


if __name__ == "__main__":
    main(sys.argv[1:])
