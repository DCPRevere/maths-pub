"""
Is check [4]'s n-uniform fact even TRUE?  The separating experiment.

THE QUESTION.  Check [4] asks whether positive definiteness of the 21 canonical
blocks implies it for the assembled `B x B` Gram.  §6b.39 asserts this by
MULTIPLICITY COUNTING; §9.5 records that the block-diagonalisation is not
formalised as an equivalence; `verify_pinretest.basis_full_rank` proves only the
converse, `H > 0 => E^T H E > 0`, and says so in its own docstring.  If the
forward direction is true it is true at every n at once, and three long exact
factorisations become unnecessary.  If it is false, those factorisations are
permanently necessary.  Either way this is a last result.

WHY THE COUNT THAT ALREADY PASSES TELLS US NOTHING -- the point of this file.
The identity `sum(multiplicity x dimension) = B` is verified exactly at
n = 5..9 (1274, 2144, 3402 out of sample, §6b.15/§6b.31).  That identity says the
decomposition is COMPLETE BY DIMENSION.  It is silent on whether the canonical
bases are isotypic-ADAPTED -- whether `E_b^T H E_b` is the Schur-lemma
multiplicity matrix or merely some full-rank compression of H.  A decomposition
can be complete by dimension and not H-orthogonal.  So the dimension count is a
SATURATED INSTRUMENT here: it passes either way, and reading support from it is
the error.  The separating instruments are the two below.

  THE TEST: the group translates of the `E_b` span everything (`W` invertible
        over Q) and distinct components are exactly H-ORTHOGONAL
        (`S_b^T H S_c = 0` over Q for b != c).  That orthogonality is the
        content; Schur forces it when the components are correctly identified,
        and a single nonzero entry refutes the fact outright.

A SCREEN I WROTE, RAN, AND WITHDREW -- recorded because the reasoning is the
trap.  The obvious cheap screen is "spec(Gram) must equal the union of the block
spectra, each with multiplicity `e_b`".  It ran in seconds and appeared to REFUTE
the fact at (k = 4, n = 5), with 0 of 350 eigenvalues accounted for on
`sigma_11`.  That verdict is VOID and the premise is false: the canonical basis
vectors are integer vectors, nowhere near orthonormal (the run measures the
largest norm and prints it), so `E_b^T H E_b` is a CONGRUENCE and not a
compression onto an orthonormal basis.  Eigenvalues are not congruence-invariant.  The proof that the
screen is wrong rather than the fact:

    H's largest eigenvalue at (k = 4, n = 5)          9.0550e+01
    the 16x16 Ind(V'|1) block's largest eigenvalue    1.4554e+05

A block eigenvalue LARGER than the whole Gram's is impossible for any spectral
restriction, so the map cannot be one.  What congruence does preserve is INERTIA
(Sylvester), and on a Gram we already know is positive definite with all blocks
positive definite, inertia is vacuous -- every count is "all positive" on both
sides.  So there is no cheap spectral screen here at all; H-orthogonality, which
IS congruence-stable, is the only instrument.  A refutation from a script whose
premise was never checked would have been the worse outcome of the two.

SCOPE.  Experiment only.  This file reports a verdict and stops.  It does not
attempt the written proof.

The two sides carry DIFFERENT groups and it matters: `sigma_0`'s blocks are
adapted to the whole of `G = (S_n x S_n) : Z_2`, `sigma_11`'s to `Stab((0,0))`.
The closure in PART 1 uses each side's own generators.
"""

import os
import sys
import time
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "dittert"))
sys.path.insert(0, HERE)
import numpy as np                                                  # noqa: E402
import sos                                                          # noqa: E402
import k4_pinretest as pr                                           # noqa: E402
import k4_sigma0 as s0                                              # noqa: E402
import k4_vv14 as vv                                                # noqa: E402
import h2_anchor as ha                                              # noqa: E402
import anchor_check3 as ac                                          # noqa: E402

K, DEG_BASIS = 4, 2
PRIME = (1 << 61) - 1                     # rank search only; verdicts are exact


def header(out):
    out("=" * 74)
    out("SEPARATING EXPERIMENT for check [4]'s n-uniform fact")
    out("=" * 74)
    out("The identity sum(multiplicity x dimension) = B is ALREADY verified")
    out("exactly at n = 5..9.  It is a SATURATED INSTRUMENT for this question:")
    out("it passes whether or not the canonical bases are isotypic-adapted, so")
    out("no support for the fact may be read from it.  The separating")
    out("instrument is EXACT H-ORTHOGONALITY of distinct components, over Q.")
    out("")
    out("A spectral screen was written, run, and WITHDRAWN: the canonical bases")
    out("are NOT orthonormal, so E^T H E is a CONGRUENCE and eigenvalues are")
    out("not preserved.  Its apparent refutation was an artefact.  Congruence")
    out("preserves INERTIA, vacuous on a positive definite example.  The")
    out("figures are MEASURED below rather than quoted here, so they cannot")
    out("drift from the prose.  See the docstring.")
    out("=" * 74)


def sides(n, basis, lean):
    """(label, group generators, canonical blocks, orbit list, offset) per side."""
    ng = len(lean["g_orbits"])
    return (("sigma_11", sos.stab_generators(n, (0, 0)),
             pr.canonical_blocks(n, basis), lean["s_orbits"], ng),
            ("sigma_0", sos.generators(n),
             s0.canonical_blocks(n, basis), lean["g_orbits"], 0))


def contract(N, dd, w, off):
    return [[sum(x * w[off + c] for c, x in N[s][t].items())
             for t in range(dd)] for s in range(dd)]


# ------------------------------------------------------------------- PART 0
def _withdrawn_part0(n, out):  # kept for the record; NOT called -- premise false
    """Spectrum match.  Floats, and a screen rather than a verdict."""
    out(f"\n--- PART 0 (screen, floats): spec(Gram) vs union of block spectra, "
        f"(k = {K}, n = {n}) ---")
    lean = ac.lean_sdp(n)
    B, basis = lean["B"], lean["basis"]
    w, doc = ha.load_point(n)
    ng, ns = len(lean["g_orbits"]), len(lean["s_orbits"])
    grams = {"sigma_11": ha.assemble(B, lean["s_orbits"], w[ng:ng + ns]),
             "sigma_0": ha.assemble(B, lean["g_orbits"], w[:ng])}
    verdicts = {}
    for label, gens, blocks, orbs, off in sides(n, basis, lean):
        G = grams[label]
        A = np.array([[float(x) for x in row] for row in G])
        specG = np.sort(np.linalg.eigvalsh(A))
        cls = pr.orbit_class_array(n, basis, orbs)
        pool = list(specG)
        total, rows, ok = 0, [], True
        for name, E in blocks:
            dd = len(E)
            N = vv.block_by_class(E, cls, B)
            hb = contract(N, dd, w, off)
            ev = np.sort(np.linalg.eigvalsh(
                np.array([[float(x) for x in r] for r in hb])))
            # how many times does this block's whole spectrum sit in spec(G)?
            tol = 1e-7 * max(1.0, float(np.abs(specG).max()))
            reps = 0
            while True:
                idx = []
                rem = list(pool)
                good = True
                for lam in ev:
                    hit = min(range(len(rem)),
                              key=lambda i: abs(rem[i] - lam)) if rem else None
                    if hit is None or abs(rem[hit] - lam) > tol:
                        good = False
                        break
                    idx.append(rem.pop(hit))
                if not good:
                    break
                pool = rem
                reps += 1
            rows.append((name, dd, reps, dd * reps))
            total += dd * reps
            if reps == 0:
                ok = False
        out(f"  {label}: Gram {B}x{B}, {len(blocks)} blocks")
        for name, dd, reps, prod in rows:
            out(f"    {name:26s} size {dd:3d}  spectrum found {reps:4d}x  "
                f"-> {prod:5d}")
        out(f"    accounted {total} of B = {B}; "
            f"{len(pool)} eigenvalues left over")
        good = ok and total == B and not pool
        out(f"    ==> {label}: spectrum {'MATCHES' if good else 'DOES NOT MATCH'}"
            f" the union of block spectra")
        verdicts[label] = good
    return all(verdicts.values()), verdicts


# ------------------------------------------------------------------- PART 1
def vecs_of(E, B):
    """Each canonical basis element as a dense integer vector of length B."""
    out = []
    for e in E:
        v = [0] * B
        for u, c in e.items():
            v[u] = int(c)
        out.append(v)
    return out


def induced_perm(basis, index, g):
    out = []
    for mono in basis:
        j = index.get(tuple(sorted(g[v] for v in mono)))
        if j is None:
            return None
        out.append(j)
    return out


def close_component(seed, perms, B, out, cap=4000):
    """
    Span of the group orbit of `seed`, as a list of independent vectors.

    Independence is decided MOD A LARGE PRIME -- this only SELECTS which
    translates to keep, and PART 1's verdicts are all recomputed over Q on the
    selected set.  A mod-p rank can only be <= the rational rank, so a vector
    kept here is genuinely independent; one skipped could in principle have been
    independent, which would make the component SMALLER than reported and is
    caught by the `sum dim = B` check.
    """
    rows, piv = [], {}                      # reduced rows mod p, pivot -> row
    kept = []

    def reduce_in(vec):
        r = [x % PRIME for x in vec]
        for c, pr_ in piv.items():
            if r[c]:
                f = r[c] * pow(pr_[c], PRIME - 2, PRIME) % PRIME
                if f:
                    r = [(a - f * b) % PRIME for a, b in zip(r, pr_)]
        c = next((i for i, x in enumerate(r) if x), None)
        if c is None:
            return False
        piv[c] = r
        return True

    frontier = []
    for v in seed:
        if reduce_in(v):
            kept.append(v)
            frontier.append(v)
    while frontier and len(kept) < cap:
        nxt = []
        for v in frontier:
            for p in perms:
                gv = [0] * B
                for i, x in enumerate(v):
                    if x:
                        gv[p[i]] = x
                if reduce_in(gv):
                    kept.append(gv)
                    nxt.append(gv)
                    if len(kept) >= cap:
                        break
            if len(kept) >= cap:
                break
        frontier = nxt
    return kept


def part1(n, out):
    out(f"\n--- PART 1 (exact over Q): span and H-orthogonality, "
        f"(k = {K}, n = {n}) ---")
    t0 = time.time()
    lean = ac.lean_sdp(n)
    B, basis = lean["B"], lean["basis"]
    index = {tuple(m): i for i, m in enumerate(basis)}
    w, doc = ha.load_point(n)
    ng, ns = len(lean["g_orbits"]), len(lean["s_orbits"])
    grams = {"sigma_11": ha.assemble(B, lean["s_orbits"], w[ng:ng + ns]),
             "sigma_0": ha.assemble(B, lean["g_orbits"], w[:ng])}
    allok = True
    for label, gens, blocks, orbs, off in sides(n, basis, lean):
        G = grams[label]
        perms = [p for p in (induced_perm(basis, index, g) for g in gens)
                 if p is not None]
        out(f"  {label}: {len(perms)} generator actions on the {B} basis "
            f"monomials")
        comps, total = [], 0
        for name, E in blocks:
            S = close_component(vecs_of(E, B), perms, B, out)
            comps.append((name, len(E), S))
            total += len(S)
            out(f"    {name:26s} block size {len(E):3d} -> component dim "
                f"{len(S):5d}")
        out(f"    total {total} against B = {B}  "
            f"{'OK' if total == B else '*** MISMATCH ***'}")
        if total != B:
            out(f"    ==> {label}: the translates do NOT span; the "
                f"decomposition as built is INCOMPLETE")
            allok = False
            continue

        # cross-component H-orthogonality, exactly over Q -- the content.
        #
        # `G a` is computed ONCE per vector and reused across every later
        # component, instead of once per (component pair, vector).  That is pure
        # loop-invariant motion -- `G` and `Si` do not depend on `j` -- and the
        # earlier version's recomputation was most of PART 1's cost.
        #
        # A restructured loop is exactly where a verifier starts silently
        # testing less than it prints, so the number of products is COUNTED and
        # asserted against the closed form `(B^2 - sum |S_i|^2) / 2`.  A verdict
        # is refused if the count does not match.
        expected = (B * B - sum(len(c[2]) ** 2 for c in comps)) // 2
        out(f"    checking {expected:,} inner products for exact zero, over "
            f"all {len(comps) * (len(comps) - 1) // 2} pairs of distinct "
            f"components")
        done, bad, t1 = 0, [], time.time()
        for i in range(len(comps)):
            Si = comps[i][2]
            GS = [[sum(G[u][v] * a[u] for u in range(B) if a[u])
                   for v in range(B)] for a in Si]
            for j in range(i + 1, len(comps)):
                Sj = comps[j][2]
                for Ga in GS:
                    for b in Sj:
                        done += 1
                        val = sum(Ga[v] * b[v] for v in range(B) if b[v])
                        if val:
                            bad.append((comps[i][0], comps[j][0], val))
                            break
                    if bad:
                        break
                if bad:
                    break
            del GS
            if bad:
                break
            out(f"      component {i + 1}/{len(comps)} "
                f"({comps[i][0].strip()}): {done:,} of {expected:,} products, "
                f"{time.time() - t1:.0f} s elapsed")
        if not bad and done != expected:
            out(f"    *** COVERAGE FAULT: {done:,} products checked against "
                f"{expected:,} expected -- refusing to report a verdict")
            allok = False
            continue
        if bad:
            out(f"    ==> {label}: components are NOT H-orthogonal, e.g. "
                f"{bad[0][0]} vs {bad[0][1]} gives {bad[0][2]}")
            out(f"        the canonical bases are NOT isotypic-adapted, so "
                f"block PD does NOT imply Gram PD by this route")
            allok = False
        else:
            out(f"    ==> {label}: all distinct components are EXACTLY "
                f"H-orthogonal over Q, and the translates span")
    out(f"  PART 1 finished in {time.time() - t0:.0f} s")
    return allok


def congruence_note(n, out):
    """
    Show, at this n, WHY there is no spectral screen -- so the withdrawal is
    checkable rather than asserted.
    """
    lean = ac.lean_sdp(n)
    B, basis = lean["B"], lean["basis"]
    w, _ = ha.load_point(n)
    ng, ns = len(lean["g_orbits"]), len(lean["s_orbits"])
    H = ha.assemble(B, lean["s_orbits"], w[ng:ng + ns])
    top = float(np.linalg.eigvalsh(
        np.array([[float(x) for x in r] for r in H])).max())
    cls = pr.orbit_class_array(n, basis, lean["s_orbits"])
    worst, wname, nrm = 0.0, None, 0.0
    for name, E in pr.canonical_blocks(n, basis):
        N = vv.block_by_class(E, cls, B)
        hb = contract(N, len(E), w, ng)
        e = float(np.linalg.eigvalsh(
            np.array([[float(x) for x in r] for r in hb])).max())
        nrm = max(nrm, max(float(sum(c * c for c in v.values())) ** 0.5
                           for v in E))
        if e > worst:
            worst, wname = e, name
    out(f"\n--- why there is no spectral screen, at (k = {K}, n = {n}) ---")
    out(f"  Gram sigma_11 largest eigenvalue        {top:.4e}")
    out(f"  largest block eigenvalue ({wname})  {worst:.4e}")
    out(f"  largest canonical basis vector norm    {nrm:.3f}  (not orthonormal)")
    out(f"  block eigenvalue exceeds the Gram's by {worst / top:.1f}x, so "
        f"E^T H E is a CONGRUENCE;")
    out(f"  eigenvalues are not preserved and only INERTIA is, which is vacuous "
        f"here.")
    return worst > top


def main(argv):
    ns = [int(a) for a in argv if a.isdigit()] or [5]
    out = lambda s: print(s, flush=True)                       # noqa: E731
    header(out)
    for n in ns:
        if not congruence_note(n, out):
            out("  NOTE: the congruence demonstration did NOT reproduce at this "
                "n; the withdrawal of the spectral screen rests on n = 5.")
        if "--note-only" in argv:
            continue
        ok = True
        if "--part2-only" not in argv:
            ok = part1(n, out)
        if ok and "--part1-only" not in argv:
            ok = part2(n, out) and ok
        out(f"\n==> (k = {K}, n = {n}): {'CONSISTENT WITH' if ok else 'REFUTES'}"
            f" the n-uniform fact for check [4]")
        if not ok:
            return 1
    return 0




# ------------------------------------------------------------------- PART 2
#
# The SECOND half of the authorised test: "each h_b repeated dim times".
#
# PART 1 proves the components span and are pairwise H-orthogonal, so H is
# congruent to the direct sum of the COMPONENT Grams `S_b^T H S_b`, of size
# dim(component b).  That is not yet the fact: the canonical block `h_b` has size
# d_b, far smaller, and its positive definiteness does not follow.  What is
# missing is that H restricted to a component is `h_b` tensored with an identity.
#
# BASIS-FREE FORM, which is what makes it testable.  If `E_b` spans a
# multiplicity slice `{v} (x) M_b`, then `g E_b` spans `{gv} (x) M_b` and
#
#     (g E_b)^T H (g' E_b)  =  <gv, g'v>  *  h_b
#
# so EVERY d_b x d_b sub-block of the component Gram, taken between whole
# translated slices, is a rational SCALAR MULTIPLE of `h_b`.  Then
# `S_b^T H S_b = C (x) h_b` with `C` the Gram of the translates, and since C is
# positive definite (the slices were kept only when independent), positive
# definiteness of `h_b` gives it for the whole component -- which, with PART 1,
# is exactly "block PD implies Gram PD".
#
# A single sub-block that is NOT a multiple of h_b refutes the fact.  The slice
# g = identity gives `h_b` itself with scalar 1, which is the built-in self-check
# that the sub-block extraction is wired the right way round.


def slice_closure(E, perms, B, target, out, maxwords=20000):
    """
    Translates of the WHOLE slice `E`, kept when they add full rank d_b.

    Groups by translate, unlike `close_component`, because the structure being
    tested lives between slices and is invisible to a flat vector list.
    Independence is decided mod a large prime; that only SELECTS slices, and
    every reported value is recomputed over Q.
    """
    d = len(E)
    piv = {}

    def reduce_in(vec):
        r = [x % PRIME for x in vec]
        for c, pr_ in piv.items():
            if r[c]:
                f = r[c] * pow(pr_[c], PRIME - 2, PRIME) % PRIME
                if f:
                    r = [(a - f * b) % PRIME for a, b in zip(r, pr_)]
        c = next((i for i, x in enumerate(r) if x), None)
        if c is None:
            return False
        piv[c] = r
        return True

    def take(sl):
        snapshot = dict(piv)
        added = sum(1 for v in sl if reduce_in(v))
        if added == d:
            return True
        piv.clear()
        piv.update(snapshot)
        return False

    ident = list(range(B))
    slices, seen, queue = [], {tuple(ident)}, [ident]
    if take(E):
        slices.append((ident, E))
    words = 0
    while queue and len(piv) < target and words < maxwords:
        cur = queue.pop(0)
        for p in perms:
            comp = [p[cur[i]] for i in range(B)]
            key = tuple(comp)
            if key in seen:
                continue
            seen.add(key)
            queue.append(comp)
            words += 1
            sl = []
            for v in E:
                gv = [0] * B
                for i, x in enumerate(v):
                    if x:
                        gv[comp[i]] = x
                sl.append(gv)
            if take(sl):
                slices.append((comp, sl))
            if len(piv) >= target:
                break
    return slices, len(piv)


def part2(n, out):
    out(f"\n--- PART 2 (exact over Q): is each component Gram  C (x) h_b ?  "
        f"(k = {K}, n = {n}) ---")
    t0 = time.time()
    lean = ac.lean_sdp(n)
    B, basis = lean["B"], lean["basis"]
    index = {tuple(m): i for i, m in enumerate(basis)}
    w, _ = ha.load_point(n)
    ng, ns = len(lean["g_orbits"]), len(lean["s_orbits"])
    grams = {"sigma_11": ha.assemble(B, lean["s_orbits"], w[ng:ng + ns]),
             "sigma_0": ha.assemble(B, lean["g_orbits"], w[:ng])}
    allok = True
    for label, gens, blocks, orbs, off in sides(n, basis, lean):
        G = grams[label]
        perms = [p for p in (induced_perm(basis, index, g) for g in gens)
                 if p is not None]
        cls = pr.orbit_class_array(n, basis, orbs)
        out(f"  {label}:")
        for name, E in blocks:
            d = len(E)
            hb = contract(vv.block_by_class(E, cls, B), d, w, off)
            vE = vecs_of(E, B)
            full = close_component(vE, perms, B, out)
            slices, rank = slice_closure(vE, perms, B, len(full), out)
            if rank != len(full):
                out(f"    {name:26s} slice closure reached rank {rank} of "
                    f"{len(full)} -- NOT a union of whole slices")
                allok = False
                continue
            # every slice-pair sub-block must be a rational multiple of h_b
            nz = next(((s, t) for s in range(d) for t in range(d) if hb[s][t]),
                      None)
            if nz is None:
                out(f"    {name:26s} h_b is identically zero; skipped")
                continue
            bad, scal = None, []
            for i in range(len(slices)):
                Si = slices[i][1]
                GS = [[sum(G[u][v] * a[u] for u in range(B) if a[u])
                       for v in range(B)] for a in Si]
                for j in range(i, len(slices)):
                    Sj = slices[j][1]
                    M = [[sum(GS[s][v] * Sj[t][v] for v in range(B) if Sj[t][v])
                          for t in range(d)] for s in range(d)]
                    c = F(M[nz[0]][nz[1]], 1) / hb[nz[0]][nz[1]] \
                        if hb[nz[0]][nz[1]] else F(0)
                    if any(M[s][t] != c * hb[s][t]
                           for s in range(d) for t in range(d)):
                        bad = (i, j)
                        break
                    scal.append(c)
                if bad:
                    break
            if bad:
                out(f"    {name:26s} *** sub-block ({bad[0]},{bad[1]}) is NOT a "
                    f"multiple of h_b -- the fact is REFUTED here")
                allok = False
            else:
                out(f"    {name:26s} {len(slices):3d} slices, all "
                    f"{len(scal)} sub-blocks are exact rational multiples of "
                    f"h_b (identity slice gives {scal[0]})")
        out(f"    ==> {label}: "
            f"{'component Grams are C (x) h_b' if allok else 'REFUTED'}")
    out(f"  PART 2 finished in {time.time() - t0:.0f} s")
    return allok


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
