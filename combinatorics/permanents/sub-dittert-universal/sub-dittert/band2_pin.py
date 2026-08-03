"""
BAND 2: the 2-dimensional quotient made explicit, and the PD test on what it
pins -- which turns out to be nothing.

POSITIVITY.md section 10.5 measured that the four band right-hand sides span only
TWO dimensions of the degree->=4 row space modulo the lambda columns, and
suggested the resulting 2-dimensional subspace "points somewhere".  This file
runs that to its end.

RESULT.  The quotient is confirmed 2-dimensional and its basis is explicit:
rhs_H(2) and rhs_H(3) both lie in span(lambda columns, rhs_H(4), rhs_H(5)).  But
the statement is about the TARGET space, not about the Grams.  On the H rows the
system has rank 75 in 339 columns, so 264 coordinates stay free, and the
canonical representative (free coordinates zero) has 5 nonzero coordinates at
k = 4 and 12 at k = 5 -- none of them a diagonal class.  Its degree-2 Gram block
is therefore identically zero on the diagonal at every k of the band:

    325 of 325 diagonal entries exactly zero, 0 negative

so it is not positive definite, and NOT because anything obstructs it.  The
identity pins no Gram entry that positivity can read.  "Sharp demand 2" is a
statement about targets, not a localisation of the design.
"""
import os, sys
from fractions import Fraction as F
HERE = "/home/ae/src/dcprevere/maths/problems/permanents/sub-dittert"
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "dittert")); sys.path.insert(0, HERE)
import allk_gen2 as gen2, band2_family as bf, band2_identity as b2, k4_system as k4
from general_k3 import RF
ZERO = RF([]); ONE = RF([F(1)])

sym2 = k4.build(verbose=False); M2 = gen2.build_matrix(sym2); rows2 = sym2["rows"]
ng, ns, nl = len(sym2["gvars"]), len(sym2["svars"]), len(sym2["lvars"])
degs = bf.row_degrees(sym2)
hi = [i for i, d in enumerate(degs) if d >= 4]
tc = bf.type_columns(sym2)
# D1 frame: (1,2) off.  high = (2,2) classes only.
high = sorted(tc.get(("g",(2,2)),[]) + tc.get(("s",(2,2)),[]))
lam  = list(range(ng+ns, ng+ns+nl))
cols = high + lam
rhs = {k: b2.rhs_rf(rows2, k) for k in (2,3,4,5)}

def solve_hi(k):
    """canonical solution on the H rows, free coords zero"""
    A = [[M2[i][c] for c in cols] + [rhs[k][i]] for i in hi]
    nR, nc = len(A), len(cols)
    piv, r = [], 0
    for c in range(nc):
        p = next((i for i in range(r,nR) if A[i][c]), None)
        if p is None: continue
        A[r],A[p] = A[p],A[r]; pv=A[r][c]; A[r]=[t/pv for t in A[r]]
        for i in range(nR):
            if i!=r and A[i][c]:
                f=A[i][c]; A[i]=[A[i][t]-f*A[r][t] for t in range(nc+1)]
        piv.append(c); r+=1
        if r==nR: break
    inc = [i for i in range(r,nR) if A[i][nc]]
    x = [ZERO]*nc
    for idx,c in enumerate(piv): x[c] = A[idx][nc]
    return x, len(inc), r

sols = {}
for k in (2,3,4,5):
    x, inc, rk = solve_hi(k)
    sols[k] = x
    print(f"  k={k}: high-row system rank {rk}, inconsistent {inc}")

# express rhs_H(2),(3) via rhs_H(4),(5) modulo the lambda span
def rank_of(vs):
    A=[list(v) for v in vs]; nR=len(A); nc=len(A[0]) if A else 0; r=0
    for c in range(nc):
        p=next((i for i in range(r,nR) if A[i][c]),None)
        if p is None: continue
        A[r],A[p]=A[p],A[r]; pv=A[r][c]; A[r]=[t/pv for t in A[r]]
        for i in range(nR):
            if i!=r and A[i][c]:
                f=A[i][c]; A[i]=[A[i][t]-f*A[r][t] for t in range(nc)]
        r+=1
        if r==nR: break
    return r
lamv=[[M2[i][c] for i in hi] for c in lam]
base=[[rhs[k][i] for i in hi] for k in (4,5)]
r0=rank_of(lamv+base)
for k in (2,3):
    v=[[rhs[k][i] for i in hi]]
    print(f"  rhs_H({k}) in span(lambda, rhs_H(4), rhs_H(5)): "
          f"{rank_of(lamv+base+v)==r0}")
print(f"  dim of the quotient spanned by the four rhs mod lambda: "
      f"{r0-rank_of(lamv)}")

# the pinned (2,2) sigma_11 Gram at n=5, exact LDL
import numpy as np
from exactsd import assemble, ldl_pivots
from sos import build_sdp
nn = 5
d = build_sdp(nn, 4, 2, verbose=False)
B = d["B"]; basis = d["basis"]
from general_k3 import cells_of
def pkey(orb, fix):
    u,v = divmod(orb[0], B)
    return k4.canon_pair(cells_of(basis[u],nn), cells_of(basis[v],nn), fix)
gk = [pkey(o, False) for o in d["g_orbits"]]
sk = [pkey(o, True)  for o in d["s_orbits"]]
gpos = {key:j for j,key in enumerate(sym2["gvars"])}
spos = {key:j for j,key in enumerate(sym2["svars"])}
deg2 = [u for u in range(B) if len(basis[u])==2]
print(f"\n  n={nn}: Gram {B}x{B}, degree-2 part {len(deg2)}")
for k in (2,3,4,5):
    x = sols[k]
    full = [ZERO]*(ng+ns+nl)
    for t,c in enumerate(cols): full[c] = x[t]
    xq = [full[gpos[key]].at(F(nn)) for key in gk]
    yq = [full[ng+spos[key]].at(F(nn)) for key in sk]
    G0 = assemble(B, d["g_orbits"], xq); H = assemble(B, d["s_orbits"], yq)
    for nm, G in (("sigma_0", G0), ("sigma_11", H)):
        sub = [[G[u][v] for v in deg2] for u in deg2]
        piv, fail = ldl_pivots(sub)
        dz = sum(1 for i in range(len(deg2)) if sub[i][i] == 0)
        dn = sum(1 for i in range(len(deg2)) if sub[i][i] < 0)
        nzc = sum(1 for t in range(len(cols)) if x[t])
        diag_neg = f"{dz} zero, {dn} negative; nonzero free coords {nzc} of {len(cols)}"
        print(f"    k={k} {nm:<9s} (2,2) block: "
              f"{'PD' if piv else f'NOT PD, first bad pivot {fail}'}"
              f"; diagonal: {diag_neg}")
