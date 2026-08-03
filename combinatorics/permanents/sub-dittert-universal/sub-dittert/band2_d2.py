"""
DESIGN D2 -- the scaled-identity family, and it reduces band 2 to ONE PD test.

D1 frame (block diagonal by degree): the Gram is diag(G^(1,1), G^(2,2)), the
(1,1) block IS band 1's (law B1, PD for n >= n0), so only the (2,2) block is
open.  Only the 75 rows of degree >= 4 see it, together with lambda.

Put every DIAGONAL (2,2) orbit class equal to one scalar t (so that part of the
Gram is t times the identity on the degree-2 basis), and solve the 75 rows for
the off-diagonal (2,2) classes and lambda, canonically.  The solution is AFFINE
in t:                x_Omega(t, k) = p(k) - t h .
Hence            G^(2,2)(t,k) = t ( I - Gram(h) ) + Gram(p(k)) .
t is unconstrained -- the identity holds for every t -- so if  M := I - Gram(h)
is positive definite, then t large enough makes G^(2,2) positive definite, and t
may be taken an explicit rational function of n.  Band 2 then closes.

So the whole design collapses to ONE decidable question:  is M positive definite?
"""
import os, sys
from fractions import Fraction as F
HERE = "/home/ae/src/dcprevere/maths/problems/permanents/sub-dittert"
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "dittert")); sys.path.insert(0, HERE)
import allk_gen2 as gen2, band2_family as bf, band2_identity as b2, k4_system as k4
from general_k3 import RF, cells_of
from exactsd import assemble, ldl_pivots
from sos import build_sdp
ZERO = RF([]); ONE = RF([F(1)])

sym2 = k4.build(verbose=False); M2 = gen2.build_matrix(sym2); rows2 = sym2["rows"]
ng, ns, nl = len(sym2["gvars"]), len(sym2["svars"]), len(sym2["lvars"])
degs = bf.row_degrees(sym2); hi = [i for i,d in enumerate(degs) if d>=4]
tc = bf.type_columns(sym2)
allhigh = sorted(tc.get(("g",(2,2)),[]) + tc.get(("s",(2,2)),[]))
gd, sd = bf.diagonal_classes(sym2)
DIAG = set(gd) | set(sd)
OM = [c for c in allhigh if c not in DIAG]
lam = list(range(ng+ns, ng+ns+nl))
cols = OM + lam
print(f"  diagonal (2,2) classes: {len(DIAG)}   off-diagonal: {len(OM)}   lambda: {len(lam)}")

def solve(target):
    A = [[M2[i][c] for c in cols] + [target[i]] for i in hi]
    nR, nc = len(A), len(cols); piv, r = [], 0
    for c in range(nc):
        p = next((i for i in range(r,nR) if A[i][c]), None)
        if p is None: continue
        A[r],A[p]=A[p],A[r]; pv=A[r][c]; A[r]=[t/pv for t in A[r]]
        for i in range(nR):
            if i!=r and A[i][c]:
                f=A[i][c]; A[i]=[A[i][t]-f*A[r][t] for t in range(nc+1)]
        piv.append(c); r+=1
        if r==nR: break
    inc = sum(1 for i in range(r,nR) if A[i][nc])
    x=[ZERO]*nc
    for idx,c in enumerate(piv): x[c]=A[idx][nc]
    return x, inc, r

# h : response to setting every diagonal class to 1  (target = -sum of those cols)
tgt = [ZERO]*len(rows2)
for i in hi:
    acc = ZERO
    for c in DIAG:
        if M2[i][c]: acc = acc + M2[i][c]
    tgt[i] = ZERO - acc
hvec, inch, rh = solve(tgt)
print(f"  h: rank {rh}, inconsistent {inch}, nonzero coords {sum(1 for v in hvec if v)}")

def coeffs(x, tdiag):
    full=[ZERO]*(ng+ns+nl)
    for t,c in enumerate(cols): full[c]=x[t]
    for c in DIAG: full[c]=full[c]+tdiag
    return full

for nn in [int(a) for a in sys.argv[1:]] or [5, 6]:
    d = build_sdp(nn, 4, 2, verbose=False)
    B=d["B"]; basis=d["basis"]
    def pk(orb, fix):
        u,v=divmod(orb[0],B)
        return k4.canon_pair(cells_of(basis[u],nn), cells_of(basis[v],nn), fix)
    gkey=[pk(o,False) for o in d["g_orbits"]]; skey=[pk(o,True) for o in d["s_orbits"]]
    gpos={k_:j for j,k_ in enumerate(sym2["gvars"])}; spos={k_:j for j,k_ in enumerate(sym2["svars"])}
    deg2=[u for u in range(B) if len(basis[u])==2]
    full = coeffs([ZERO - v for v in hvec], ONE)      # M = I - Gram(h)
    xq=[full[gpos[k_]].at(F(nn)) for k_ in gkey]
    yq=[full[ng+spos[k_]].at(F(nn)) for k_ in skey]
    for nm, orbs, co in (("sigma_0", d["g_orbits"], xq), ("sigma_11", d["s_orbits"], yq)):
        G = assemble(B, orbs, co)
        sub=[[G[u][v] for v in deg2] for u in deg2]
        piv, fail = ldl_pivots(sub)
        dmin = min(sub[i][i] for i in range(len(deg2)))
        mx = max((abs(sub[i][j]) for i in range(len(deg2))
                  for j in range(len(deg2)) if i != j), default=0)
        print(f"  n={nn} {nm:<9s} M = I - Gram(h) on the {len(deg2)}-dim degree-2 basis: "
              f"{'POSITIVE DEFINITE' if piv else f'NOT PD (first bad pivot {fail})'}"
              f";  min diagonal {float(dmin):+.6g}, "
              f"max |off-diagonal| {float(mx):.6g}")
