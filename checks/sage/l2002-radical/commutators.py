"""Exact checks of formulas (12)--(14), conjugation, and a small counterexample.

The symbolic calculation covers 2 by 2 matrices over a rational function field.
Finite calculations cover the explicitly reported rings and ranks only.
"""
from sage.all import *
import json, sys

def adj(a, b):
    return a + b + a*b

def inv(a):
    return (1 + a).inverse() - 1

def comm(a, b):
    return adj(adj(adj(inv(a), inv(b)), a), b)

def unit(ring, n, i, j):
    e = zero_matrix(ring, n)
    e[i,j] = 1
    return e

def rhs13(a, x, k, m):
    n = a.nrows(); ring = a.base_ring(); star = inv(a)
    e = lambda i,j: unit(ring,n,i,j)
    out = zero_matrix(ring,n)
    for u in range(n):
        if u == k: continue
        for v in range(n):
            if v != m: out += x*star[u,k]*a[m,v]*e(u,v)
        out += x*(1+a[m,m])*star[u,k]*e(u,m)
    for v in range(n):
        if v != m:
            out += x*(1+star[k,k]-x*star[m,k])*a[m,v]*e(k,v)
    out += x*(adj(a[m,m],star[k,k])-x*star[m,k]*(1+a[m,m]))*e(k,m)
    return out

def rhs14(a,x,k):
    n=a.nrows();ring=a.base_ring();star=inv(a);xp=-x/(1+x)
    e=lambda i,j:unit(ring,n,i,j)
    out=zero_matrix(ring,n)
    for u in range(n):
        if u == k: continue
        for v in range(n):
            if v != k: out += x*star[u,k]*a[k,v]*e(u,v)
        out += x*(1+a[k,k])*star[u,k]*e(u,k)
    for v in range(n):
        if v != k: out -= xp*(1+star[k,k])*a[k,v]*e(k,v)
    out -= xp*adj(star[k,k],a[k,k])*e(k,k)
    return out

P=PolynomialRing(QQ,names=('a','b','c','d','x','y','z'))
F=P.fraction_field(); a,b,c,d,x,y,z=F.gens()
A=matrix(F,[[a,b],[c,d]]); E=lambda i,j:unit(F,2,i,j)
symbolic=[]
row_extension_checks=0
for k in range(4):
    for m in range(4):
        for u in range(k+1,4):
            if k==m or u==m:continue
            assert comm(unit(F,4,u,k),x*unit(F,4,k,m))==x*unit(F,4,u,m)
            row_extension_checks+=1
for k,m in [(0,1),(1,0)]:
    assert comm(x*E(k,m),A)==rhs13(A,x,k,m)
    t=-x*y;tp=-t/(1+t)
    factor=adj(adj(adj(x*tp*E(k,m),t*E(m,m)),tp*E(k,k)),-y*tp*E(m,k))
    assert comm(x*E(k,m),y*E(m,k))==factor
    symbolic.extend(['12:'+str((k,m)),'13:'+str((k,m))])
for k in range(2):
    assert comm(x*E(k,k),A)==rhs14(A,x,k)
    # The printed last sign in (14) is positive. Keep it as a refuted reading.
    printed=rhs14(A,x,k)+2*(-x/(1+x))*adj(inv(A)[k,k],A[k,k])*E(k,k)
    assert comm(x*E(k,k),A)!=printed
    symbolic.append('14:'+str(k))
for m,t in [(0,1),(1,0)]:
    B=A
    corrected=B+z*E(m,t)*B-z*B*E(m,t)-z*z*E(m,t)*B*E(m,t)
    assert adj(adj(z*E(m,t),B),-z*E(m,t))==corrected
    assert corrected != corrected-identity_matrix(F,2)
    assert corrected[m,t] == B[m,t]+z*(B[t,t]-B[m,m])-z*z*B[t,m]
    assert corrected[m,t] != B[m,t]-z*(B[t,t]-B[m,m])-z*z*B[t,m]
    symbolic.append('conjugation:'+str((m,t)))

set_random_seed(200243)
finite_count=0; column_cases=[]
for modulus,prime,n,samples in [(9,3,2,120),(27,3,3,150),(25,5,3,150)]:
    ring=Integers(modulus);e=lambda i,j:unit(ring,n,i,j)
    for _ in range(samples):
        aa=matrix(ring,n,lambda i,j:ring.random_element() if i>j else prime*ring.random_element())
        for k in range(n):
            for m in range(n):
                xx=ring.random_element() if k>m else prime*ring.random_element()
                if k==m:
                    assert comm(xx*e(k,k),aa)==rhs14(aa,xx,k)
                else:
                    bb=comm(xx*e(k,m),aa)
                    assert bb==rhs13(aa,xx,k,m)
                    lam=[aa[m,i]/(1+aa[m,m]) for i in range(n)]
                    reduced=bb
                    for i in range(n):
                        if i not in (k,m):
                            reduced=adj(adj(lam[i]*e(m,i),reduced),-lam[i]*e(m,i))
                    reduced=adj(adj(lam[k]*e(m,k),reduced),-lam[k]*e(m,k))
                    expected=zero_matrix(ring,n)
                    for s in range(n):
                        for t in range(n):
                            if t==m and s!=m:expected[s,t]=bb[s,t]
                            elif s==m and t==m:expected[s,t]=-xx*xx*inv(aa)[m,k]*aa[m,k]-lam[k]*xx
                            elif s==k and t!=m:expected[s,t]=lam[t]*xx
                            elif s==m and t!=m:expected[s,t]=lam[k]*lam[t]*xx
                    assert reduced==expected
                    column_cases.append(True)
                finite_count+=1

ring=Integers(4);e=lambda i,j:unit(ring,2,i,j)
G=[matrix(ring,[[a,b],[c,d]]) for a in (0,2) for b in (0,2) for c in range(4) for d in (0,2)]
key=lambda aa:tuple(int(x) for x in aa.list())
known={key(zero_matrix(ring,2)),key(2*e(0,1))}
while True:
    before=len(known)
    mats=[matrix(ring,2,2,list(k)) for k in known]
    for h in mats:
        known.add(key(inv(h)))
        for g in G: known.add(key(adj(adj(inv(g),h),g)))
        for h2 in mats:known.add(key(adj(h,h2)))
    if len(known)==before:break
assert key(2*e(1,0)) not in known
result={
 'sage_version':version(),
 'symbolic_pass':symbolic,
 'lemma_3_1_row_extension_checks':row_extension_checks,
 'finite_formula_checks':finite_count,
 'finite_rings':[['Z/9',2,120],['Z/27',3,150],['Z/25',3,150]],
 'lemma_3_2_pass':sum(column_cases),'lemma_3_2_fail':len(column_cases)-sum(column_cases),
 'lemma_3_1_counterexample':{'K':'Z/4','J':'2K','F':'2K','normal_closure_of':'2e12',
   'group_order':len(G),'normal_closure_order':len(known),
   'normal_closure_matrices':sorted(known),'2e21_contained':False},
 'scope':'Symbolic rank 2 identities plus sampled exact finite-ring matrices in ranks 2 and 3; no claim of an all-rank proof.'}
print(json.dumps(result,indent=2))
print(f"ok l2002-radical commutators: {len(symbolic)} symbolic identities, "
      f"{row_extension_checks} row extensions, "
      f"{finite_count} finite identities, {sum(column_cases)} column reductions, "
      "one exhaustive counterexample", file=sys.stderr)
