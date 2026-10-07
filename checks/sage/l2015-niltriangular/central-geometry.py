"""Theorem 4.8: actual Q/[g,Q], all ambient commutators, all S,N.

Finite verification only; the general proof is the double-commutator
and graph argument in th:l2015-niltriangular-lie-enumeration. In particular
this program does not replace actual quotient geometry by 2r coordinates.
"""
from sage.all import GF,VectorSpace,binomial
from itertools import combinations
from copy import copy
import json

checks=0
def check(c):
    global checks
    assert c
    checks+=1
def chains(n):
    for m in range(1,n):
        for ii in combinations(range(2,n+1),m):
            for jj in combinations(range(1,n),m):
                if all(j<i for i,j in zip(ii,jj)):yield tuple(zip(ii,jj))
def bracket(a,b):
    i,j=a;u,v=b
    ans={}
    if j==u:ans[i,v]=1
    if v==i:ans[u,j]=ans.get((u,j),0)-1
    return {p:c for p,c in ans.items() if c}
def quotient(c,n):
    positions=tuple((i,j) for i in range(2,n+1) for j in range(1,i))
    Q=tuple(p for p in positions if p not in c and
            any(p[0]>=i and p[1]<=j for i,j in c))
    D=tuple(p for p in Q if any(p[0]>=i and p[1]<=j and
             p[0]-i+j-p[1]>=2 for i,j in c))
    W=tuple(p for p in Q if p not in D)
    check(set(D)=={p for a in positions for b in Q for p in bracket(a,b)})
    check(all(p in D for a in positions for b in D for p in bracket(a,b)))
    check(all(p in D for a in positions for b in W for p in bracket(a,b)))
    maps=tuple(tuple(tuple(bracket(a,b).get(p,0) for p in W) for b in c)
               for a in positions)
    return D,W,tuple(sorted(set(m for m in maps if any(any(v) for v in m))))
def table(n,q):
    return {2:1,3:q+3,4:3*q*q+4*q+6,
        5:q**4+7*q**3+14*q*q+9*q+10,
        6:2*q**6+5*q**5+26*q**4+35*q**3+34*q*q+14*q+15}[n]
def gaussian(q,c,d):
    # Exact product; division only after multiplication.
    top=1;bot=1
    for k in range(d):top*=q**(c-k)-1;bot*=q**(d-k)-1
    return top//bot
cache={}
def count(c,n,q,all_N=True):
    D,wp,maps=quotient(c,n); key=(q,len(c),len(wp),maps,all_N)
    if key in cache:return cache[key]
    F=GF(q);A=VectorSpace(F,len(c));W=VectorSpace(F,len(wp))
    Ns=[N for d in range(len(wp)+1) for N in W.subspaces(d)] if all_N else None
    total=0
    for t in range(1,len(c)+1):
        for S in A.subspaces(t):
            if not all(any(v[i] for v in S.basis()) for i in range(len(c))):continue
            images=[W([sum(v[a]*f[a][k] for a in range(len(c)))
                    for k in range(len(wp))]) for f in maps for v in S.basis()]
            I=W.subspace(images);dimc=W.dimension()-I.dimension()
            expected=sum(gaussian(q,dimc,d)*q**(t*(dimc-d)) for d in range(dimc+1))
            if all_N:
                direct=sum(q**(t*(W.dimension()-N.dimension())) for N in Ns if I.is_subspace(N))
                check(direct==expected)
            total+=expected
    cache[key]=total
    return total
cases=[]
for q,maxn in ((2,6),(3,5),(4,4)):
    for n in range(2,maxn+1):
        total=sum(count(c,n,q) for c in chains(n))
        print(f'q={q},n={n}: actual={total}, table={table(n,q)}',flush=True)
        check(total==table(n,q))
        cases.append(dict(q=q,n=n,nonzero_ideals=int(total)))
specials=[(6,((2,1),(4,3),(6,5)),2,2),
          (8,((4,1),(6,2),(8,5)),1,2),
          (6,((3,1),(4,3),(6,4)),1,0),
          (7,((2,1),(4,2),(5,3),(7,5)),2,1)]
geometry=[]
for n,c,r,expected_c in specials:
    D,wp,maps=quotient(c,n)
    for q in (2,3):
        W=VectorSpace(GF(q),len(wp))
        I=W.subspace([W([sum(f[a][k] for a in range(len(c)))
              for k in range(len(wp))]) for f in maps])
        # The first example has one proportional condition per pair;
        # the nonadjacent and overlapping examples use real cell counts.
        if n==6 and len(c)==3 and c[0]==(2,1):check(W.dimension()-I.dimension()==2)
        elif n==8:check(W.dimension()-I.dimension()==1)
        elif n==7:check(W.dimension()-I.dimension()==1)
        else:check(W.dimension()-I.dimension()==0)
        total=count(c,n,q)
        if n==6 and c[0]==(2,1):check(total==2*q**4-q**3)
        geometry.append(dict(n=n,corners=c,q=q,W=list(wp),dimI=int(I.dimension()),
                             total=int(total)))
print(json.dumps(dict(cases=cases,specials=geometry,checks=checks,
                     shapes=len(cache)),ensure_ascii=False))
print(f'ok central geometry: {checks} checks')
