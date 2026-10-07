"""Exact checks for Theorems 4.7, 4.8 and Table 1 (pp. 44–45).

All staircase chains for n <= 6 are checked against the small-rank
polynomial expansion. The unrestricted formula is checked in
central-geometry.py, using the actual quotient cells. All Lie ideals
are independently enumerated for
GF(2), n <= 4 and GF(3), GF(4), n <= 3. This does not prove the
classification for arbitrary fields, division rings, or additive ideals.
"""
from sage.all import ZZ, PolynomialRing, VectorSpace, GF, binomial, prod
from itertools import combinations
import json

R=PolynomialRing(ZZ,'q'); q=R.gen(); checks=0
def check(c):
    global checks
    assert c
    checks+=1
def proper(m,t):
    return sum(prod((q**(k+1)-1)**(js[k+1]-js[k]-1)
                    for k in range(t-1))*(q**t-1)**(m-js[-1])
               for rest in combinations(range(2,m+1),t-1)
               for js in [(1,)+rest])
def chains(n):
    for m in range(1,n):
        for is_ in combinations(range(2,n+1),m):
            for js in combinations(range(1,n),m):
                if all(j<i for i,j in zip(is_,js)):
                    yield tuple(zip(is_,js))
def components(chain):
    # Small-rank geometry only (n<=6): remove all forced central coordinates.
    # The remaining cell graph and corner-constraint graph are forests.
    n=max(i for i,j in chain)
    P=[(i,j) for i in range(2,n+1) for j in range(1,i)]
    Q=[p for p in P if p not in chain and any(p[0]>=i and p[1]<=j for i,j in chain)]
    D=[p for p in Q if any(p[0]>=i and p[1]<=j and p[0]-i+j-p[1]>=2 for i,j in chain)]
    W=[p for p in Q if p not in D]
    maps=[]
    for u,v in P:
        terms=[]
        for a,(i,j) in enumerate(chain):
            if v==i and (u,j) in W:terms.append((W.index((u,j)),a))
            if j==u and (i,v) in W:terms.append((W.index((i,v)),a))
        if terms:maps.append(terms)
    forced={f[0][0] for f in maps if len(f)==1}
    while True:
        enlarged=forced|{x for f in maps if any(x in forced for x,a in f) for x,a in f}
        if enlarged==forced:break
        forced=enlarged
    free=[f for f in maps if all(x not in forced for x,a in f)]
    check(all(len(f)==2 for f in free))
    pending=set(range(len(free))); answer=[]
    while pending:
        start=pending.pop(); edges={start}; cells={x for x,a in free[start]}
        while True:
            extra={k for k in pending if any(x in cells for x,a in free[k])}
            if not extra:break
            edges|=extra;pending-=extra;cells|={x for k in extra for x,a in free[k]}
        check(len(cells)==len(edges)+1)
        answer.append(tuple(tuple(a for x,a in free[k]) for k in sorted(edges)))
    # Independent proportionality conditions contract a forest of corners.
    parent=list(range(len(chain)))
    def find(a):
        while parent[a]!=a:a=parent[a]
        return a
    for f in free:
        a,b=(a for x,a in f);a=find(a);b=find(b)
        check(a!=b);parent[a]=b
    return tuple(answer)
def links(chain):
    return tuple((a,a+1) for a,((i,j),(u,v)) in
                 enumerate(zip(chain,chain[1:])) if v==i+1)
def one(chain,corrected=True):
    m=len(chain); r=len(links(chain))
    return sum((binomial(r,s) if corrected else 1)*(q-1)**s
               *sum(q**(s*t)*proper(m-s,t) for t in range(1,m-s+1))
               for s in range(r+1))
def gaussian(a,b):
    if b<0 or b>a: return R.zero()
    if b==0 or b==a: return R.one()
    return gaussian(a-1,b)+q**(a-b)*gaussian(a-1,b-1)
def B(s,t):
    return sum((-1)**(s-u)*binomial(s,u)*sum(gaussian(u,d)*q**(t*(u-d))
               for d in range(u+1)) for u in range(s+1))
def true_one(chain):
    m=len(chain); C=components(chain)
    return sum((q-1)**a*sum(B(s,t)*proper(m-a,t) for t in range(1,m-a+1))
               for s in range(len(C)+1) for chosen in combinations(C,s)
               for a in [sum(len(c) for c in chosen)])
table={2:R(1),3:q+3,4:3*q**2+4*q+7,
       5:q**4+7*q**3+14*q**2+9*q+10,
       6:2*q**6+5*q**5+20*q**4+46*q**3+27*q**2+16*q+15}
totals={n:sum(true_one(c) for c in chains(n)) for n in range(2,7)}
print(json.dumps({'table':{str(n):{'printed':str(table[n]),
     'corrected':str(totals[n]),'equal':table[n]==totals[n]}
     for n in table}},ensure_ascii=False))
for n in range(2,4): check(table[n]==totals[n])
check(table[4]!=totals[4]); check(totals[4]==3*q**2+4*q+6)
check(table[5]==totals[5])
check(table[6]!=totals[6])
print('actual_n6_polynomial',totals[6],flush=True)
check(totals[6]==2*q**6+5*q**5+26*q**4+35*q**3+34*q**2+14*q+15)
sample=((2,1),(4,3),(6,5))
check(len(links(sample))==2)
check(one(sample)-one(sample,False)==(q-1)*sum(q**t*proper(2,t)
                                            for t in range(1,3)))
check(true_one(sample)-one(sample)==q*(q-1)**3)
check(true_one(sample)==2*q**4-q**3)
for t in range(1,9):
    check(B(0,t)==1)
    check(B(1,t)==q**t)
    check(B(2,t)==q**(2*t)+(q-1)*q**t)
print(json.dumps({'two_links':{'printed':str(one(sample,False)),
                            'corrected':str(one(sample))}},ensure_ascii=False))
for n in range(2,7):
    for c in chains(n):
        pairs=links(c); r=len(pairs); m=len(c)
        # Enumerating edge subsets is independent of the binomial collapse.
        explicit=sum((q-1)**len(sub)*sum(q**(len(sub)*t)*proper(m-len(sub),t)
                     for t in range(1,m-len(sub)+1))
                     for s in range(r+1) for sub in combinations(pairs,s))
        check(explicit==one(c))
        # Geometry is field-independent: forests give one annihilator
        # coordinate per fully proportional cell component. This exact
        # expansion is used only for the five small-rank table rows.
        check(true_one(c).parent()==R)

cases=[]
for order,n in [(2,2),(2,3),(2,4),(3,2),(3,3),(4,2),(4,3)]:
    F=GF(order); positions=[(i,j) for i in range(n) for j in range(i)]
    V=VectorSpace(F,len(positions)); index={p:k for k,p in enumerate(positions)}
    def product(a,b):
        return V([sum(a[index[i,k]]*b[index[k,j]] for k in range(j+1,i))
                  for i,j in positions])
    found=[]; examined=0
    for t in range(V.dimension()+1):
        for S in V.subspaces(t):
            examined+=1
            if all(product(a,b)-product(b,a) in S
                   for a in S.basis() for b in V.basis()): found.append(S)
    check(len(found)==1+totals[n](order))
    cases.append({'q':order,'n':n,'all_ideals':len(found),'subspaces':examined})
    # Both q+3 and 1 count nonzero ideals; the zero subspace is an ideal.
    check(V.zero_subspace() in found)
    check(len(found)!=totals[n](order))
print(json.dumps({'finite_cases':cases,'checks':checks},ensure_ascii=False))
print(f'ok l2015-niltriangular enumeration: {checks} checks')
