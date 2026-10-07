"""Exact bounded checks of (4.2)--(4.7) and the quasi-inverse filtration.

Integral matrix models independently realize every ordered basis-pair bracket
in ranks 3 and 4. This is not a proof of the infinite classifications.
"""
from sage.all import ZZ, PolynomialRing, matrix, identity_matrix

checks = 0
def check(condition):
    global checks
    assert condition
    checks += 1

def model(kind, n):
    indices = list(range(1,n+1)) + ([0] if kind=='B' else []) + list(range(-1,-n-1,-1))
    def E(i,j):
        X=matrix(ZZ,len(indices)); X[indices.index(i),indices.index(j)]=1
        return X
    roots=[(i,j) for i in range(1,n+1) for j in range(1,i)]
    if kind=='B': roots += [(i,0) for i in range(1,n+1)]
    roots += [(i,-j) for i in range(1,n+1) for j in range(1,i+(kind=='C'))]
    basis={}
    for i,j in roots:
        if j>0: X=E(i,j)-E(-j,-i)
        elif j==0: X=E(i,0)+2*E(0,-i)
        elif i==-j: X=E(i,j)
        else: X=E(i,j)+(1 if kind=='C' else -1)*E(-j,-i)
        basis[i,j]=X
    return roots,basis

def coefficients(kind,n,a,b,printed=False):
    get=lambda x,i,j:x.get((i,j),0)
    c={}
    for u in range(1,n+1):
        for k in range(0 if kind=='B' else 1,u):
            c[u,k]=sum(get(a,u,j)*get(b,j,k)-get(b,u,j)*get(a,j,k) for j in range(k+1,u))
            if printed and kind=='C':
                c[u,k]+=sum(get(a,k,j)*get(b,u,-j)-get(b,k,j)*get(a,u,-j) for j in range(1,n+1))
        for k in range(1,u):
            c[u,-k]=sum(get(b,j,-k)*get(a,u,j)-get(a,j,-k)*get(b,u,j) for j in range(k if kind=='C' else k+1,u))
            c[u,-k]+=sum(get(a,k,j)*get(b,u,-j)-get(b,k,j)*get(a,u,-j) for j in range(1,n+1))
            if kind=='B': c[u,-k]+=2*(get(a,u,0)*get(b,k,0)-get(b,u,0)*get(a,k,0))
            if kind=='C' or not printed:
                c[u,-k]+=(1 if kind=='C' else -1)*sum(get(a,u,-j)*get(b,k,j)-get(b,u,-j)*get(a,k,j) for j in range(-n if printed else -k+1,0))
        if kind=='C':
            c[u,-u]=2*sum(get(a,u,j)*get(b,u,-j)-get(b,u,-j if printed else j)*get(a,u,j if printed else -j) for j in range(1,u))
    return c

refuted=set()
for kind in ('B','C','D'):
    for n in (3,4):
        roots,basis=model(kind,n)
        zero=matrix(ZZ,next(iter(basis.values())).nrows())
        for r in roots:
            for s in roots:
                bracket=basis[r]*basis[s]-basis[s]*basis[r]
                c=coefficients(kind,n,{r:1},{s:1})
                computed=sum((v*basis[t] for t,v in c.items()),zero)
                assert computed==bracket, (kind,n,r,s,c,computed,bracket)
                check(computed==bracket)
                old=coefficients(kind,n,{r:1},{s:1},printed=True)
                for t in roots:
                    if old[t]!=c[t]:
                        refuted.add(('4.7' if t[0]==-t[1] else '4.5' if t[1]>0 else '4.6') if kind=='C' else '4.3' if kind=='B' else '4.4')
check(refuted=={'4.3','4.4','4.5','4.6','4.7'})

# Each finite truncation of the shift has a nonzero nth superdiagonal up to
# its nilpotence bound. Coordinatewise the infinite series is nevertheless
# finite at every place and gives a two-sided quasi-inverse.
for n in range(2,9):
    A=matrix(ZZ,n)
    for i in range(1,n): A[i,i-1]=1
    I=identity_matrix(ZZ,n)
    gamma=sum(((-A)**k for k in range(1,n)),matrix(ZZ,n))
    check(A+gamma+A*gamma==0)
    check(gamma+A+gamma*A==0)
    for k in range(1,n):
        correct=sum(((-A)**m for m in range(1,k+1)),matrix(ZZ,n))
        old=sum(((-A)**m for m in range(1,k)),matrix(ZZ,n))
        check(all((gamma-correct)[i,j]==0 for i in range(n) for j in range(n) if i-j<=k))
        check((gamma-old)[k,0]!=0)

# The endpoint of the ideal adjacency path is distinguished by exactly one
# nonzero bracket modulo the third lower diagonal, not one zero bracket.
n=7
units=[]
for j in range(n-1):
    X=matrix(ZZ,n);X[j+1,j]=1;units.append(X)
for i,X in enumerate(units):
    neighbors=[j for j,Y in enumerate(units) if X*Y-Y*X!=0]
    check(neighbors==[j for j in range(n-1) if abs(i-j)==1])
check(units[0]*units[1]-units[1]*units[0]!=0)

# Universal isolation identity in the repaired Lie-ideal argument, with all
# lower-triangular coordinates independent over ZZ (no commutativity or
# coefficient specialization is used in these linear identities).
n=7
pairs=[(i,j) for i in range(n) for j in range(i)]
P=PolynomialRing(ZZ,names=['a%d_%d'%r for r in pairs])
X=matrix(P,n)
for r,z in zip(pairs,P.gens()): X[r]=z
def unit(i,j):
    E=matrix(P,n);E[i,j]=1;return E
bracket=lambda A,B:A*B-B*A
for i in range(n):
    for m in range(1,i):
        for p in range(i+1,n):
            for q in range(m):
                check(bracket(unit(p,i),bracket(X,unit(m,q)))==X[i,m]*unit(p,q))
# Finite interval test of the centralizer equality used in Lemma 1:
# C(FT_{i+1,m-1}) has allowed basis entries precisely in T_{m,i}.
n=9
for m in range(2,5):
    for i in range(m+1,7):
        rectangle=[unit(p,q) for p in range(i,n) for q in range(m-1)]
        for u in range(n):
            for v in range(u):
                central=all(bracket(unit(u,v),E)==0 for E in rectangle)
                check(central==(u>=m-1 and v<=i-1))
print('ok l2019-nonfinitary:',checks,'exact bounded assertions')
print('Printed formulas refuted:',','.join(sorted(refuted)))
print('Scope: integral rank-3/rank-4 brackets; finite shift truncations; ideal adjacency. No infinite classification proof.')
