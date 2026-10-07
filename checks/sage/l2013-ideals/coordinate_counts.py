"""Exact bounded checks of the coordinate version and corrected path indices.

Passages: th:l2013-ideals-main-count,
lem:l2013-ideals-primary-staircase-count,
lem:l2013-ideals-secondary-staircase-count.
This does not classify general D-invariant ideals. The latter statement is
refuted separately in diagonal_ideal_counterexample.py.
"""
from sage.all import ZZ, QQ, binomial, PolynomialRing
from sage.env import SAGE_VERSION as sage_version
from itertools import combinations, product
import json

checks=0
def check(v):
    global checks
    assert v
    checks+=1

def corners(n):
    for r in range(1,n+1):
        for rows in combinations(range(n),r):
            for cols in combinations(range(n),r):
                yield tuple(zip(rows,cols))

def secondary(n,i,j):
    for q in range(min(i,n-j-1)+1):
        for rows in combinations(range(i),q):
            for cols in combinations(range(j+1,n),q):
                yield tuple(zip(rows,cols))

def ideals_from_corners(n,s):
    out={(s,)*(n*n)}
    for m in range(s):
        for L in corners(n):
            if m==0 and any(i<=j for i,j in L):continue
            choices=[()] if m==s-1 else secondary(n,L[0][0],L[-1][1])
            for free in choices:
                Lp=((0,L[-1][1]),(L[0][0],n-1))+tuple(free)
                a=[]
                for i,j in product(range(n),repeat=2):
                    value=min(s,m+2)
                    if any(i>=k and j<=l for k,l in Lp):value=min(value,m+1)
                    if any(i>=k and j<=l for k,l in L):value=m
                    a.append(value)
                check(tuple(a) not in out)
                out.add(tuple(a))
    return out

def valid(a,n,s):
    for i,j in product(range(n),repeat=2):
        if i<=j and a[i*n+j]<min(1,s):return False
        for k in range(n):
            if a[k*n+j]>a[i*n+j]+int(k<=i):return False
            if a[i*n+k]>a[i*n+j]+int(j<=k):return False
    return True

def omega(n,s):
    if s==1:return binomial(2*n,n-1)//n
    return (s-1)*(2*n-1)*binomial(2*n-2,n-1)+binomial(2*n,n)-2**(2*n-2)

examined=0; outcomes=[]
for n,s in [(2,s) for s in range(1,6)]+[(3,s) for s in range(1,4)]+[(4,1)]:
    expected=ideals_from_corners(n,s)
    actual=set()
    for a in product(range(s+1),repeat=n*n):
        examined+=1
        if valid(a,n,s):actual.add(a)
    check(actual==expected)
    check(len(actual)==omega(n,s))
    outcomes.append(dict(n=n,s=s,count=len(actual)))

for n in range(2,9):
    full=list(corners(n));strict=[L for L in full if all(i>j for i,j in L)]
    check(len(full)==binomial(2*n,n)-1)
    total=plus=0
    for i,j in product(range(n),repeat=2):
        primary=[L for L in full if L[0][0]==i and L[-1][1]==j]
        other=list(secondary(n,i,j))
        check(len(primary)==binomial(n-i+j-1,n-i-1))
        strict_primary=sum(L in strict for L in primary)
        check(strict_primary==binomial(n-i+j-1,n-i-1)-binomial(n-i+j-1,j-i))
        check(len(other)==binomial(i+n-j-1,n-j-1))
        for r in range(1,n+1):
            actual=sum(len(L)==r for L in primary)
            check(actual==binomial(n-i-1,r-1)*binomial(j,r-1))
        for q in range(n+1):
            actual=sum(len(L)==q for L in other)
            check(actual==binomial(i,q)*binomial(n-j-1,q))
        total+=len(primary)*len(other)
        plus+=sum(L in strict for L in primary)*len(other)
    check(total==(2*n-1)*binomial(2*n-2,n-1))
    check(plus==(2*n-1)*binomial(2*n-2,n-1)-2**(2*n-2))
    check(sum(binomial(n+d-1,d)*2**(n-d-1) for d in range(n))==2**(2*n-2))

# Printed Theorem 3.3 and Main Theorem fail independently of D-invariance.
printed_plus3=2**5+2*binomial(4,2)-QQ(4)/3*binomial(6,1)-binomial(6,3)
check(printed_plus3==16)
check(printed_plus3!=14)
check(omega(3,2)==34)
check(omega(3,2)!=36)

# Printed r and q+1 indices fail even at boundary corners (n,i,j)=(2,2,1).
check(binomial(0,1)*binomial(0,1)!=1)
check(binomial(1,1)*binomial(1,1)==1)
check(binomial(1,0)*binomial(1,0)==1)

# The four expanded residue terms have the opposite signs in the source.
R=PolynomialRing(QQ,'x');x=R.gen();F=R.fraction_field();x=F(x)
for n in range(2,8):
    for i in range(1,n+1):
        for j in range(1,n+1):
            direct=(1-x)**(-j)*x**i*((1-x)-(1-x)**j)/(1-(1-x))*(x**(-i-1)-x**(-n-1))/(1-x**(-1))
            corrected=-(1-x)**(-j)*x**(-1)+(1-x)**(-1)*x**(-1)+(1-x)**(-j)*x**(-n+i-1)-(1-x)**(-1)*x**(-n+i-1)
            check(direct==corrected)
            if direct:check(direct!=-corrected)
print(json.dumps(dict(sage=sage_version,assertions=checks,valuation_arrays_examined=examined,bounded_counts=outcomes),indent=2))
print(f'ok l2013-ideals coordinate_counts: {checks} checks')
