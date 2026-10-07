from sage.all import *
from sage.env import SAGE_VERSION
import json
import sys

# Theorem9: independent enumeration of all two-sided ideals in NT(n,GF(q)),
# and of full-coordinate-support subspaces used in the inner summation.
# This checks finite cases only, not the classification theorem.
def gaussian(n,k,q):
    if k < 0 or k > n: return ZZ(0)
    return ZZ(prod(QQ(q**(n-i)-1)/QQ(q**(k-i)-1) for i in range(k)))

def F(m,q):
    return ZZ(sum((-1)**(m-t-k)*q**k*binomial(m-1,t+k-1)*gaussian(t+k-1,k,q)
                  for t in range(1,m+1) for k in range(m-t+1)))

support=[]
for q in [2,3,4,5]:
    for m in range(1,5):
        V=VectorSpace(GF(q,'a'),m)
        count=0
        examined=0
        for t in range(1,m+1):
            for W in V.subspaces(t):
                examined+=1
                if all(any(v[j] for v in W.basis()) for j in range(m)):
                    count+=1
        expected=F(m,q)
        assert count==expected,(q,m,count,expected)
        support.append(dict(q=q,m=m,count=count,subspaces_examined=examined))

def ideal_count(n,q):
    K=GF(q,'a'); positions=[(i,j) for i in range(n) for j in range(i)]
    V=VectorSpace(K,len(positions)); basis=V.basis()
    def mul(a,b):
        out=V([0]*len(positions))
        for u,(i,j) in enumerate(positions):
            for v,(k,l) in enumerate(positions):
                if j==k:
                    out[positions.index((i,l))]+=a[u]*b[v]
        return out
    count=examined=0
    for t in range(V.dimension()+1):
        for W in V.subspaces(t):
            examined+=1
            if all(mul(a,b) in W and mul(b,a) in W for a in W.basis() for b in basis):
                count+=1
    formula=ZZ(sum(QQ(binomial(n,m)*binomial(n,m+1))/n*F(m,q) for m in range(1,n)))
    assert count!=formula # Refuted manuscript reading, which omits the zero ideal.
    assert count==1+formula,(n,q,count,formula)
    return dict(n=n,q=q,ideals=count,subspaces_examined=examined,
                manuscript_without_zero=int(formula),corrected=int(1+formula))

ideals=[ideal_count(n,q) for n,q in [(2,2),(3,2),(3,3),(3,4),(3,5),(4,2)]]

# B(m,Phi): enumerate actual antichains of the positive-root poset.
roots=[]
for kind,ns in [('A',range(1,7)),('B',range(2,7)),('C',range(2,7)),('D',range(4,7))]:
    for rank in ns:
        lattice=RootSystem([kind,rank]).root_lattice()
        ps=[tuple(r[i] for i in range(1,rank+1)) for r in lattice.positive_roots()]
        P=Poset((ps,lambda a,b: all(x<=y for x,y in zip(a,b))),facade=True)
        counts=[0]*(rank+1)
        for antichain in P.antichains(): counts[len(antichain)]+=1
        if kind=='A':
            n=rank+1
            expected=[ZZ(QQ(binomial(n,m)*binomial(n,m+1))/n) for m in range(rank+1)]
        elif kind in ['B','C']:
            n=rank;expected=[binomial(n,m)**2 for m in range(rank+1)]
        else:
            n=rank;expected=[binomial(n,m)*(binomial(n-1,m)+binomial(n-2,m-2)) for m in range(rank+1)]
        assert counts==expected,(kind,rank,counts,expected)
        roots.append(dict(type=kind,rank=rank,antichains=counts))

print(json.dumps(dict(sage=SAGE_VERSION,full_support=support,ideals=ideals,root_antichains=roots),indent=2))
print('ok l2018-enveloping: 41 formula comparisons, including6 refuted manuscript counts',file=sys.stderr)
