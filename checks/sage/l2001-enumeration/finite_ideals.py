from sage.all import *
import json, datetime, hashlib
from pathlib import Path

def gaussian(m,k,q):
    return prod(QQ(q**m-q**i)/(q**k-q**i) for i in range(k))
def proper_counts(q,limit):
    values=[0]
    for m in range(1,limit+1):
        values.append(sum(gaussian(m,k,q) for k in range(1,m+1))-
            sum(binomial(m,j)*values[j] for j in range(1,m)))
    return values
results=[]
for n,q in [(2,2),(3,2),(3,3),(3,4),(4,2)]:
    F=GF(q); positions=[(i,j) for i in range(n) for j in range(i)]
    d=len(positions); V=VectorSpace(F,d); basis=V.basis()
    def mult(a,b):
        aa=dict(zip(positions,a)); bb=dict(zip(positions,b))
        return V([sum(aa.get((i,k),0)*bb.get((k,j),0) for k in range(n)) for i,j in positions])
    ideals=0; scanned=0
    for k in range(d+1):
        for S in V.subspaces(k):
            scanned+=1
            if all(mult(a,b) in S and mult(b,a) in S for a in S.basis() for b in basis):
                ideals+=1
    Q=proper_counts(q,n-1)
    expected=1+sum(QQ(1)/n*binomial(n,m)*binomial(n,m+1)*Q[m] for m in range(1,n))
    assert ideals==expected
    results.append(dict(n=n,q=q,subspaces=scanned,ideals=ideals,theorem4=int(expected)))
project=Path(__file__).resolve().parents[3]
checked=project/'content/papers/l2001-enumeration/05-problems.typ'
print(json.dumps(dict(results=results,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    checked_text_sha256={str(checked.relative_to(project)):hashlib.sha256(checked.read_bytes()).hexdigest()},
    version=version(),limits='Exhaustive K-linear subspaces of NT_n(GF(q)) for the listed pairs only; closure tested under all basis multiplications on both sides. Does not enumerate arbitrary additive subgroups over nonprime fields or prove classification for all n.'),indent=2))
