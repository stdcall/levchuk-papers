from sage.all import GF, matrix, vector, VectorSpace
import json
from pathlib import Path

out = Path(__file__).resolve().parent
checks = 0
def check(x):
    global checks
    assert x
    checks += 1

from model import root_data

results=[]
for n in range(2,8):
    for q in (2,3):
        k=GF(q)
        roots,tables,bracket=root_data(n,k)
        v=VectorSpace(k,len(roots))
        gamma=v
        dims=[gamma.dimension()]
        while gamma.dimension():
            gamma=v.subspace([bracket(x,y) for x in gamma.basis() for y in v.basis()])
            dims.append(gamma.dimension())
        nilclass=len(dims)-1
        print(n,q,dims,nilclass,flush=True)
        check(nilclass==(max(n,2*n-3) if q==2 else 2*n-1))
        # Formula (9): all admissible i, with t=1 in characteristic two.
        if q==2:
            for i in range(1,n-1):
                f=matrix(k,len(roots),len(roots),1)
                for a in range(i+1,n+1):
                    f[roots.index((a,-i)),roots.index((a,i))]+=1
                check(f.det()==1)
                for a,x in enumerate(v.basis()):
                    for b,y in enumerate(v.basis()):
                        check(f*tables[a][b]==bracket(f*x,f*y))
        results.append({'rank':n,'field':q,'lower_dimensions':list(map(int,dims)),
                        'nilpotency_class':nilclass})
print('PASS',checks,results)
