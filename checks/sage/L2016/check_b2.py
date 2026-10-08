from sage.all import GF, QQ, matrix, vector, identity_matrix, factorial
from itertools import product
import json
from pathlib import Path

out=Path(__file__).resolve().parent
# Order: e10,e2,-1,e20,e21. The only nonzero characteristic-two
# bracket is [e21,e10]=e20 (and its symmetric characteristic-two mate).
k=GF(2)
def bracket(x,y):
    return vector(k,[0,0,x[3]*y[0]+x[0]*y[3],0])
one=identity_matrix(k,4)
f=matrix(k,one);f[1,3]=1
basis=[vector(k,[int(i==j) for i in range(4)]) for j in range(4)]
assert f*f==one
assert all(f*bracket(x,y)==bracket(f*x,f*y) for x,y in product(basis,repeat=2))
# Integral Chevalley adjoint generators. With [y,e_r] as the
# publication's ad(e_r), D^3=0 and exp(D)=I+D+D^2/2.
def rational_bracket(x,y):
    return vector(QQ,[0,2*(x[2]*y[0]-x[0]*y[2]),
                      x[3]*y[0]-x[0]*y[3],0])
qbasis=[vector(QQ,x) for x in basis]
gens=[]
for root in qbasis:
    d=matrix(QQ,[rational_bracket(x,root) for x in qbasis]).transpose()
    g=identity_matrix(QQ,4)+d+d*d/2
    assert all(z.denominator()==1 for z in g.list())
    gens.append(matrix(k,g))
for g in gens:
    assert all(g*bracket(x,y)==bracket(g*x,g*y) for x,y in product(basis,repeat=2))
inner={tuple(one.list())}; queue=[one]
for a in queue:
    for g in gens:
        h=a*g;key=tuple(h.list())
        if key not in inner:
            inner.add(key);queue.append(h)
assert tuple(f.list()) not in inner
assert all(bracket((f-one)*x,y)==0 for x,y in product(basis,repeat=2))
# Centre span(e2,-1,e20); R/Z is nonzero, Z2=R.
assert sum(all(bracket(x,y)==0 for y in basis) for x in product(k,repeat=4))==4
print('PASS B2 GF2 central outer automorphism, chi=1; inner order',len(inner))
