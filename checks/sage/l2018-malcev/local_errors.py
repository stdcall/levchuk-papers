"""Exact bounded checks for Cartan action, Lemma 5 and the D-type ideal sum.

Passages: sec:l2018-malcev-preliminaries,
lem:l2018-malcev-hypercenters, lem:l2018-malcev-centralizers.
These checks do not certify the classification theorems.
"""
from sage.all import ZZ, QQ, GF, matrix, vector
import json

records=[]
def E(d,i,j,base=ZZ):
    a=matrix(base,d);a[i,j]=1;return a
# C2: r=epsilon_2-epsilon_1, s=2epsilon_1, h_s=coroot(s).
er=E(4,1,0)-E(4,2,3)
hs=E(4,0,0)-E(4,2,2)
r=vector(ZZ,[-1,1]);s=vector(ZZ,[2,0])
assert hs*er-er*hs == -er
assert 2*r.dot_product(s)/s.dot_product(s)==-1
assert 2*r.dot_product(s)/r.dot_product(r)==-2
records.append(dict(check='Cartan denominator C2', observed=-1, printed=-2, corrected=-1))
# B2 over F2. Basis e21, e10, e20, e2,-1.
F=GF(2);ids=[2,1,0,-1,-2];pos={a:i for i,a in enumerate(ids)}
def B(i,j):return E(5,pos[i],pos[j],F)
e21=B(2,1)-B(-1,-2);e10=B(1,0)-2*B(0,-1);e20=B(2,0)-2*B(0,-2)
assert e21*e10-e10*e21==e20 and e20!=0
records.append(dict(check='Lemma5 B2 boundary', field='GF(2)',
                    element='e21', claimed='central', bracket_with_e10='e20 != 0'))
# Dn principal root ideals from componentwise nonnegative simple-root expansions.
for n in range(3,9):
    units=[vector(ZZ,[int(i==j) for j in range(n)]) for i in range(n)]
    roots={(i,j):units[i-1]-units[j-1] for i in range(2,n+1) for j in range(1,i)}
    roots.update({(i,-j):units[i-1]+units[j-1] for i in range(2,n+1) for j in range(1,i)})
    simple=[units[0]+units[1]]+[units[i]-units[i-1] for i in range(1,n)]
    base=matrix(QQ,simple).transpose()
    coefficients={key:base.solve_right(r) for key,r in roots.items()}
    assert all(all(c>=0 and c in ZZ for c in cs) for cs in coefficients.values())
    for i in range(2,n+1):
        def ideal(key):return {k for k,v in coefficients.items()
                              if all(a-b>=0 for a,b in zip(v,coefficients[key]))}
        rectangular={k for k in roots if k[0]>=i and k[1]<=1}
        assert ideal((i,-1))|ideal((i,1)) == rectangular
    records.append(dict(check='Dn T_i1 principal ideal sum', rank=n,
                        verified_i=list(range(2,n+1)), passed=True))
print(json.dumps(records,indent=2))
