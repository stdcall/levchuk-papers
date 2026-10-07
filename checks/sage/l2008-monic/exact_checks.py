"""Bounded exact checks of the quadratic calculations and interpolation.

The script checks the five printed quadratic tensors in finite dimensions.
It does not prove the full tame-group classification or the lifting claim.
"""
from itertools import permutations
import json
from sage.all import QQ, GF, matrix, vector, PolynomialRing
from sage.version import version


def tensor(n, terms, field=QQ):
    v = vector(field, n**3)
    for (i, a, b), c in terms.items():
        v[(i*n+a)*n+b] += c
    return v


def act(q, L):
    """Quadratic part of L^-1 (identity+q) L; X is a row vector."""
    n = L.nrows()
    inv = L.inverse()
    out = vector(L.base_ring(), n**3)
    for j in range(n):
        for a in range(n):
            for b in range(n):
                c = q[(j*n+a)*n+b]
                if not c:
                    continue
                for i in range(n):
                    for u in range(n):
                        for v in range(n):
                            out[(i*n+u)*n+v] += inv[j,i]*c*L[u,a]*L[v,b]
    return out


def from_images(images, field=QQ):
    n = len(images)
    return matrix(field, n, n, lambda j,i: images[i].get(j, 0))


report = {"sage_version": version, "checks": []}
n = 3
zero = vector(QQ, n**3)
phi1 = tensor(n, {(0,1,1): 1})
phi2 = tensor(n, {(0,1,2): 1})
phi3 = tensor(n, {(0,0,2): 1, (1,1,2): -1})
phi4 = tensor(n, {(0,2,0): 1, (1,2,1): -1})
phi5 = tensor(n, {(0,0,2): 1, (1,2,1): 1, (2,2,2): -1})
L = from_images([{0:1}, {1:1,0:1}, {2:1}])
rhs3 = act(phi2,L) + tensor(n,{(0,1,2):-1,(1,0,2):1})
assert rhs3 == phi3
report["checks"].append({"target":"lem:l2008-monic-quadratic-wild-classes",
                         "calculation":"printed phi3 decomposition", "pass":True})
L = from_images([{2:1}, {1:1,2:1}, {0:1,2:1}])
P23 = from_images([{0:1}, {2:1}, {1:1}])
Pcycle = from_images([{2:1}, {0:1}, {1:1}])
rhs5 = (act(phi2,L) + tensor(n,{(0,1,2):1,(0,2,2):1,
                               (1,2,0):1,(1,2,2):1,(2,1,0):-1})
        + act(phi4,P23) + act(phi3,Pcycle.inverse()))
report["checks"].append({"calculation":"printed phi5 decomposition",
                         "pass":rhs5 == phi5,
                         "difference":list(rhs5-phi5)})
opposite_phi5 = tensor(n,{(0,2,0):1,(1,1,2):1,(2,2,2):-1})
assert rhs5 == -opposite_phi5
report["checks"].append({"calculation":"corrected tau(phi5)^-1 decomposition",
                         "pass":True})

for n in [3,4,5]:
    terms = [{(0,1,1):1}, {(0,1,2):1}, {(0,0,2):1,(1,1,2):-1},
             {(0,2,0):1,(1,2,1):-1},
             {(0,0,2):1,(1,2,1):1,(2,2,2):-1}]
    for F in [QQ, GF(2), GF(3), GF(5)]:
        rows=[]
        for p in permutations(range(n)):
            for t in terms:
                rows.append(tensor(n,{(p[i],p[a],p[b]):c
                                      for (i,a,b),c in t.items()},F))
        rank=matrix(F,rows).rank()
        report["checks"].append({"calculation":"permutation orbit span",
                                 "n":n,"field":str(F),"rank":rank,
                                 "printed_dimension":n**3-2*n})
        assert rank == n**3-2*n

def divergence(q,n,F=QQ):
    d=vector(F,2*n)
    for i in range(n):
        for a in range(n):
            for b in range(n):
                c=q[(i*n+a)*n+b]
                if a==i: d[b]+=c
                if b==i: d[n+a]+=c
    return d

for n in [3,4,5]:
    original=[]
    corrected=[]
    for i in range(n):
        p=list(range(n));p[0],p[i]=p[i],p[0]
        original += [divergence(tensor(n,{(p[0],p[0],p[1]):1}),n),
                     divergence(tensor(n,{(p[0],p[1],p[0]):1}),n)]
        p=list(range(n));p[1],p[i]=p[i],p[1]
        corrected += [divergence(tensor(n,{(p[0],p[0],p[1]):1}),n),
                      divergence(tensor(n,{(p[0],p[1],p[0]):1}),n)]
    assert matrix(QQ,original).rank()==4
    assert matrix(QQ,corrected).rank()==2*n
    report['checks'].append({'calculation':'last 2n representatives',
                            'n':n,'original_rank':4,'corrected_rank':2*n})

# A Vandermonde determinant with distinct admissible nonzero interpolation
# nodes; this verifies the denominator-clearing step in characteristic 2.
F = GF(8, "a")
nodes = list(F)[1:5]
V = matrix(F, [[r**j for j in range(4)] for r in nodes])
assert V.is_invertible()
report["checks"].append({"target":"lem:l2008-monic-vector-interpolation",
                         "field":"GF(8)","degree":3,"pass":True})

# Monic degree-2 substitutions compose by addition modulo words of degree 3.
# The example x+x^2 has degree 2d on every nonconstant univariate polynomial.
for F in [QQ,GF(2),GF(3)]:
    A=PolynomialRing(F,"x")
    x=A.gen()
    for d in range(1,9):
        g=x**d+x+1
        if not g.degree():
            continue
        assert g(x+x*x).degree()==2*g.degree()
report["checks"].append({"target":"exm:l2008-monic-nonsurjective-endomorphism",
                         "fields":["QQ","GF(2)","GF(3)"],
                         "degrees":"1..8", "pass":True})
print(json.dumps(report,ensure_ascii=False,indent=2,default=str))
