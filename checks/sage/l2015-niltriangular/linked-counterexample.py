"""Refute Lemma 4.6 and formula (7) for NT(6,GF(2)), pp.43–45.

Every hypothesis and every ambient Lie bracket is checked. The quotient
construction counts all ideals with the staircase ((2,1),(4,3),(6,5))
over GF(2), GF(3), GF(4), GF(5) independently of printed formula (7).
"""
from sage.all import GF, VectorSpace, matrix, PolynomialRing, ZZ
import json
checks=0
def check(c):
    global checks
    assert c
    checks+=1
n=6; F=GF(2); ps=[(i,j) for i in range(1,n+1) for j in range(1,i)]
V=VectorSpace(F,len(ps)); ix={p:k for k,p in enumerate(ps)}
def e(i,j): return V.basis()[ix[i,j]]
def mul(a,b):
    return V([sum(a[ix[i,k]]*b[ix[k,j]] for k in range(j+1,i)) for i,j in ps])
corners=((2,1),(4,3),(6,5))
support=[p for p in ps if any(p[0]>=i and p[1]<=j for i,j in corners)]
qps=[p for p in support if p not in corners]
wps=[(3,1),(4,2),(5,3),(6,4)]
base=[p for p in qps if p not in wps]
Q=V.subspace([e(*p) for p in qps])
alpha=e(2,1)+e(4,3)+e(6,5)
beta2=e(3,1)+e(4,2); beta4=e(5,3)+e(6,4)
gamma=e(3,1)+e(5,3)
H=V.subspace([e(*p) for p in base]+[alpha,beta2,beta4,gamma])
check(H.dimension()==10)
check(all(mul(a,b)-mul(b,a) in H for a in H.basis() for b in V.basis()))
check(all(any(a[ix[p]] for a in H.basis()) for p in corners))
check(all(not any(a[ix[p]] for a in H.basis()) for p in ps if p not in support))
observed_corners=tuple(p for p in support
    if any(a[ix[p]] for a in H.basis()) and not any(
        t!=p and p[0]>=t[0] and p[1]<=t[1]
        and any(a[ix[t]] for a in H.basis()) for t in support))
check(observed_corners==corners)
Qstar=V.subspace([e(*p) for p in qps if e(*p) in H])
check(Qstar.dimension()==6)
check(all(e(*p) not in H for p in wps))
check(gamma in Q.intersection(H))
check(gamma not in Qstar+V.subspace([beta2,beta4]))
check(Q.intersection(H).dimension()==9)
check((Qstar+V.subspace([beta2,beta4])).dimension()==8)
check(Q not in [Q.intersection(H)])
print(json.dumps({'counterexample':{'field':2,'n':6,'corners':corners,
 'dimH':int(H.dimension()),'dimQstar':int(Qstar.dimension()),
 'dimQinterH':int(Q.intersection(H).dimension()),'printed_span_dimension':8}},ensure_ascii=False))

out=[]
for order in (2,3,4,5):
    K=GF(order); A=VectorSpace(K,3); W=VectorSpace(K,4); total=0
    for t in range(1,4):
        for S in A.subspaces(t):
            if not all(any(a[i] for a in S.basis()) for i in range(3)): continue
            image=W.subspace([W([a[0],-a[1],0,0]) for a in S.basis()]
                           +[W([0,0,a[1],-a[2]]) for a in S.basis()])
            # Central kernel N may mix the two exceptional coordinate pairs.
            for d in range(image.dimension(),5):
                for N in W.subspaces(d):
                    if image.is_subspace(N): total+=order**(t*(4-d))
    expected=2*order**4-order**3
    check(total==expected)
    printed=order**4
    check(total!=printed)
    binomial_repair=order**4+2*order**3-3*order**2+order
    check(total-binomial_repair==order*(order-1)**3)
    out.append({'q':order,'all_fixed_staircase_ideals':total,
                'printed_formula':printed,'binomial_only':binomial_repair})
print(json.dumps({'staircase_counts':out,'checks':checks},ensure_ascii=False))
P4=[(i,j) for i in range(1,5) for j in range(1,i)]
V4=VectorSpace(GF(2),len(P4));ix4={p:k for k,p in enumerate(P4)}
def e4(i,j):return V4.basis()[ix4[i,j]]
def mul4(a,b):
    return V4([sum(a[ix4[i,k]]*b[ix4[k,j]] for k in range(j+1,i)) for i,j in P4])
H4=V4.subspace([e4(4,1),e4(2,1)+e4(4,3),e4(3,1)+e4(4,2)])
check(H4.dimension()==3)
check(all(mul4(a,b)-mul4(b,a) in H4 for a in H4.basis() for b in V4.basis()))
check(e4(2,1)+e4(4,3) in H4)
check(e4(4,3) not in H4)
check(e4(3,1) not in H4 and e4(4,2) not in H4)
check(any(v[ix4[2,1]] for v in H4.basis()) and any(v[ix4[4,3]] for v in H4.basis()))
check(all(not any(v[ix4[p]] for v in H4.basis()) for p in P4 if p not in
      [(2,1),(3,1),(4,1),(4,2),(4,3)]))
print(json.dumps({'remainder_counterexample':{'q':2,'n':4,'dimH':3,
                   'alpha_in_H':True,'alpha_prime_in_H':False},'checks':checks}))
print(f'ok l2015-niltriangular linked counterexample: {checks} checks')
