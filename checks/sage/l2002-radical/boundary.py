"""An exact rank-four test of the final inference in Lemma 2.6."""
from sage.all import *
import json
n=4;modulus=9
e=lambda i,j:matrix(ZZ,n,n,lambda u,v:int((u,v)==(i,j)))
ring_basis=[(1 if i>j else 3)*e(i,j) for i in range(n) for j in range(n)]
alpha=e(2,1)+3*e(0,3)
ambient=FreeModule(ZZ,16)
H=ambient.span([9*v for v in ambient.basis()]+[vector(ZZ,alpha.list())])
steps=0
while True:
    vs=list(H.basis())
    for v in H.basis():
        a=matrix(ZZ,n,n,v)
        for b in ring_basis:vs.append(vector(ZZ,(a*b-b*a).list()))
    H2=ambient.span(vs)
    steps+=1
    if H2==H:break
    H=H2
projection_gcd=[[int(gcd([9]+[v[i*n+j] for v in H.basis()])) for j in range(n)] for i in range(n)]
primary=[(i,j) for i in range(n) for j in range(n) if i!=j and projection_gcd[i][j]==1]
secondary=[(i,j) for i in range(n) for j in range(n) if i!=j and projection_gcd[i][j]==3]
order=lambda p,q:p[0]>=q[0] and p[1]<=q[1]
Lc=[p for p in primary if not any(order(p,q) and p!=q for q in primary)]
Lp_candidates=[p for p in secondary if all(p[0]<q[0] and p[1]>q[1] for q in Lc)]
Lp=[p for p in Lp_candidates if not any(order(p,q) and p!=q for q in Lp_candidates)]
assert Lc==[(2,1)] and Lp==[(0,3)]
tilde_L={(2,1),(3,1),(2,0),(3,0)}
tilde_Lp={(0,3)}
phi_plus=alpha[2,1]*e(2,0)-alpha[0,3]*e(1,3)+alpha[3,1]*e(3,0)-alpha[0,2]*e(1,2)
phi_minus=alpha[2,1]*e(3,1)-alpha[0,3]*e(0,2)+alpha[2,0]*e(3,0)-alpha[1,3]*e(1,2)
allowed=tilde_L|tilde_Lp|{(i,i) for i in range(n)}
outside=lambda a:[(i+1,j+1,int(a[i,j]%9)) for i in range(n) for j in range(n) if (i,j) not in allowed and a[i,j]%9]
assert vector(ZZ,phi_plus.list()) in H
assert vector(ZZ,phi_minus.list()) in H
assert outside(phi_plus) and outside(phi_minus)
print(json.dumps({'sage_version':version(),'ring':'Z/9','J':'3K','n':4,
 'generator':'e32+3e14','closure_steps':steps,'primary_corners':[(3,2)],'secondary_corners':[(1,4)],
 'phi_plus_in_H':True,'phi_minus_in_H':True,'phi_plus_outside_A':outside(phi_plus),
 'phi_minus_outside_A':outside(phi_minus),
 'scope':'One exact finite-rank counterexample to membership in A; preceding identities prove membership in the Lie closure of A.'},indent=2))
import sys
print("ok l2002-radical boundary: two closure-membership checks and "
      "two refuted boundary-membership checks", file=sys.stderr)
