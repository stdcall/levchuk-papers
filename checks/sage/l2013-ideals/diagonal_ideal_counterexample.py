"""Main Theorem and Theorem1.1: exact D-invariant ideal counterexample.

Printed1250140-2,4: R2(F3[epsilon]/epsilon²,(epsilon)), whose residue
field has order3 and principal radical has nilpotence degree2.
Enumerate every F3-linear subspace; the ground field is prime,
so every additive subgroup is such a subspace.
This refutes the universal printed count, not a classification for
arbitrary coefficient rings. The printed count remains a refuted assert.
"""
from sage.all import *
import json
F=GF(3);P=PolynomialRing(F,'z');z=P.gen();K=P.quotient(z**2,'epsilon');eps=K.gen()
V=VectorSpace(F,5)
positions=[(0,0,eps),(0,1,eps),(1,0,K.one()),(1,0,eps),(1,1,eps)]
basis=[]
for i,j,a in positions:
 M=zero_matrix(K,2);M[i,j]=a;basis.append(M)
def coords(M):
 return vector(F,[M[0,0].lift()[1],M[0,1].lift()[1],M[1,0].lift()[0],M[1,0].lift()[1],M[1,1].lift()[1]])
left=[matrix(F,[coords(M*b) for M in basis]) for b in basis]
right=[matrix(F,[coords(b*M) for M in basis]) for b in basis]
units=[u for u in K if u.is_unit()]
assert len(K)==9 and len(units)==6 and eps**2==0 and eps!=0
def action(u):
 d=diagonal_matrix(K,[u,K.one()]);return matrix(F,[coords(d*M*d.inverse()) for M in basis])
generators=[action(K(2)),action(1+eps)]
count=coordinate=examined=0
counterexamples=[]
for dim in range(6):
 for W in V.subspaces(dim):
  examined+=1
  if all(v*A in W for A in left+right+generators for v in W.basis()):
   count+=1
   axis=[v for v in V.basis() if v in W]
   if V.subspace(axis)==W:coordinate+=1
   else:counterexamples.append([list(map(int,v)) for v in W.basis()])
H=V.subspace([V.basis()[0]+V.basis()[4],V.basis()[3]])
assert H.dimension()==2
assert all(v*A in H for v in H.basis() for A in left+right)
assert all(v*action(u) in H for v in H.basis() for u in units)
assert V.basis()[0] not in H and V.basis()[4] not in H
# Formula(1), n=2,s=2, and Example1.3 print eight.
n=s=2
printed=(2*s*n-s-3*n+1)*binomial(2*n-2,n-1)-QQ(4)/n*binomial(2*n,n-2)+2**(2*n-1)
assert printed==8
assert count!=printed
assert count==12 and coordinate==8 and examined==2664,(count,coordinate,examined)
print(json.dumps(dict(sage=version(),coefficient_ring='F3[epsilon]/epsilon²',radical_degree=2,residue_order=3,ring_order=3**5,subspaces_examined=examined,D_invariant_ideals=count,coordinate_ideals=coordinate,printed_refuted_count=int(printed),noncoordinate_ideals=counterexamples,explicit_H='F3 epsilon I2 + F3 epsilon e21'),indent=2))
print('ok l2013-ideals: exact counterexample, all2664subspaces; printed8 refuted by12')
