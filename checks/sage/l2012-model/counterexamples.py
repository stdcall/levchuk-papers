"""Two concrete obstructions, without a general replacement theorem.
Passages: th:l2012-model-semilocal-normal-form, lem:l2012-model-unit-adjunction.
"""
from sage.all import *
import json
F=GF(2); I=identity_matrix(F,3)
s=matrix(F,[[0,1,0],[1,0,0],[0,0,1]])
B=[matrix(F,[[1,a,b],[0,1,c],[0,0,1]]) for a in F for b in F for c in F]
Ws=[matrix(F,3,3,lambda i,j:int(j==perm[i])) for perm in Permutations(range(3))]
cells=[]
for n in Ws:
 cell={tuple((b*n*c).list()) for b in B for c in B}
 cells.append(cell)
assert sum(tuple(I.list()) in c and tuple(s.list()) in c for c in cells)==0
G=SL(3,F)
assert len(set.union(*cells))==G.order()==168
Z4=Integers(4); P=PolynomialRing(F,'x'); x=P.gen(); D=P.quotient(x*x,'e');e=D.gen()
K4=[Z4(0),Z4(2)];KD=[D(0),e]
assert all(a*b==0 for a in K4 for b in K4)
assert all(a*b==0 for a in KD for b in KD)
assert Z4.cardinality()==D.cardinality()==4
assert Z4.characteristic()==4 and D.characteristic()==2
assert len(K4)==len(KD)==2
out=dict(passed=True,bruhat=dict(type='A2',ring='GF(2) × GF(2)',radical_zero=True,group='SL3, hence adjoint center trivial over GF2',single_field_group_order=168,cell_sizes=[len(c) for c in cells],mixed_element='(I,s_alpha)',same_cell_membership=False),unit_adjunction=dict(base_ring='C2 with zero multiplication',extensions=['Z/4','GF2[e]/e²'],cardinalities=[4,4],characteristics=[4,2],quotient_indices=[2,2],minimality='Index1 would make the nonzero zero-multiplication ring unital, impossible',isomorphic=False))
print(json.dumps(out))
