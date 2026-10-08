"""Counterexample to printed96 Theorem1's arbitrary exact-envelope scope.

The polynomial identity over ZZ proves the concrete deformed multiplication
associative over every commutative base ring and leaves the Lie bracket exact.
GF2 exhausts all64 elements and separates the isomorphism classes by x²=0.
It does not give a replacement classification theorem.
"""
import json
from itertools import product
from sage.all import ZZ,GF,PolynomialRing,matrix,zero_matrix

positions=[(i,j) for i in range(4) for j in range(i)]
P=PolynomialRing(ZZ,18,'t');v=P.gens()
def lower(F,values):
    X=zero_matrix(F,4)
    for pos,a in zip(positions,values):X[pos]=a
    return X
def central(F):
    X=zero_matrix(F,4);X[3,0]=1;return X
def star(X,Y):return X*Y+X[2,1]*Y[2,1]*central(X.base_ring())
X,Y,Z=[lower(P,v[i:i+6]) for i in [0,6,12]]
assert star(star(X,Y),Z)==star(X,star(Y,Z))
assert star(X,Y)-star(Y,X)==X*Y-Y*X
# These printed-definition hypotheses are checked on the actual matrix space.
assert all(star(X,Y)[i,j]==0 for i in range(4) for j in range(i,4))
F=GF(2);allX=[lower(F,u) for u in product(F,repeat=6)]
ordinary=sum(A*A==0 for A in allX)
deformed=sum(star(A,A)==0 for A in allX)
assert len(allX)==64 and ordinary==28 and deformed==20
for A,B in product(allX,repeat=2):
    assert star(A,B)-star(B,A)==A*B-B*A
basis=[lower(F,[int(i==j) for i in range(6)]) for j in range(6)]
for A,B,C in product(basis,repeat=3):
    assert star(star(A,B),C)==star(A,star(B,C))
assert sum(A*A==0 for A in allX)==ordinary  # Opposite product has same square.
E32=lower(F,[0,0,1,0,0,0])
assert E32*E32==0 and star(E32,E32)==central(F)
print(json.dumps({'status':'PASS','source':'printed96 Theorem1, n4 overGF2',
 'generic_polynomial_associativity_ZZ18':True,'generic_same_matrix_Lie_bracket':True,
 'GF2_elements':64,'all_GF2_commutator_pairs':4096,
 'GF2_basis_associator_triples':216,
 'ordinary_square_zero':ordinary,'deformed_square_zero':deformed,
 'nonisomorphism_reason':'Any algebra/ring isomorphism is bijective and preserves x²=0; opposite product has identical square counts.',
 'limits':'concrete arbitrary exact-envelope counterexample; no corrected classification'},indent=2))
