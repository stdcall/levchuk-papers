"""Exact identities used in repairing Lemma3.8, not an all-rank classification.
The symbolic quotient has square-zero epsilon over ZZ[d,c,u]. It checks
the stated commutators in an arbitrary square-zero layer. Z/27 supplies
a counterexample to two intermediate printed assertions while 2 is a unit.
"""
from sage.all import *
import json

def adj(a,b):return a+b+a*b
def inv(a):return (identity_matrix(a.base_ring(),a.nrows())+a).inverse()-1
def comm(a,b):return adj(adj(adj(inv(a),inv(b)),a),b)

P=PolynomialRing(ZZ,names=('d','c','u','eps'))
d,c,u,eps=P.gens()
S=P.quotient(P.ideal(eps**2),names=('d','c','u','eps'))
d,c,u,eps=S.gens()
A=matrix(S,[[d*eps,c*eps],[0,-d*eps]])
E=matrix(S,[[0,0],[1,0]])
I=identity_matrix(S,2)
def layer_comm(X,Y):
    # X is a scalar multiple of E; Y has square zero, including its layer.
    assert X*X==0 and Y*Y==0
    return (I-X)*(I-Y)*(I+X)*(I+Y)-I
B=layer_comm(u*E,A)
assert B==matrix(S,[[-u*c*eps,0],[(2*u*d+u*u*c)*eps,u*c*eps]])
assert layer_comm(E,B)==-2*u*c*eps*E
assert B[1,0] != 0

F=PolynomialRing(QQ,names=('x','y','ell','p','b','delta')).fraction_field()
x,y,ell,p,b,delta=F.gens()
topright=((1+x*ell)*(1+delta)-x*ell*p*b-1)/(x*ell*ell)
B3=matrix(F,[[1+x*ell,x*p,topright],[0,1,b],
             [x*ell*ell,x*ell*p,1+delta]])
assert B3.det()==1 and B3.inverse()[2,2]==1+x*ell
E13=zero_matrix(F,3);E13[0,2]=1
Gamma=comm(y*E13,B3.inverse()-1)
expected=x*y*ell*(2+(x-y)*ell-x*y*ell*ell)
assert Gamma[0,2]==expected
assert Gamma[2,2]==x*y*ell*ell*(1+x*ell)
E32=zero_matrix(F,3);E32[2,1]=1
E31=zero_matrix(F,3);E31[2,0]=1
C=comm(E32,inv(Gamma))
assert C==Gamma[2,2]*E32+Gamma[0,2]*matrix(F,[[0,1,0],[0,0,0],[0,0,0]])
assert comm(C,E31)==-Gamma[0,2]*E32

R=Integers(27);E=lambda n,i,j:matrix(R,n,n,lambda a,b:1 if (a,b)==(i,j) else 0)
alpha=E(2,1,0);x=R(3);y=R(3)
beta=comm(x*E(2,0,1),alpha)
barbeta=adj(adj(E(2,1,0),beta),-E(2,1,0))
assert barbeta==matrix(R,[[3,9],[3,6]])
gamma=comm(y*E(2,0,1),inv(barbeta))
assert gamma==matrix(R,[[18,18],[0,9]])
assert 2*R(14)==1
assert R(3)**3==0 and R(3)**2!=0
first=comm(E(2,1,0),gamma)
assert first==matrix(R,[[9,0],[0,18]])
double=comm(E(2,1,0),first)
assert double==18*E(2,1,0)
beta2=comm(x*E(2,0,1),2*alpha)
barbeta2=adj(adj(2*E(2,1,0),beta2),-2*E(2,1,0))
gamma2=comm(y*E(2,0,1),inv(barbeta2))
first2=comm(E(2,1,0),gamma2)
assert gamma2==matrix(R,[[18,9],[0,9]])
assert first2==matrix(R,[[18,0],[18,9]])
assert gamma[0,0]!=0 and gamma[1,1]!=0

payload={'symbolic_checks':8,'square_zero_layer':str(S),
         'gamma_upper_coefficient':str(expected),
         'printed_base_counterexample':{'K':'Z/27','J':'3K','n':2,'H':'entire adjoint group',
          'alpha':'e21','x':3,'y':3,'nilpotency_index':3,
          'two_inverse':14,'gamma':[[18,18],[0,9]],
          'first_commutator':[[9,0],[0,18]],'second_commutator':'18e21',
          'alpha2_gamma':[[18,9],[0,9]],'alpha2_first_commutator':[[18,0],[18,9]]},
         'scope':'Polynomial identities in a square-zero quotient, one explicit Z/27 example; the all-ring J-adic induction is a written argument, not a finite enumeration.'}
print(json.dumps(payload,ensure_ascii=False,indent=2))
