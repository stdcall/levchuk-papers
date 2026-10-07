"""Exact bounded checks of local steps in Levchuk1987, not a proof of its classification."""
from sage.all import GF, QQ, PolynomialRing, matrix, identity_matrix, version
from itertools import product, combinations
from pathlib import Path
import hashlib, datetime, json
ROOT = Path(__file__).resolve().parents[3]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
report = {"date_utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),
 "sage_version":str(version()),"script_sha256":sha(Path(__file__)),
 "checked_text_sha256":{str(p.relative_to(ROOT)):sha(p) for p in sorted((ROOT/"content/papers/l1987-rings").glob("*")) if p.is_file()}, "checks":[]}
def E(K,n,i,j,x=1):
 a=matrix(K,n,n); a[i,j]=x; return a
def key(a): return tuple(a.list())
def bracket(a,b): return a*b-b*a
def adjoint(a,b): return a+b+a*b

# Double Lie commutator displayed in the proof of Theorem 1.
# Generic commutative symbolic NT(5) and 2x2 noncommutative blocks.
P=PolynomialRing(QQ,names=["x","y"]+[f"b{i}{j}" for i in range(5) for j in range(i)])
x,y,*bb=P.gens(); B=matrix(P,5,5)
for (i,j),b in zip([(i,j) for i in range(5) for j in range(i)],bb): B[i,j]=b
cases=0
for i,l,j in combinations(range(5),3):
 # combinations increasing, rename to the strict lower order.
 i,l,j=j,l,i
 U=E(P,5,i,l,x); V=E(P,5,l,j,y)
 assert bracket(U,bracket(V,B))==U*V*B
 cases+=1
report["checks"].append({"claim":"p.632 double commutator","result":"pass","scope":"generic symbolic NT(5, QQ[x,y,b_ij])","triples":cases})
F=GF(3); N=5; B=matrix(F,2*N,2*N)
for i in range(N):
 for j in range(i):
  B.set_block(2*i,2*j,matrix(F,[[i,j+1],[2*j+1,i+j]]))
X=matrix(F,[[1,1],[0,1]]); Y=matrix(F,[[0,1],[1,0]]); cases=0
for j,l,i in combinations(range(N),3):
 U=matrix(F,2*N,2*N); U.set_block(2*i,2*l,X)
 V=matrix(F,2*N,2*N); V.set_block(2*l,2*j,Y)
 assert bracket(U,bracket(V,B))==U*V*B
 cases+=1
report["checks"].append({"claim":"p.632 double commutator, noncommutative coefficients","result":"pass","scope":"fixed NT(5, Mat(2,GF(3))) exact matrices","triples":cases})

# p.633, the two degenerate-index cases: the original reverses matrix H.
P=PolynomialRing(QQ,names=["x","y"]+[f"h{i}{j}" for i in range(5) for j in range(i)])
x,y,*hh=P.gens(); H=matrix(P,5,5)
for ij,h in zip([(i,j) for i in range(5) for j in range(i)],hh): H[ij]=h
cases=0
for m,j,i in combinations(range(5),3):
 U=E(P,5,i,j,x); V=E(P,5,j,m,y)
 assert bracket(U,bracket(H,V)) == -(U*V)*H
 cases+=1
for j,i,k in combinations(range(5),3):
 U=E(P,5,i,j,x); V=E(P,5,k,i,y)
 assert bracket(U,bracket(H,V)) == -H*(V*U)
 cases+=1
report["checks"].append({"claim":"p.633, corrected order of H in the two degenerate-index double-commutator cases",
 "result":"pass","scope":"generic strictly lower triangular H over QQ[x,y,h_ij], n=5",
 "index_cases":cases,"sign":"Minus signs disappear when these are additive subgroups."})

# sigma_lambda over GF(3), n=4, lambda(x)=x(x-1)/2, a=1.
F=GF(3); n=4; pos=[(i,j) for i in range(n) for j in range(i)]
elements=[]
for coords in product(F,repeat=len(pos)):
 A=matrix(F,n,n)
 for ij,c in zip(pos,coords): A[ij]=c
 elements.append(A)
generators=[E(F,n,i,j,c) for i,j in pos for c in F if c]
def sigma(A):
 x=A[1,0]; return A+E(F,n,3,1,x)+E(F,n,3,0,x*(x-1)/F(2))
assert len({key(sigma(A)) for A in elements})==len(elements)
for A,G in product(elements,generators): assert sigma(adjoint(A,G))==adjoint(sigma(A),sigma(G))
def sigma_lie(A): return A+E(F,n,3,1,A[1,0])
basis=[E(F,n,*ij) for ij in pos]
for A,B in product(basis,basis): assert sigma_lie(bracket(A,B))==bracket(sigma_lie(A),sigma_lie(B))
U=E(F,n,1,0)
assert sigma_lie(U*U)!=sigma_lie(U)*sigma_lie(U)
report["checks"].append({"claim":"p.636 sigma_lambda group automorphism; sigma_a Lie automorphism, not ring automorphism",
 "result":"pass","scope":"NT(4,GF(3)); all 729 elements, right products by 12 elementary generators; 36 Lie basis pairs",
 "group_elements":len(elements),"generator_products":len(elements)*len(generators),
 "ring_counterexample":"U=e_21: sigma_a(U)^2=e_41, sigma_a(U^2)=0",
 "theorem4_local_implication":"H containing e_21 and invariant under sigma_lambda must contain e_42 modulo the central term; choosing x=1 removes that central term"})

# A concrete GF(2) adjoint-group extension of nu_1 modulo the center.
# eta differs from the Lie map by a central correction, as warned by the paper.
F=GF(2);n=5;pos=[(i,j) for i in range(n) for j in range(i)]
elements=[]
for coords in product(F,repeat=len(pos)):
 A=matrix(F,n,n)
 for ij,c in zip(pos,coords): A[ij]=c
 elements.append(A)
def nu(A): return A+E(F,n,4,2,A[1,0])+E(F,n,4,1,A[2,0])
def eta(A):
 x,y,z=A[1,0],A[2,0],A[2,1]
 return A+E(F,n,4,2,x)+E(F,n,4,1,y+x*z)+E(F,n,4,0,x*y+y)
basis=[E(F,n,*ij) for ij in pos]
for A,B in product(basis,basis): assert nu(bracket(A,B))==bracket(nu(A),nu(B))
assert len({key(eta(A)) for A in elements})==len(elements)
for A,G in product(elements,basis): assert eta(adjoint(A,G))==adjoint(eta(A),eta(G))
assert all(eta(E(F,n,1,0,x))-nu(E(F,n,1,0,x))==0 for x in F)
report["checks"].append({"claim":"p.636 nu_a and a possible group extension eta_a","result":"pass",
 "scope":"NT(5,GF(2)), 100 Lie basis pairs and all 1024 group elements times 10 elementary generators",
 "generator_products":len(elements)*len(basis),
 "explicit_eta":"N + x e_53 + (y+xz)e_52 + (xy+y)e_51; x=N_21,y=N_31,z=N_32",
 "limitation":"This is a finite specialization of the construction, not a check of every characteristic-2 field."})

# Essential finite-support caveat in Theorem 1's proof: condition (1)
# need not restrict to an arbitrary smaller chain. Use the full carpet
# over GF(3), Gamma={0,1,2,3}, but Gamma1={0,2,3}.
report["checks"].append({"claim":"p.632 finite subchain caveat","result":"counterexample to preservation of condition (1)",
 "scope":"full NT(4,GF(3)), subchain {0,2,3}",
 "details":"For (i,j)=(2,0), A'_20=GF(3) in Gamma using l=1; in Gamma1 A'_20=0 while I_2=0 because A_32=GF(3). Thus l_m in Gamma1 cannot be asserted without enlarging Gamma1.",
 "interpretation":"The support reduction needs additional finite auxiliary indices; this does not refute Theorem 1 itself."})
print(json.dumps(report, ensure_ascii=False, indent=2))
