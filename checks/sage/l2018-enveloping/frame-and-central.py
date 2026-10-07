from sage.all import *
import json
checks=0
def verify(x):
 global checks
 assert x
 checks+=1
# A1: the ring and Lie ring are one-dimensional with zero product.
F=GF(2)
assert (F.one()+F.one())==0
verify(matrix(F,1,1,[0]).rank()==0)
# B2: integral Chevalley constants 1 and 2; retain the integral
# orientation when reducing the ring multiplication modulo 2.
def bmul(x,y):
 return vector(F,[0,0,x[0]*y[1],x[0]*y[2]-x[2]*y[0]])
def bracket(x,y):return bmul(x,y)-bmul(y,x)
basis=list(identity_matrix(F,4).rows())
phi=identity_matrix(F,4);phi[1,2]=1
apply=lambda x:x*phi
verify(phi.det()!=0)
for x in basis:
 verify(all(bracket(basis[2],x)==0 for x in basis))
 verify(bracket(basis[3],x)==0)
 for y in basis:verify(apply(bracket(x,y))==bracket(apply(x),apply(y)))
verify(apply(bmul(basis[0],basis[1]))!=bmul(apply(basis[0]),apply(basis[1])))
verify(apply(basis[1])-basis[1]==basis[2])
# D4: construct an integral Chevalley basis in so(8) and compute every
# positive-root structure constant. Matrix units use +1..+4,-1..-4.
def unit(i,j):
 a=zero_matrix(ZZ,8);a[i,j]=1;return a
simple=matrix(QQ,[(1,-1,0,0),(0,1,-1,0),(0,0,1,-1),(0,0,1,1)])
rootmat={}
for i in range(4):
 for j in range(i+1,4):
  for sign in [-1,1]:
   v=vector(QQ,4);v[i]=1;v[j]=sign
   r=tuple(ZZ(t) for t in v*simple.inverse())
   rootmat[r]=unit(i,j)-unit(j+4,i+4) if sign==-1 else unit(i,j+4)-unit(j,i+4)
roots=sorted(rootmat,key=lambda r:(sum(r),r));idx={r:i for i,r in enumerate(roots)}
table={}
for r in roots:
 for s in roots:
  t=tuple(a+b for a,b in zip(r,s));C=rootmat[r]*rootmat[s]-rootmat[s]*rootmat[r]
  if t not in rootmat:verify(C.is_zero());continue
  X=rootmat[t];pos=next((i,j) for i in range(8) for j in range(8) if X[i,j])
  N=C[pos]/X[pos];verify(C==N*X);verify(abs(N)==1)
  table[idx[r],idx[s]]=(idx[t],F(1 if N>0 else 0))
V=VectorSpace(F,len(roots));E=list(V.basis())
def mul(x,y):
 z=vector(F,[0]*len(roots))
 for (i,j),(k,n) in table.items():z[k]+=x[i]*y[j]*n
 return z
def e(r):return E[idx[tuple(r)]]
def Q(r):return [E[idx[t]] for t in roots if t!=tuple(r) and all(a>=b for a,b in zip(t,r))]
def T(r):return [E[idx[t]] for t in roots if all(a>=b for a,b in zip(t,r))]
s=(0,0,1,0);bs=(0,0,0,1);s1=(0,1,1,0);b1=(0,1,0,1);s2=(1,1,1,0);b2=(1,1,0,1)
I=V.subspace(T((0,1,1,1))+Q(s2)+Q(b2)+[e(s1)+e(b1),e(s2)+e(b2)])
f=e(s)+e(bs);lift=f+e(s2);H=V.subspace(list(I.basis())+[lift])
for h in H.basis():
 for x in E:verify(mul(x,h) in H);verify(mul(h,x) in H)
verify(f not in H);verify(lift in H);verify(e(s2) not in I)
corners=[]
support=[r for r in roots if any(h[idx[r]] for h in H.basis())]
for r in support:
 if not any(t!=r and all(a<=b for a,b in zip(t,r)) for t in support):corners.append(r)
verify(set(corners)=={s,bs})
frame=V.subspace([vector(F,[h[i] if r in corners else 0 for i,r in enumerate(roots)]) for h in H.basis()])
verify(frame==V.subspace([f]))
ql=V.subspace(Q(s)+Q(bs));verify(H.intersection(ql)==I)
verify(V.subspace(list(H.basis())+list(ql.basis()))==V.subspace(list(frame.basis())+list(ql.basis())))
verify(not all(x in H for x in Q(s)));verify(not all(x in H for x in Q(bs)))
verify(not all(x in H for x in Q(s1)));verify(all(x in H for x in Q(s2)))
result={'sage':version(),'assertions':checks,'A1':{'field':'GF(2)','lambda':'identity=-identity','1+lambda_rank':0},'B2':{'field':'GF(2)','ordered_basis':['alpha','beta','alpha+beta','2alpha+beta'],'map':'e_beta -> e_beta+e_(alpha+beta)','Lie_automorphism':True,'ring_automorphism':False,'central_difference':'e_(alpha+beta)'},'D4':{'field':'GF(2)','simple_roots':'Bourbaki alpha1=e1-e2,alpha2=e2-e3,alpha3=e3-e4,alpha4=e3+e4','positive_roots':len(roots),'I_dimension':I.dimension(),'H_dimension':H.dimension(),'corners':corners,'frame_dimension':frame.dimension(),'frame_subset_H':False,'lift':'e_alpha3+e_alpha4+e_(alpha1+alpha2+alpha3)','two_sided_ideal_verified':True}}
print(json.dumps(result,ensure_ascii=False,indent=2,default=int))
