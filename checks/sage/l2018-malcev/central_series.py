"""Exact bounded Lie central-series checks from signed root matrices.

Passages: lem:l2018-malcev-centralizers,
lem:l2018-malcev-hypercenters, lem:l2018-malcev-b-c-distinction.
Checks the corrected Lemmas 3/5/6 over small fields, not the isomorphism
classification or the model-theoretic transfer theorem.
"""
from sage.all import *
import json
count=0;fail=[]
def ck(name,a,b):
 global count
 count+=1
 if a!=b:fail.append({'check':name,'observed':str(a),'expected':str(b)})
def run(kind,n,q):
 F=GF(q);ids=list(range(n,0,-1))+([0] if kind=='B' else [])+list(range(-1,-n-1,-1));pos={x:i for i,x in enumerate(ids)};d=len(ids)
 def E(i,j):
  a=matrix(F,d);a[pos[i],pos[j]]=1;return a
 labels=[];eps=[];heights=[]
 for i in range(1,n+1):
  for j in range(1,i):
   labels.extend([(i,j),(i,-j)]);eps.extend([E(i,j)-E(-j,-i),(-E(i,-j)+E(j,-i)) if kind in ['B','D'] else E(i,-j)+E(j,-i)]);heights.extend([i-j,i+j-({'B':0,'C':1,'D':2}[kind])])
  if kind=='B':labels.append((i,0));eps.append(E(i,0)-2*E(0,-i));heights.append(i)
  elif kind=='C':labels.append((i,-i));eps.append(E(i,-i));heights.append(2*i-1)
 V=VectorSpace(F,len(labels));basis=V.basis();pivots=[next((u,v,A[u,v]) for u in range(d) for v in range(d) if A[u,v]) for A in eps]
 def coords(A):
  z=V([A[u,v]/a for u,v,a in pivots]);assert sum((z[k]*eps[k] for k in range(len(eps))),matrix(F,d))==A;return z
 br=[[coords(A*B-B*A) for B in eps] for A in eps]
 def span_indices(f):return V.subspace([basis[k] for k,x in enumerate(labels) if f(x,k)])
 L=lambda h:span_indices(lambda x,k:heights[k]>=h)
 R=lambda j:span_indices(lambda x,k:x[1]==0 and x[0]>=j)
 L0=lambda j:span_indices(lambda x,k:0<=x[1]<x[0] and x[0]-x[1]>=j)
 A2=F(2)==0
 T=lambda i,m:span_indices(lambda x,k:x[0]>=i and x[1]<=m)
 for i in range(1,n+1):
  for m0 in range(-i,i):
   if kind=='D' and (m0==0 or abs(m0)==i):continue
   if kind=='B' and m0==-i:continue
   t=T(i,m0)
   if not t.dimension():continue
   m=matrix(F,len(t.basis())*V.dimension(),V.dimension(),[sum(v[k]*br[j][k][r] for k in range(V.dimension())) for v in t.basis() for r in range(V.dimension()) for j in range(V.dimension())])
   observed=V.subspace(m.right_kernel().basis());expected=T(1,-m0-1)
   if kind=='B' and m0>=0 and A2:expected+=R(m0+1)
   if i==n and (kind!='C' or A2):expected+=T(n,n-1)
   ck(f'{kind}{n}/GF{q}/C(T{i},{m0})',observed,expected)
 if kind=='D':return
 z=V.subspace([]);g=V;upper=[];lower=[g]
 for h in range(1,2*n):
  quot=V.quotient(z)
  # Stack the maps ad(e_j), with input-coordinate columns.
  m=matrix(F,V.dimension()*quot.dimension(),V.dimension(),[quot(br[i][j])[r] for j in range(V.dimension()) for r in range(quot.dimension()) for i in range(V.dimension())])
  z=V.subspace(m.right_kernel().basis());upper.append(z)
  if kind=='C':expected=L(2*n-h)+(L(2*n-h-1) if A2 else V.subspace([]))
  elif h<=n-2:expected=L(2*n-h)+(R(n+1-h) if A2 else V.subspace([]))
  elif h==n-1:expected=L(n+1)+(R(2)+span_indices(lambda x,k:x==(n,1) and n>2) if A2 else V.subspace([]))
  elif n<=h<=2*n-3:expected=L(2*n-h)+(R(1)+L0(2*n-h-2) if A2 else V.subspace([]))
  elif h==2*n-2:expected=L(2)+(L(1) if A2 else V.subspace([]))
  else:expected=V
  ck(f'{kind}{n}/GF{q}/Z{h}',z,expected)
  g=V.subspace([sum((v[i]*br[j][i] for i in range(V.dimension())),V.zero()) for v in g.basis() for j in range(V.dimension())]);lower.append(g)
  i=h+1
  if kind=='C' and i<2*n:
   expected=span_indices(lambda x,k:heights[k]>=i and abs(x[1])<x[0])
   if not A2:expected+=span_indices(lambda x,k:x[1]==-x[0] and 2*x[0]>i)
   ck(f'{kind}{n}/GF{q}/Gamma{i}',g,expected)
  if kind=='B' and 2<=i<=n and n>2:
   expected=L0(i)+L(i+2)+(L(i) if not A2 else V.subspace([]));ck(f'{kind}{n}/GF{q}/Gamma{i}',g,expected)
 if n>=3 and A2:ck(f'{kind}{n}/centre-in-derived',upper[0].is_subspace(lower[1]),kind=='B')
for kind in ['B','C']:
 for n in range(2,6):
  for q in [2,3,5]:run(kind,n,q)
for n in [4,5]:
 for q in [2,3,5]:run('D',n,q)
# Cartan denominator diagnostic: C2 long r=2ε2, short s=ε2−ε1.
ck('Cartan corrected integer',2*2/2,2);ck('Cartan printed value',2*2/4,1)
E=lambda i,j:matrix(QQ,4,4,{(i,j):1})
H=E(0,0)-E(1,1)+E(2,2)-E(3,3);long=E(0,3)
ck('C2 actual Cartan bracket',H*long-long*H,2*long)
out={'checks':count,'failures':fail,'scope':'B2..B5/C2..C5 Lie upper/lower central series over GF2/GF3/GF5; actual signed matrices; no universal classification certificate'}
print(json.dumps(out,indent=2))
assert not fail, fail
