from sage.all import ZZ, Zmod, matrix, identity_matrix
from itertools import product

rows=[]
# Exact ideal arithmetic in Z/p^m: exponent m denotes the zero ideal.
for n in range(2,7):
 for p,m,d in [(2,2,1),(2,3,1),(2,4,2),(3,2,1)]:
  v=[[0 if i>j else d for j in range(n)] for i in range(n)]
  power=v
  for k in range(1,n*m+1):
   s,t=divmod(k,n)
   expected=[[min(m,d*(s+(i-j<t)+(i-j<t-n))) for j in range(n)] for i in range(n)]
   assert power==expected
   # Independently computed left/right annihilator coefficient thresholds.
   left=[[m-min(power[j]) for j in range(n)] for i in range(n)]
   right=[[m-min(power[r][i] for r in range(n)) for j in range(n)] for i in range(n)]
   lp=[[max(0,m-d*(s+(j<t))) for j in range(n)] for i in range(n)]
   rp=[[max(0,m-d*(s+(i>=n-t))) for j in range(n)] for i in range(n)]
   assert left==lp and right==rp
   rows.append(dict(n=n,p=p,m=m,d=d,k=k,power=True,left_ann=True,right_ann=True))
   power=[[min(m,min(power[i][r]+v[r][j] for r in range(n))) for j in range(n)] for i in range(n)]
# A concrete original-Lemma1.3 counterexample, including actual multiplication.
F=Zmod(2)
x=matrix(F,3,3,{(1,0):1});y=matrix(F,3,3,{(2,1):1})
assert y*x==matrix(F,3,3,{(2,0):1}) and y*x!=0

# All almost-annihilator parameter maps over K=Z/4, J=2K, n=2.
K=Zmod(4); J=[K(0),K(2)]
elems=[matrix(K,2,2,[a,b,c,d]) for a,b,c,d in product(J,J,list(K),J)]
def am(c,v):return K(int(c)*(int(v)//2))
maps=[]
for l,u,s in product(J,J,J):
 def f(v):
  a,b,c,d=v.list()
  return matrix(K,2,2,[a+am(l,b),b,c+am(s,b)+am(l,d)+am(u,a),d+am(u,b)])
 conditions=True
 for y,z in product(J,J):
  conditions &= y*am(u,z)==-am(l,y)*z
  conditions &= am(s,z*y)==am(u,z)*am(l,y)
  conditions &= am(u,y)*am(s,z)+am(s,y)*am(l,z)==0
  conditions &= y*am(s,z)+am(l,y)*am(l,z)==0
  conditions &= am(s,y)*z+am(u,y)*am(u,z)==0
 for x,y in product(list(K),J):
  conditions &= am(l,x*y)==x*am(l,y)
  conditions &= am(u,y*x)==am(u,y)*x
 if not conditions: continue
 for x,y in product(elems,elems):
  assert f(x+y)==f(x)+f(y)
  assert f(x*y)==f(x)*f(y)
 assert len({tuple(f(x).list()) for x in elems})==len(elems)
 maps.append(dict(lambda_image=int(l),mu_image=int(u),sigma_image=int(s),elements=len(elems),pairs=len(elems)**2,bijective=True))
assert len(maps)==8
print('PASS',len(rows),'ideal checks;',len(maps),'maps,',sum(q['pairs'] for q in maps),'pairs')
