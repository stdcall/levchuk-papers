"""Bounded exact checks for Levchuk1974; no claim for all ranks or all fields."""
from sage.all import GF, matrix, identity_matrix, PolynomialRing, QQ, version
from itertools import product, combinations
from pathlib import Path
import hashlib, json, datetime

ROOT = Path(__file__).resolve().parents[3]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
checked = {str(p.relative_to(ROOT)): sha(p) for p in sorted((ROOT/'content/papers/l1974').glob('*')) if p.is_file()}
report = {'date_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
          'sage_version':str(version()), 'script_sha256':sha(Path(__file__)),
          'checked_text_sha256':checked, 'checks':[]}

# Equation (1): multiply elementary bases of the ring ideal. Positions alone
# decide this span, so no floating arithmetic and no random sampling.
cases = 0
for n in range(2, 9):
 for t in range(1,n):
  for size in range(1,t+1):
   for rr in combinations(range(1,t+1),size):
    R=set(rr); d=n-t
    basis={(i,j) for i in range(1,n+1) for j in range(1,i)
           if i-j>d or (i-j==d and j in R)}
    square={(i,l) for i,j in basis for k,l in basis if j==k}
    zero={(i,j) for i in range(1,n+1) for j in range(1,i)
          if 0<i-j<2*d or (i-j==2*d and (j not in R or i+t-n not in R))
          or (i-j==2*d+1 and j not in R and i+t-n not in R)}
    allpos={(i,j) for i in range(1,n+1) for j in range(1,i)}
    assert square == allpos-zero, (n,t,rr,square,zero)
    cases+=1
report['checks'].append({'claim':'Equation (1), ring-ideal elementary basis support',
                        'ranks':list(range(2,9)), 'nonempty_R_cases':cases,
                        'result':'pass', 'scope':'integer support combinatorics, not proof for arbitrary n'})

# Example 4: its displayed inclusion Z <= Y(X+Y) allows Z=0, which fails.
# The reversed inclusion contains precisely the missing cross term.
K=GF(8,'h'); h=K.gen(); z=K.zero(); one=K.one()
X=[z,one]; Y=[z,h]; T=[z,one,h*h,one+h*h]; Z=[z,h,h*h,h+h*h]
def elem(x,y,zv,t):
 return matrix(K,[[1,0,0,0],[x+y,1,0,0],[zv,y,1,0],[t+x*y,x+y,0,1]])
def key(a): return tuple(a.list())
assert set(X)&set(Y)=={z}
assert all(x*x2+y*y2 in T for x,x2,y,y2 in product(X,X,Y,Y))
assert h not in T
badH={key(elem(x,y,z,t)) for x,y,t in product(X,Y,T)}
badA=elem(z,h,z,z); badB=elem(one,z,z,z)
badproduct=badA*badB
assert key(badproduct) not in badH
H=[elem(x,y,zv,t) for x,y,zv,t in product(X,Y,Z,T)]
keys={key(a) for a in H}
assert len(keys)==64
for a,b in product(H,H): assert key(a*b) in keys
for a in H: assert key(a.inverse()) in keys
I=identity_matrix(K,4)
assert key(I+(badA-I)*(badB-I)) not in keys
report['checks'].append({'claim':'Example 4, corrected Z >= Y(X+Y)',
 'field':'GF(8)', 'modulus':str(K.modulus()), 'group_order':len(keys),
 'ordered_pairs':len(H)**2, 'inverses':len(H), 'result':'pass',
 'original_counterexample':{'Z':'{0}', 'left':str(badA), 'right':str(badB),
                           'product':str(badproduct)},
 'scope':'all elements of this group over GF(8); does not prove every admissible field'})

# Equation (10) with the author's [u,a]=u^-1*a^-1*u*a convention.
# Symbolic commutative coefficients for n=4. Formula is also checked with
# noncommutative 2x2 block coefficients (a separate exact specialization).
P=PolynomialRing(QQ, names=['a21','a31','a32','a41','a42','a43','x'])
a21,a31,a32,a41,a42,a43,x=P.gens()
A=matrix(P,[[1,0,0,0],[a21,1,0,0],[a31,a32,1,0],[a41,a42,a43,1]])
AI=A.inverse(); N=4; total=0
for k in range(N):
 for m in range(k):
  E=matrix(P,N,N); E[k,m]=x; U=identity_matrix(P,N)+E
  rhs=identity_matrix(P,N)-E
  for s in range(k,N):
   for r in range(m+1): rhs[s,r]+=AI[s,k]*x*A[m,r]
  assert (identity_matrix(P,N)-E)*AI*U*A == rhs
  total+=1
report['checks'].append({'claim':'Equation (10)', 'result':'pass',
 'scope':'symbolic generic UT(4) over QQ[a21,...,a43,x]', 'positions':total})

F=GF(3); blockcases=0
for seed in range(3):
 N=4; A=identity_matrix(F,2*N)
 for i in range(N):
  for j in range(i):
   for u,v in product(range(2),repeat=2): A[2*i+u,2*j+v]=F(seed+i+2*j+u*v+u+2*v)
 AI=A.inverse(); X=matrix(F,[[seed,1],[2,seed+1]])
 for k in range(N):
  for m in range(k):
   E=matrix(F,2*N,2*N); E.set_block(2*k,2*m,X)
   rhs=identity_matrix(F,2*N)-E
   for s in range(k,N):
    for r in range(m+1):
     block=AI.matrix_from_rows_and_columns([2*s,2*s+1],[2*k,2*k+1])*X*A.matrix_from_rows_and_columns([2*m,2*m+1],[2*r,2*r+1])
     for u,v in product(range(2),repeat=2): rhs[2*s+u,2*r+v]+=block[u,v]
   assert (identity_matrix(F,2*N)-E)*AI*(identity_matrix(F,2*N)+E)*A==rhs
   blockcases+=1
report['checks'].append({'claim':'Equation (10), noncommutative coefficients',
 'result':'pass', 'scope':'UT(4, Mat(2,GF(3))), three fixed exact matrices', 'cases':blockcases})

# Example 6: normality in the specified finite fields, and failure to be a
# two-sided ideal. Normality is checked on all elementary generators.
for p in [2,3]:
 F=GF(p); I=identity_matrix(F,6)
 def ex6(a,b,x,y,z):
  return matrix(F,[[1,0,0,0,0,0],[0,1,0,0,0,0],[a,0,1,0,0,0],
                  [b,0,0,1,0,0],[x,0,0,0,1,0],[z,y,b,-a,0,1]])
 group=[ex6(*v) for v in product(F,repeat=5)]
 ks={key(a) for a in group}; generators=[]
 for i in range(6):
  for j in range(i):
   for c in F:
    if c:
     g=matrix(I); g[i,j]=c; generators.append(g)
 for g in generators:
  for a in group: assert key(g.inverse()*a*g) in ks
 for a in group: assert key(a.inverse()) in ks
 # Subring closure follows symbolically from the sole cross term ba'-ab'
 # in position (6,1), a free parameter; check every pair over GF(2).
 if p==2:
  for a,b in product(group,group): assert key(a*b) in ks
 E=matrix(F,6,6); E[3,2]=1
 A=ex6(F.one(),F.zero(),F.zero(),F.zero(),F.zero())-I
 assert key(I+E*A) not in ks
 report['checks'].append({'claim':'Example 6 normal subgroup, not ring ideal',
  'field':f'GF({p})', 'order':len(ks), 'conjugations':len(generators)*len(group),
  'inverses':len(group), 'group_products':len(group)**2 if p==2 else 0,
  'result':'pass', 'scope':'these fields only; characteristic status is not tested'})

print(json.dumps(report, ensure_ascii=False, indent=2))
