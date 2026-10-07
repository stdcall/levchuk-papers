from sage.all import *
from functools import lru_cache
import json, datetime, hashlib
from pathlib import Path

def C(a,b):
    return ZZ(0) if b<0 or b>a or a<0 else binomial(a,b)
def cat(n):
    return C(2*n,n)/QQ(n+1)
def ballot(X,Y):
    if X<0 or Y<0 or Y>X or (X+Y)%2: return ZZ(0)
    return QQ(Y+1)/(X+1)*C(X+1,(X+Y+2)//2)
@lru_cache(None)
def paths(X,Y,strict=False):
    if X==0: return int(Y==0)
    if Y<0 or Y>X: return 0
    if strict and Y==0: return 0
    return sum(paths(X-1,Y-d,strict) for d in [-1,1])

results={}
for X in range(1,25):
    for Y in range(X+1):
        if (X+Y)%2: continue
        assert ballot(X,Y)==paths(X,Y)
        if Y>0:
            assert QQ(Y)/X*C(X,(X+Y)//2)==paths(X,Y,True)
results['ballot']='All admissible integer endpoints 1<=X<=24, 0<=Y<=X; strict count for Y>0.'

PS=PowerSeriesRing(QQ,'x',default_prec=100); x=PS.gen()
R=PolynomialRing(QQ,'z'); z=R.gen()
cvals=[]; bvals=[]
for n in range(1,31):
    cn=sum(QQ(i)/n*2**(n-i+1)*C(2*n,n-i) for i in range(1,n+1))
    cvals.append(cn)
    if n>1: assert cn==9*cvals[-2]-2**(n+1)*cat(n-1)
    h=(1-12*x+(1-8*x).sqrt())/(1-9*x)
    assert cn==h[n]
    S1=sum(C(t-1,t-i)*QQ(t*(t+1))/(2*n-t)*C(2*n-t,n-t)
        for i in range(2,n+1) for t in range(i,n+1))
    S2=sum((t+1)*C(t-2,t-i)*QQ(m)/(2*n-m)*C(2*n-m,n-m)
        for i in range(2,n) for t in range(i,n) for m in range(t+1,n+1))
    P=n+1-2*(2*n+1)*x+2*(2*n+1)*x*x
    Q=n-4*n*x+2*(2*n+1)*x*x
    assert S1==(P*(1-x)**(-n-3)/(1-2*x))[n-2] if n>=2 else S1==0
    assert S2==(Q*(1-x)**(-n-3)/(1-2*x))[n-3] if n>=3 else S2==0
    combined=3*4**(n-1)-(2*n+1)*C(2*n-2,n-4)-(n+QQ(3)/2)*C(2*n-1,n-3)+(n+QQ(1)/4)*C(2*n,n-2)-QQ(3)/8*C(2*n+4,n+2)+QQ(3)/4*C(2*n+2,n+1)
    assert S1+S2==combined
    bn=3*4**(n-1)-2*factorial(2*n-2)/QQ(factorial(n-1)*factorial(n+1))*(n*n-n+1)
    if n>=2: assert bn==cat(n+1)+2*cat(n)-2*cat(n-1)+S1+S2
    bvals.append(bn)
    for t in range(n):
        assert sum(QQ(m)/(2*n-m)*C(2*n-m,n-m) for m in range(t+1,n+1))==QQ(t+2)/(2*n-t)*C(2*n-t,n-t-1)
        assert QQ(t*(t+1))/(2*n-t)*C(2*n-t,n-t)==(n+1)*C(2*n-t+1,n-t)-2*(2*n+1)*C(2*n-t,n-t)+2*(2*n+1)*C(2*n-t-1,n-t)
        assert QQ((t+1)*(t+2))/(2*n-t)*C(2*n-t,n-t-1)==-(n+2)*C(2*n-t+1,n-t-1)+2*(n+1)*C(2*n-t,n-t-1)+2*(n+2)*C(2*n-t,n-t-2)-2*(2*n+1)*C(2*n-t-1,n-t-2)
assert bvals[:5]==[2,10,41,166,670]
# Preserve and refute the printed readings beside their corrected identities.
assert QQ(1)/(2*3-1)*C(2*3-1,1) == 1
assert QQ(1)/(2*3-1)*C(2*3-1,3) == 2
assert QQ(1)/(2*3-1)*C(2*3-1,1) != ballot(4,0)
wrong_h=(1-12*x-(1-8*x).sqrt())/(1-9*x)
assert wrong_h[1] == -8 and h[1] == 2
n=3
wrong_P=n+1-2*(2*n+1)*x+2*(2*n+1)*x*x
wrong_residue=(wrong_P*(1-x)**(-1)/(1-2*x))[n-2]
correct_residue=(wrong_P*(1-x)**(-n-3)/(1-2*x))[n-2]
assert wrong_residue == -2 and correct_residue == 18
assert wrong_residue != correct_residue
# The printed lower limit t=1 is harmless: terms t<i are zero.
for n in range(2,31):
    zero_extended=sum(C(t-1,t-i)*QQ(t*(t+1))/(2*n-t)*C(2*n-t,n-t)
        for i in range(2,n+1) for t in range(1,n+1))
    restricted=sum(C(t-1,t-i)*QQ(t*(t+1))/(2*n-t)*C(2*n-t,n-t)
        for i in range(2,n+1) for t in range(i,n+1))
    assert zero_extended == restricted
results['printed_readings']='Refuted (12) at n=3,m=1; minus square-root sign at n=1; missing (1-x)^(-n-2) factor in (22) at n=3. The printed t=1 lower limit in (16) is retained and verified by zero extension through n=30.'
results['coefficients']='Exact QQ: C recurrence and generating function, S1/S2 integral coefficients, S3 decomposition, B closed count and ballot-tail/binomial identities, n=1..30 (B base decomposition n>=2).'
results['C_initial']=[int(v) for v in cvals[:8]]
results['B_initial']=[int(v) for v in bvals[:8]]
F=FractionField(PolynomialRing(QQ,['x','n'])); xx,nn=F.gens()
P=nn+1-2*(2*nn+1)*xx+2*(2*nn+1)*xx**2
Q=nn-4*nn*xx+2*(2*nn+1)*xx**2
RR=nn+1-(3*nn+2)*xx+2*xx**2+2*(2*nn+1)*xx**3
assert P+xx*Q==RR
assert RR/(1-2*xx)==nn+QQ(1)/4-(nn+QQ(3)/2)*xx-(2*nn+1)*xx**2+QQ(3)/4/(1-2*xx)
# z=x/[2(1+x)^2], the analytic branch at zero has sqrt(1-8z)=(1-x)/(1+x).
zz=xx/(2*(1+xx)**2)
HH=(1-12*zz+(1-xx)/(1+xx))/(1-9*zz)
assert HH==2/(1-xx/2)
assert 2*(1-xx)/(xx*(1+xx)*(1-xx/2))/((1-xx)/(2*(1+xx)**3))==HH/zz
results['symbolic']='Polynomial/rational identities over QQ(x,n), including change of variable Jacobian and the corrected square-root sign.'
results['limits']='Finite coefficient/path checks do not establish classification of Chevalley ideals or all-rank enumeration. Rational identities are symbolic. No floating arithmetic.'
results['utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
results['sage_version']=version()
project=Path(__file__).resolve().parents[3]
results['checked_text_sha256']={str(p.relative_to(project)):hashlib.sha256(p.read_bytes()).hexdigest()
    for p in [project/'content/papers/l2001-enumeration/03-lattice-paths.typ',
        project/'content/papers/l2001-enumeration/04-integral-sums.typ']}
print(json.dumps(results,ensure_ascii=False,indent=2))
