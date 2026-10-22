"""Exact formulas in Levchuk, Algebra i Logika22:4(1983), pp.421–433.

All printed 2x2 calculations are checked over explicit rational-function
fields or polynomial rings. Finite word ranges are stated separately.
This does not prove the classification of finite subgroups or Schur's
theorem. Commutators in Lemma2 are xyx^-1y^-1, determined by the printed
translation c(1-a^2), rather than the convention of the later root paper.
"""
from sage.all import QQ, ZZ, GF, PolynomialRing, matrix, identity_matrix
from sage.env import SAGE_VERSION
from itertools import product
from pathlib import Path
from hashlib import sha256
from datetime import datetime, timezone
import json

checks = 0
def check(value):
    global checks
    assert value
    checks += 1

P = PolynomialRing(QQ,names=('a','b','c','d','t','z','r','s','k','l'))
Q = P.fraction_field()
a,b,c,d,t,z,r,s,k,l = map(Q,P.gens())
I = identity_matrix(Q,2)
U = lambda x: matrix(Q,[[1,x],[0,1]])
L = lambda x: matrix(Q,[[1,0],[x,1]])
D = lambda x: matrix(Q,[[x,0],[0,1/x]])
W = lambda x: matrix(Q,[[0,x],[-1/x,0]])

# p.422, equation(2), unique fixed point of a nonupper unipotent.
Rz = U(z)*L(t)*U(-z)
check(Rz == matrix(Q,[[1+z*t,-z**2*t],[t,1-z*t]]))
check(Rz.det()==1 and Rz.trace()==2)
check(c*z**2+((2-a)-a)*z-(a*(2-a)-1)/c
      == c*(z-(a-1)/c)**2)
# Here a=a11 and d=2-a, so (1-d)/c=(a-1)/c, as printed.
check((U(r)*L(s)*U(-r)*U(z)*L(t)*U(-z)).trace()
      == 2-s*t*(r-z)**2)

# p.423, Mobius composition and projective kernel on a dense chart.
A = matrix(Q,[[a,b],[c,d]])
B = matrix(Q,[[r,s],[k,l]])
mobius = lambda M,x: (M[0,0]*x+M[0,1])/(M[1,0]*x+M[1,1])
check(mobius(A*B,z)==mobius(A,mobius(B,z)))
check(U(a)*U(b)==U(a+b))
check(D(a)*D(b)==D(a*b))
check(D(t)*U(a)*D(t).inverse()==U(t**2*a))
check(W(t)*U(a)*W(t).inverse()==L(-a/t**2))
check(U(b)*(U(c)*D(t))*U(-b)==U(c+b*(1-t**2))*D(t))
# Lemma2, p.424; all denominators correspond to nonzero diagonal t,a.
comm = lambda x,y: x*y*x.inverse()*y.inverse()
check(comm(U(c)*D(t),D(a))==U(c*(1-a**2)))

# Lemma6: traces give equations(3),(4), unique z for each t.
check((D(t)*U(z)*A).trace()==z*t*c+t*a+d/t)
solution = (2-t*a-d/t)/(t*c)
check((D(t)*U(solution)*A).trace()==2)
involution_solution = (-t*a-d/t)/(t*c)
check(involution_solution == (-(-t)*a-d/(-t))/((-t)*c))
check((D(t)*U(z)*matrix(Q,[[a,b],[c,-a]])).trace()*t
      == z*t**2*c+(t**2-1)*a)

# Lemma7: trace-zero nonupper matrices. Determinant1 is irrelevant to
# the stated upper-triangular iff relation, and is not assumed here.
Ai = matrix(Q,[[a,b],[c,-a]])
Bi = matrix(Q,[[r,s],[k,-r]])
check((Ai*Bi)[1,0]==c*r-a*k)
check((Ai*Bi)[1,0]/(c*k)==r/k-a/c)

# p.430: conjugated Weyl involution and ratio calculation.
J = U(-b)*W(t)*U(b)
check(J == matrix(Q,[[b/t,b**2/t+t],[-1/t,-b/t]]))
check((a*(-r*k)+b*k)/ (c*(-r*k)-a*k)
      == (a*r-b)/(c*r+a))
# Generic trace-zero alpha,beta normalized by their lower-left entries.
alpha = matrix(Q,[[a,(a*(-a)-1)/c],[c,-a]])
beta = matrix(Q,[[r,(r*(-r)-1)/k],[k,-r]])
ratio = (alpha*beta)[0,0]/(alpha*beta)[1,0]
check(ratio == ((a/c)*(r/k)+alpha[0,1]/c)/(r/k-a/c))
check(1/c**2 == (alpha[0,0]*alpha[1,1]-alpha[0,1]*alpha[1,0])/c**2)

# p.431, lower-left entry of conjugated unipotent, determinant4 in the
# two equations extracting a12 and a11; t=-1 in equation(3).
alpha_u = matrix(Q,[[a,(a*(2-a)-1)/c],[c,2-a]])
check((L(z)*alpha_u*L(-z))[1,0]
      == c-(2-a)*z+z*a-z**2*alpha_u[0,1])
check(matrix(Q,[[1,-2],[1,2]]).det()==4)
check(matrix(Q,[[1,-2],[1,2]]).inverse()*matrix(Q,[[r],[s]])
      == matrix(Q,[[(r+s)/2],[(s-r)/4]]))
check((D(-1)*U(z)*alpha_u).trace()==2-c*z-4)

# Lemma5, pp.425–426, characteristic2 diagonalization. rho is formal;
# t=rho+rho^-1, rho!=0,1. These are exactly the denominator conditions.
S = PolynomialRing(GF(2),names=('rho','sigma'))
T = S.fraction_field()
rho,sigma = map(T,S.gens())
u = lambda x: matrix(T,[[1,x],[0,1]])
lo = lambda x: matrix(T,[[1,0],[x,1]])
xi = matrix(T,[[rho/(1+rho),1/(1+rho)],[1,1]])
tt = rho+1/rho
check(xi.det()==1)
check(xi.inverse()*u(1)*xi==matrix(T,[[0,1],[1,0]]))
check(xi.inverse()*lo(tt)*xi==matrix(T,[[0,1/rho],[rho,0]]))
check(xi.inverse()*u(1)*lo(tt)*xi==matrix(T,[[rho,0],[0,1/rho]]))
# In a quadratic extension write rho=sigma² and a²=1/t.
xi2 = xi.apply_map(lambda q:q.subs({rho:sigma**2}))
aa = sigma/(1+sigma**2)
wa = matrix(T,[[0,aa],[1/aa,0]])
check(xi2.inverse()*wa*xi2==matrix(T,[[0,1/sigma],[sigma,0]]))

# Exceptional A5 calculations, p.429: the five-factor matrix overGF3.
V = PolynomialRing(GF(3),'z')
zz = V.gen()
up = lambda x: matrix(V,[[1,x],[0,1]])
down = lambda x: matrix(V,[[1,0],[x,1]])
omega = up(1)*down(zz)*up(1)*down(zz)*up(1)
check(omega==matrix(V,[[zz**2+1,zz**2+zz],
                     [zz**2-zz,zz**2+1]]))
check(omega.trace()==2*(zz**2+1))

# Proposition1, pp.432–433: the leading coefficient semigroup used by
# the induction. Closure is a universal identity over ZZ[a,b,c,d].
Z = PolynomialRing(ZZ,names=('a','b','c','d'))
za,zb,zc,zd = Z.gens()
lead = lambda x,y: matrix(Z,[[x,0],[y,0]])
check(lead(za,zb)*lead(zc,zd)==lead(za*zc,zb*zc))
# The printed RIGHT-column family cannot contain this leading matrix.
# Retain the erroneous reading as a refuted exact comparison, p.432.
check(lead(za*zb,zb)!=matrix(Z,[[0,za],[0,zb]]))
# Generic reduced block products, up to six blocks, with independent
# coefficients: exact polynomial identities, not finite substitutions.
for length in range(1,7):
    C = PolynomialRing(ZZ,names=tuple(f'k{i}' for i in range(length))
                       +tuple(f'l{i}' for i in range(length)))
    Xring = PolynomialRing(C,'X'); X = Xring.gen()
    coeff = C.gens(); ks=coeff[:length]; ls=coeff[length:]
    value = identity_matrix(Xring,2)
    leading = identity_matrix(C,2)
    for ki,li in zip(ks,ls):
        block = matrix(Xring,[[1+ki*li*X,ki],[li*X,1]])
        value *= block
        leading *= matrix(C,[[ki*li,0],[li,0]])
    check(all(value[i,j].degree()<=length for i in range(2) for j in range(2)))
    check(matrix(C,[[value[i,j][length] for j in range(2)] for i in range(2)])
          == leading)
    check(value[1,0].degree()==length)

# p.428–429 counting arithmetic: all q,f in a stated finite range.
# This is a bounded arithmetic cross-check, not the proof for all q.
for q in range(3,102,2):
    for f in range(1,102,2):
        if QQ(f*q-1)/2 <= q-2+f:
            check(f in (1,3))
            if f==3: check(q==3)
check(ZZ(1+3*3)*3*4/2==60)

# p.425's natural PGL2(F)->PSL2(K) requires ALL determinant square
# classes to become squares in K, not just one quadratic extension.
# This periodic V4 over QQ already needs Q(i,sqrt(2)), of degree4.
from sage.all import QuadraticField
Aq = matrix(QQ,[[-1,0],[0,1]])
Bq = matrix(QQ,[[0,2],[1,0]])
check(Aq**2==identity_matrix(QQ,2))
check(Bq**2==2*identity_matrix(QQ,2))
check(Aq*Bq==-Bq*Aq)
check(Aq.det()==-1 and (Aq*Bq).det()==2)
Qi=QuadraticField(-1,'i')
check(not Qi(2).is_square())
Ext=PolynomialRing(Qi,'s'); ss=Ext.gen()
check(Qi.extension(ss**2-2,'sqrt2').absolute_degree()==4)

print(f'ok l1983-dickson-matrices: {checks} checks')
print(json.dumps({'sage':SAGE_VERSION,'utc':datetime.now(timezone.utc).isoformat(),
                  'sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
                  'checks':checks},sort_keys=True))
