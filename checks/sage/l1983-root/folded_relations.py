"""Integral rank-two checks for formulas (2)–(4), printed pp.507–508.

Pinned D4 triality is represented on the split orthogonal 8-space.
The three outer simple generators are cycled; the central generator
is fixed. Independent ui,vi encode sigma^i(u),sigma^i(v), sigma^3=1.
Thus polynomial checks are universal identities for commutative rings
with that automorphism, rather than substitutions in a finite field.
Here [x,y]=y^-1*x^-1*y*x, the inverse of x^-1*y^-1*x*y.
The choice matters for the ordered highest-root coefficient.
"""

from sage.all import ZZ, GF, PolynomialRing, matrix, identity_matrix
from sage.env import SAGE_VERSION
from datetime import datetime, timezone
from hashlib import sha256
from pathlib import Path
import json
from itertools import product

R = PolynomialRing(ZZ, names=('u0', 'u1', 'u2', 'v0', 'v1', 'v2', 't'))
u0, u1, u2, v0, v1, v2, t = R.gens()
u = (u0, u1, u2)
v = (v0, v1, v2)
I = identity_matrix(R, 8)


def e(i, j):
    m = matrix(R, 8)
    m[i, j] = 1
    return m


def minus(i, j):
    return e(i, j) - e(j+4, i+4)


def plus(i, j):
    return e(i, j+4) - e(j, i+4)


def bracket(x, y):
    return x*y-y*x


def comm(x, y):
    return y.inverse()*x.inverse()*y*x


def root(N, z):
    assert N*N == 0
    return I+z*N


A = (minus(0, 1), minus(2, 3), plus(2, 3))
B = minus(1, 2)
C = tuple(bracket(a, B) for a in A)
D = tuple(bracket(A[i], bracket(A[(i+1) % 3], B)) for i in range(3))
E = bracket(A[0], bracket(A[1], bracket(A[2], B)))
F = bracket(B, E)


def orbit(N, z):
    value = I
    for n, parameter in zip(N, z):
        value *= root(n, parameter)
    return value


def xa(z):
    return orbit(A, z)


def xb(z):
    return root(B, z)


def xc(z):
    return orbit(C, z)


def xd(z):
    return orbit(D, z)


def xe(z):
    return root(E, z)


def xf(z):
    return root(F, z)


def signed(z, sign):
    return tuple(sign*x for x in z)


checks = 0


def check(value):
    global checks
    assert value
    checks += 1


def unique_signs(actual, factors):
    matches = []
    for signs in product((-1, 1), repeat=len(factors)):
        expected = I
        for factor, sign in zip(factors, signs):
            expected *= factor(sign)
        if expected == actual:
            matches.append(signs)
    check(len(matches) == 1)
    return matches[0]


# Formula (2), including every matrix entry and all four factors.
norm_u = u0*u1*u2
signs2 = unique_signs(comm(xa(u), xb(t)), (
    lambda s: xc(signed(tuple(x*t for x in u), s)),
    lambda s: xd(signed(tuple(u[i]*u[(i+1) % 3]*t for i in range(3)), s)),
    lambda s: xe(s*norm_u*t),
    lambda s: xf(s*norm_u*t**2),
))
# With the inverse convention x^-1*y^-1*x*y and the same factor order,
# the last magnitude is 2, not 1. This is not a change to the source;
# it records why the convention must be stated when comparing formulas.
forward_signs2 = unique_signs(comm(xb(t), xa(u)), (
    lambda s: xc(signed(tuple(x*t for x in u), s)),
    lambda s: xd(signed(tuple(u[i]*u[(i+1) % 3]*t for i in range(3)), s)),
    lambda s: xe(s*norm_u*t),
    lambda s: xf(s*2*norm_u*t**2),
))

# Formula (3), with independent conjugates, hence also checking every
# bar placement. The source allows a root-normalization-dependent sign
# for each factor, but not independent signs within the three traces.
w = tuple(u[i]*v[(i+1) % 3] + u[(i+1) % 3]*v[i] for i in range(3))
trace_uuv = sum(u[i]*u[(i+1) % 3]*v[(i+2) % 3] for i in range(3))
trace_uvv = sum(u[i]*v[(i+1) % 3]*v[(i+2) % 3] for i in range(3))
signs3 = unique_signs(comm(xa(u), xc(v)), (
    lambda s: xd(signed(w, s)),
    lambda s: xe(s*trace_uuv),
    lambda s: xf(s*trace_uvv),
))
short_first = comm(xa(u),xc(v))
unique_signs(comm(short_first,xa(u)), (lambda s: xe(s*2*trace_uuv),))
unique_signs(comm(short_first,xc(v)), (lambda s: xf(s*2*trace_uvv),))

print('formula (2) signs', signs2)
print('inverse-convention formula (2) signs, last magnitude 2',forward_signs2)
print('formula (3) signs', signs3)

# Every intermediate commutator in the first triality extraction.
first = comm(comm(xa(u), xb(t)), xa(u))
third = comm(first, xa(u))
signs_triple = unique_signs(third, (lambda s: xe(s*6*norm_u*t),))
signs_fourth = unique_signs(comm(third, xb(t)), (
    lambda s: xf(s*6*norm_u*t**2),))
dsign = None
for s in (-1, 1):
    rest = xd(tuple(2*s*u[i]*u[(i+1)%3]*t for i in range(3))).inverse()*first
    if all(rest[i,j] == I[i,j] for i in range(8) for j in range(8)
           if E[i,j] == 0 and F[i,j] == 0):
        dsign = s
        eij = next((i,j) for i in range(8) for j in range(8) if E[i,j])
        fij = next((i,j) for i in range(8) for j in range(8) if F[i,j])
        pe = (rest[eij]-I[eij])/E[eij]
        pf = (rest[fij]-I[fij])/F[fij]
        check(rest == xe(pe)*xf(pf))
        print('triality first correction parameters', pe, pf)
check(dsign is not None)
check(first.inverse() == xd(tuple(2*u[i]*u[(i+1)%3]*t for i in range(3)))
      * xe(-6*norm_u*t) * xf(-3*norm_u*t**2))
print('triality extraction signs', signs_triple, signs_fourth, dsign)

# Complete G2 table: all ordered nonproportional positive/negative
# root pairs, including every zero commutator, in the pinned fixed
# subgroup of D4. Extract coefficients by distinct monomial degrees.
positive = {(1,0): lambda z: xa((z,z,z)), (0,1): xb,
            (1,1): lambda z: xc((z,z,z)),
            (2,1): lambda z: xd((z,z,z)), (3,1): xe, (3,2): xf}
groups = dict(positive)
for r, generator in positive.items():
    groups[tuple(-a for a in r)] = lambda z, gen=generator: gen(z).transpose()
g2_pairs = 0
g2_coefficients = []
for r, s in product(groups, repeat=2):
    if r == s or r == tuple(-a for a in s):
        continue
    targets = [(i+j,i,j,(i*r[0]+j*s[0],i*r[1]+j*s[1]))
               for i in range(1,5) for j in range(1,5)
               if (i*r[0]+j*s[0],i*r[1]+j*s[1]) in groups]
    targets.sort()
    residual = comm(groups[r](u0), groups[s](v0))
    for _, i, j, z in targets:
        linear = groups[z](t).apply_map(lambda p: p.monomial_coefficient(t))
        entry = next((a,b) for a in range(8) for b in range(8) if linear[a,b])
        coeff = R(residual[entry]).monomial_coefficient(u0**i*v0**j)/linear[entry]
        check(coeff in ZZ and 1 <= abs(coeff) <= 3)
        g2_coefficients.append((r,s,i,j,int(coeff)))
        residual = groups[z](-coeff*u0**i*v0**j)*residual
    check(residual == I)
    g2_pairs += 1
print('G2 ordered independent pairs', g2_pairs,
      'nonzero coefficients', len(g2_coefficients))
print('G2 coefficients', g2_coefficients)

# Formula (5): all root pairs, using the rank-one SL2 parametrization.
# The 12 roots use the same integral representatives as the full table.
gram = matrix(ZZ,[[2,-3],[-3,6]])
def pairing(r,s):
    return ZZ(2*sum(r[i]*gram[i,j]*s[j] for i in range(2) for j in range(2))
              /sum(r[i]*gram[i,j]*r[j] for i in range(2) for j in range(2)))
def weyl(r,z):
    nr = tuple(-a for a in r)
    return groups[r](z)*groups[nr](-1/z)*groups[r](z)
for r,s in product(groups,repeat=2):
    n = weyl(r,R(-1))
    h = weyl(r,t)*n
    check(h*groups[s](u0)*h.inverse() == groups[s](t**pairing(r,s)*u0))
    reflected = tuple(s[i]-pairing(r,s)*r[i] for i in range(2))
    conjugated = n*groups[s](u0)*n.inverse()
    check(any(conjugated == groups[reflected](sign*u0) for sign in (-1,1)))

# Section3: polynomial commutators actually used at the bad primes.
simple_a = positive[(1,0)]
simple_b = positive[(0,1)]
short_c = positive[(1,1)]
short_d = positive[(2,1)]
long_f = positive[(3,2)]
comm_ab = comm(simple_a(u0),simple_b(t))
check(any(comm(comm_ab,simple_b(v0)) == long_f(s*u0**3*t*v0)
          for s in (-1,1)))
def mod_equal(left,right,p):
    Q = R.change_ring(GF(p))
    return left.change_ring(Q) == right.change_ring(Q)
check(any(mod_equal(comm(comm(simple_a(1),simple_b(t)),simple_a(1)),
                    short_d(s*2*t),3) for s in (-1,1)))
nb = weyl((0,1),R(-1))
check(any(mod_equal(comm(comm(nb*simple_a(u0)*nb.inverse(),simple_a(1)),
                          simple_b(1)),long_f(s*3*u0),2) for s in (-1,1)))

# The first B2-type extraction statements l=3 and l=5 are covered by
# the full table. State their literal coefficient magnitudes as checks.
coeffs_l3 = sorted(abs(c) for r,s,i,j,c in g2_coefficients
                  if r==(1,0) and s==(1,1))
coeffs_l5 = sorted(abs(c) for r,s,i,j,c in g2_coefficients
                  if r==(1,0) and s==(0,1))
check(coeffs_l3 == [2,3,3])
check(coeffs_l5 == [1,1,1,1])

# Formula (4), pinned A3 involution interchanging the two outer roots.
J = identity_matrix(R, 4)
def e4(i,j):
    m = matrix(R,4)
    m[i,j] = 1
    return m
A0, A1, B4 = e4(0,1), e4(2,3), e4(1,2)
C0, C1 = bracket(A0,B4), bracket(A1,B4)
D4 = bracket(A0,bracket(A1,B4))
xa4 = lambda z0,z1: (J+z0*A0)*(J+z1*A1)
xb4 = lambda z: J+z*B4
xc4 = lambda z0,z1: (J+z0*C0)*(J+z1*C1)
xd4 = lambda z: J+z*D4
actual4 = comm(xa4(u0,u1),xb4(t))
matches4 = [(s1,s2) for s1,s2 in product((-1,1),repeat=2)
            if actual4 == xc4(s1*u0*t,s1*u1*t)*xd4(s2*u0*u1*t)]
check(len(matches4) == 1)
double4 = comm(actual4,xa4(u0,u1))
check(any(double4 == xd4(s*2*u0*u1*t) for s in (-1,1)))
print('formula (4) signs', matches4[0])
print(f'ok l1983-root-folded: {checks} checks')
print(json.dumps({'sage':SAGE_VERSION,'utc':datetime.now(timezone.utc).isoformat(),
                  'sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
                  'checks':checks,'g2_pairs':g2_pairs,
                  'g2_nonzero_coefficients':len(g2_coefficients)},sort_keys=True))
