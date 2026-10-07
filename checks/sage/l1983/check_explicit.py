"""Bounded exact checks of Levchuk1983, printed pp. 72, 76–78.

Sources: the original definitions and equations (3), (17), (18), Lemma16,
Corollary6 and the quadratic-integer Example. Expected small orders are
read literally from Corollary6. The checks do not prove the classification
of arbitrary automorphisms over arbitrary rings.
"""
from sage.all import ZZ, PolynomialRing, GF, matrix
from itertools import product

checks = 0


def check(value):
    global checks
    assert value
    checks += 1


# Example p.78: p nonsquare, K=Z+Z sqrt(p), x=a+b sqrt(p).
# Arithmetic as pairs avoids assumptions about the sign of p.
def mul(u, v, p):
    a, b = u
    c, d = v
    return (a*c + p*b*d, a*d + b*c)


for p in (-3, -1, 2, 3, 5, 6, 7, 8, 10):
    check(not ZZ(p).is_square())
    # x=sqrt(p): x^2-x has sqrt coefficient -1, so has no half in K.
    check((p, -1)[1] % 2 != 0)
    for a, b in product(range(-8, 9), repeat=2):
        sq = mul((a, b), (a, b), p)
        rho = a + b*p
        z = (a*(a+1)//2 + p*b*(b+1)//2, a*b)
        check((2*z[0], 2*z[1]) == (sq[0]+rho, sq[1]))

# General polynomial identity underlying Lemma16 (commutative special case)
# and (17): 2*(lambda(x+y)-lambda(x)-lambda(y))=2*c*x*y.
P = PolynomialRing(ZZ, names=('x', 'y', 'c', 'a', 'b', 'p'))
x, y, c, a, b, p = P.gens()
check(c*((x+y)**2-(x+y)-x**2+x-y**2+y) == 2*c*x*y)
check((a+b)**2-(a+b)-a**2+a-b**2+b == 2*a*b)

# (3), and original p.72 misprint [ ... ]=1: in the adjoint group
# the neutral element is the zero matrix. Check every elementary pair
# over GF(2), GF(3), GF(5), ranks3..6, all scalar coefficients.
for q in (2, 3, 5):
    F = GF(q)
    for n in range(3, 7):
        O = matrix(F, n)
        I = matrix.identity(F, n)
        def elementary(i, j, scalar):
            A = matrix(F, n)
            A[i, j] = scalar
            return A
        indices = [(i,j) for i in range(n) for j in range(i)]
        for (i,j), (k,l), aa, bb in product(indices, indices, F, F):
            A = elementary(i,j,aa)
            B = elementary(k,l,bb)
            bracket = (I+A).inverse()*(I+B).inverse()*(I+A)*(I+B)-I
            expected = O
            if j == k:
                expected = elementary(i,l,aa*bb)
            elif i == l:
                expected = elementary(k,j,-bb*aa)
            check(bracket == expected)
        # Pair chosen in p.72's displayed condition, using phi=identity.
        A = elementary(2,0,F.one())
        B = elementary(1,0,F.one())
        printed_one = (I+A).inverse()*(I+B).inverse()*(I+A)*(I+B)-I
        check(printed_one != I)  # the printed reading is retained/refuted
        check(printed_one == O)

# Complete enumeration of automorphisms of NT(3,GF(p)) as an adjoint
# group, p=2,3. Each automorphism is determined by the two generators.
# All their defining relations are checked, then every pair of elements.
for p, expected_order in ((2, 8), (3, 432)):
    E = list(product(range(p), repeat=3))
    zero = (0,0,0)
    def compose(u,v):
        a,b,c = u
        d,e,f = v
        return ((a+d)%p, (b+e)%p, (c+f+b*d)%p)
    def inverse(u):
        a,b,c = u
        return ((-a)%p,(-b)%p,(-c+a*b)%p)
    def power(u, k):
        result = zero
        for _ in range(k):
            result = compose(result,u)
        return result
    def comm(u,v):
        return compose(compose(compose(inverse(u),inverse(v)),u),v)
    automorphisms = 0
    for A,B in product(E, repeat=2):
        C = comm(B,A)
        if C == zero or power(A,p) != zero or power(B,p) != zero:
            continue
        if C[:2] != (0,0):
            continue
        images = {u: compose(compose(power(A,u[0]),power(B,u[1])),power(C,u[2])) for u in E}
        if len(set(images.values())) != len(E):
            continue
        check(all(images[compose(u,v)] == compose(images[u],images[v]) for u,v in product(E,repeat=2)))
        automorphisms += 1
    check(automorphisms == expected_order)

# Derivation of A_nq from |Z|*|J|*|D|*|Aut(K)|/|Z inter J|;
# each exponent is integral. It checks arithmetic, not group classification.
for n, q, m in product(range(3,9), (2,3,4,5,8,9), (1,2,3)):
    if not ZZ(q).is_prime_power() or ZZ(q).factor()[0][1] != m:
        continue
    expected_exp = (n-1)*(ZZ(n)/2+m)-3
    check(expected_exp.denominator() == 1)
    A = m*(q-1)**(n-1)*q**expected_exp
    independently = m*(q-1)**(n-1)*q**(m*(n-1)+n*(n-1)//2-1-2)
    check(A == independently)
    if q == 2 and n >= 5:
        check(8*A == 2**((n-1)*(1+ZZ(n)/2)))
check(6 * (2**((4-1)*(ZZ(4)/2+1)-3)) == 3*2**7)

print(f'ok l1983-explicit: {checks} checks')
