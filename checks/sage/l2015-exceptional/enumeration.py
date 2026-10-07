"""Check formulas (0.1),(2.5),(2.7) and the table on pp. 166–171.

Exact checks cover every printed polynomial, all corner chains through
n=9, and all subspaces in the stated finite-field ranges. This does not
prove classification over arbitrary fields or all additive subgroups.
"""
from sage.all import ZZ, QQ, PolynomialRing, binomial, VectorSpace, GF, prod
from itertools import combinations
import json

R = PolynomialRing(ZZ, 'q')
q = R.gen()
checks = 0

def check(condition):
    global checks
    assert condition
    checks += 1

def proper(m, t):
    result = R.zero()
    for rest in combinations(range(2, m + 1), t - 1):
        pivots = (1,) + rest
        result += prod((q**(k+1) - 1)**(pivots[k+1] - pivots[k] - 1)
                       for k in range(t - 1)) * (q**t - 1)**(m - pivots[-1])
    return result

def count(n):
    return sum(ZZ(binomial(n, m)*binomial(n, m+1)/n)
               * sum(proper(m,t) for t in range(1,m+1))
               for m in range(1,n))

printed = {
    2: R(1), 3: q+3, 4: 2*q**2+5*q+6,
    5: q**4+3*q**3+16*q**2+11*q+10,
    6: 2*q**6+2*q**5+16*q**4+36*q**3+46*q**2+14*q+15,
    7: q**9+3*q**8+4*q**7+37*q**6+39*q**5+16*q**4
       +144*q**3+48*q**2+15*q+21,
}
computed = {n: count(n) for n in printed}
table = {str(n): {'printed': str(printed[n]), 'computed': str(computed[n]),
                 'equal': printed[n] == computed[n]} for n in printed}
print(json.dumps({'table': table}, ensure_ascii=False))
for n in range(2,7):
    check(computed[n] == printed[n])
check(computed[7] != printed[7])
corrected_seven = printed[7] + 100*q**4
check(computed[7] == corrected_seven)

def gaussian(a,b):
    if b < 0 or b > a:
        return R.zero()
    if b == 0 or b == a:
        return R.one()
    return gaussian(a-1,b) + q**(a-b)*gaussian(a-1,b-1)

for m in range(1,8):
    for t in range(1,m+1):
        independent = sum((-1)**j*binomial(m,j)*gaussian(m-j,t)
                          for j in range(m+1))
        check(independent == proper(m,t))
for n in range(2,10):
    total = 1
    for m in range(1,n):
        chains = sum(all(a < b for a,b in zip(js,is_))
                     for js in combinations(range(1,n),m)
                     for is_ in combinations(range(2,n+1),m))
        expected = ZZ(binomial(n,m)*binomial(n,m+1)/n)
        check(chains == expected)
        total += chains
    check(total == ZZ(binomial(2*n,n-1)/n))
    check(total != 1 + ZZ(binomial(2*n,n-1)/n))

# The quotient formula in (2.7) agrees with the direct polynomial sum,
# including negative printed exponents t-j_t.
for m in range(1,9):
    for t in range(1,m+1):
        value = R.zero()
        for rest in combinations(range(2,m+1),t-1):
            pivots = (1,) + rest
            value += R((q**t-1)**(m-pivots[-1])/(q-1)**(t-pivots[-1])
                       * prod(((q**(k+1)-1)/(q-1))**
                              (pivots[k+1]-pivots[k]-1)
                              for k in range(1,t-1)))
        check(value == proper(m,t))
    check(proper(m,1) == (q-1)**(m-1))
    check(proper(m,m) == 1)
    if m >= 2:
        check(proper(m,2) == (q-1)**(m-2)*sum((q+1)**k for k in range(m-1)))

spaces = 0
ranges = {2: 5, 3: 4, 4: 4, 5: 3}
for order, bound in ranges.items():
    for m in range(1,bound+1):
        V = VectorSpace(GF(order),m)
        for t in range(1,m+1):
            observed = 0
            for S in V.subspaces(t):
                spaces += 1
                if all(any(row[i] for row in S.basis()) for i in range(m)):
                    observed += 1
            check(observed == proper(m,t)(order))

# The printed i<m definition admits the zero subgroup when m=1.
zero = VectorSpace(GF(2),1).zero_subspace()
check(all(any(row[i] for row in zero.basis()) for i in range(0)))
check(not all(any(row[i] for row in zero.basis()) for i in range(1)))
print(json.dumps({'checks': checks, 'subspaces': spaces,
                  'finite_field_ranges': ranges}, ensure_ascii=False))
ideal_cases = []
for order,n in ((2,2),(2,3),(2,4),(3,2),(3,3),(4,2),(4,3)):
    F = GF(order)
    positions = [(i,j) for i in range(n) for j in range(i)]
    dim = len(positions)
    V = VectorSpace(F,dim)
    def product(a,b):
        coefficients = {(i,j): sum(a[positions.index((i,k))]
                                  *b[positions.index((k,j))]
                                  for k in range(j+1,i))
                        for i,j in positions}
        return V([coefficients[p] for p in positions])
    ideals = 0
    examined = 0
    for t in range(dim+1):
        for S in V.subspaces(t):
            examined += 1
            if all(product(a,b) in S and product(b,a) in S
                   for a in S.basis() for b in V.basis()):
                ideals += 1
    check(ideals == 1 + count(n)(order))
    ideal_cases.append({'q':order,'n':n,'ideals':ideals,'subspaces':examined})
print(json.dumps({'ideal_cases':ideal_cases,'checks':checks},ensure_ascii=False))
print(f'ok l2015-exceptional enumeration: {checks} checks')
