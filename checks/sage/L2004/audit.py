"""Exact finite matrix checks of the identities used in the finitary article.

These certificates do not prove classification for arbitrary coefficient rings
or infinite chains. The Peirce decomposition has a separate general proof.
"""
from itertools import product
import json
from sage.all import GF, Matrix, QQ, VectorSpace, matrix, vector, zero_matrix, PolynomialRing, ZZ

checks = 0


def check(condition):
    global checks
    assert condition
    checks += 1


def units(n, field=QQ):
    result = []
    for i in range(n):
        for j in range(i):
            e = zero_matrix(field, n)
            e[i, j] = 1
            result.append(e)
    return result


def coordinates(a):
    return vector(a.base_ring(), [a[i, j] for i in range(a.nrows()) for j in range(i)])


def centralizer(n, basis):
    es = units(n)
    columns = []
    for e in es:
        columns.append(sum(((e * b - b * e).list() for b in basis), []))
    if not basis:
        return VectorSpace(QQ, len(es))
    return matrix(QQ, columns).left_kernel()


def span(n, pairs):
    return VectorSpace(QQ, n * (n - 1) // 2).subspace(
        [coordinates(e) for e in units(n) if next(
            (i, j) for i in range(n) for j in range(i) if e[i, j]) in pairs])


for n in range(3, 9):
    all_pairs = {(i, j) for i in range(n) for j in range(i)}
    es = units(n)
    r2 = {(i, j) for i, j in all_pairs if i - j >= 2}
    for t in range(1, n):
        nt = {(i, j) for i, j in all_pairs if i >= t and j < t}
        basis = [e for e in es if any(e[i, j] for i, j in nt)]
        check(centralizer(n, basis) == span(n, nt))
    for v in range(1, n):
        for t in range(1, n):
            rect = {(i, j) for i, j in all_pairs if i >= v and j < t}
            basis = [e for e in es if any(e[i, j] for i, j in rect)]
            expected = {(i, j) for i, j in all_pairs if i >= t and j < v}
            check(centralizer(n, basis) == span(n, expected))
    for j in range(1, n):
        power = [e for e in es if any(e[i, k] for i, k in all_pairs
                                    if i - k >= j)]
        cpower = centralizer(n, power)
        nij = {(i, k) for i, k in all_pairs if i >= n-j and k < j}
        check(cpower == span(n, nij))
        if n-j <= j:
            next_power = [e for e in es if any(e[i, k] for i, k in all_pairs
                                              if i - k >= j - 1)]
            rhs = (cpower.intersection(span(n, r2))
                   + centralizer(n, next_power)
                   + span(n, {(i, k) for i, k in all_pairs if i >= j and k < j})
                   + span(n, {(i, k) for i, k in all_pairs
                              if i >= n - j and k < n - j}))
            check(cpower == rhs)

# The sum of the two ideals is not their set-theoretic union.
n = 5
nl = {(i, j) for i in range(n) for j in range(i) if i >= 2 and j < 2}
nt = {(i, j) for i in range(n) for j in range(i) if i >= 3 and j < 3}
nii = {(i, j) for i in range(n) for j in range(i) if i >= 2 and j <= 2}
check(span(n, nl) + span(n, nt) == span(n, nii))
a = zero_matrix(QQ, n)
a[2, 0] = a[4, 2] = 1
check(coordinates(a) not in span(n, nl))
check(coordinates(a) not in span(n, nt))
check(coordinates(a) in span(n, nii))

# Noncommutative Peirce decomposition in M_2(F_2).
field = GF(2)
elements = [matrix(field, 2, data) for data in product(field, repeat=4)]
f = matrix(field, [[1, 0], [0, 0]])
one = Matrix.identity(field, 2)
a1 = {tuple((a * f).list()) for a in elements}
a2 = {tuple((a * (one - f)).list()) for a in elements}
b1 = {tuple(((one - f) * a).list()) for a in elements}
b2 = {tuple((f * a).list()) for a in elements}
for a in elements:
    check(tuple(a.list()) in {tuple((matrix(field, 2, x) + matrix(field, 2, y)).list())
                       for x in a1 for y in a2})
    check(tuple(a.list()) in {tuple((matrix(field, 2, x) + matrix(field, 2, y)).list())
                       for x in b1 for y in b2})
for left, right in ((a1, b1), (a2, b2)):
    for x in left:
        for y in right:
            check(matrix(field, 2, x) * matrix(field, 2, y) == 0)
check(f * f == f)
check(any(f * a != a * f for a in elements))

# The printed cubic image at c=0 kills a nonzero root element.
e31 = zero_matrix(field, 5)
e31[2, 0] = 1
check(e31 != 0)
check(0 * e31 == 0)

# The two half-open intervals of integers in Example 2.8 are isomorphic.
gamma = list(range(1, 5))
omega = list(range(2, 6))
check([x + 1 for x in gamma] == omega)
check(all((x < y) == (x + 1 < y + 1) for x in gamma for y in gamma))

# Standard idempotent mixture with one fixed central f=(1,0) in F_2×F_2.
# The local f_i is defined by the fixed (m+1,m) projection of H^(i).
f = (1, 0)
fc = (0, 1)
for n in (6, 7, 8):
    for m in range(n//2+1, n):
        mp = n-m+1
        if m <= mp:
            continue
        def coefficient(i,u,v):
            direct = u >= i+1 and v <= i
            reverse = u >= n+1-i and v <= n-i
            return tuple(int(direct)*a+int(reverse)*b for a,b in zip(f,fc))
        fm = coefficient(m,m+1,m)
        fnm = coefficient(n-m,m+1,m)
        check(fm == f and fnm == fc)
        for i in (m,n-m):
            fi = coefficient(i,m+1,m)
            fni = coefficient(i,mp,mp-1)
            check(coefficient(i,m,1) == fni)
            check(coefficient(i,n,mp) == fi)
        check(coefficient(n-m,n,mp) != fm)

# Complete symbolic cubic map in NT(5,K), with p=1,k=2,m=3,q=5.
# Polynomial residuals are proved to be multiples of the two displayed
# relations, rather than assuming that the desired map is a homomorphism.
names = ["a" + str(i) + str(j) for i in range(5) for j in range(i)]
names += ["b" + str(i) + str(j) for i in range(5) for j in range(i)]
names += ["c"]
p = PolynomialRing(ZZ, names)
variables = list(p.gens())
c = variables[-1]
vs = variables
def strict(data):
    a = zero_matrix(p, 5)
    for index, (i,j) in enumerate((i,j) for i in range(5) for j in range(i)):
        a[i,j] = data[index]
    return a
def cubic(a):
    result = matrix(a)
    x,y,z = a[1,0], a[2,1], a[2,0]
    result[4,2] += c*x
    result[4,1] += c*(z+y*y-y+x*y)
    result[4,0] += c*(z*z+x*z)
    return result
a,b = strict(vs[:10]), strict(vs[10:20])
residual = cubic(a+b+a*b)-cubic(a)-cubic(b)-cubic(a)*cubic(b)
obstruction = c*(a[2,1]**2-a[2,1])*(b[1,0]**2-b[1,0])
residual[4,0] -= obstruction
for value in residual.list():
    quotient, remainder = value.quo_rem(c)
    check(remainder == 0)
    check(all(coefficient % 2 == 0 for coefficient in quotient.coefficients()))
for value in (cubic(cubic(a))-a).list():
    quotient, remainder = value.quo_rem(c)
    check(remainder == 0)
    check(all(coefficient % 2 == 0 for coefficient in quotient.coefficients()))
for i,j in ((1,0),(2,1),(2,0)):
    e = zero_matrix(p,5)
    e[i,j] = vs[0]
    image = cubic(e)
    check(image[i,j] == vs[0])

print(json.dumps({"checks": checks, "status": "PASS",
                  "scope": "finite identities and original-error certificates"}))
