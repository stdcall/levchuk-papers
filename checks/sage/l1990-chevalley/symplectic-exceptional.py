"""Exact local checks for pp. 331–335, equations (14)–(17) and E-type roots.

The symplectic realization uses E_ij-E_-j,-i, E_i,-j+E_j,-i and E_i,-i.
Its signs and commutator convention are checked against Lemmas 2–3.
All root-addition and root-pair commutator relations are checked over the
specified finite rings. These computations do not prove the classification
over arbitrary rings, or the omitted characteristic-subgroup argument.
Exceptional checks are root-support identities in simply laced types;
Chevalley coefficients there are units, so the checks are independent of
characteristic. Numbering is Bourbaki, plates V–VII.
"""

from datetime import datetime, timezone
from hashlib import sha256
from pathlib import Path
from time import perf_counter

from sage.all import (
    GF, ZZ, QQ, Integers, LieAlgebra, PolynomialRing, RootSystem,
    identity_matrix, matrix, vector,
)
from sage.env import SAGE_VERSION

started = perf_counter()
checks = 0


def check(condition):
    global checks
    assert condition
    checks += 1


class Symplectic:
    def __init__(self, ring, n):
        self.ring, self.n = ring, n
        self.indices = list(range(1, n + 1)) + list(range(-1, -n - 1, -1))
        self.I = identity_matrix(ring, 2 * n)
        self.roots = sorted(
            [(i, j) for i in range(2, n + 1) for j in range(1, i)]
            + [(i, -j) for i in range(1, n + 1) for j in range(1, i + 1)],
            key=lambda r: (self.height(r), r),
        )
        self.basis = {}
        for i, j in self.roots:
            E = matrix(ring, 2 * n)
            E[self.indices.index(i), self.indices.index(j)] = 1
            if j > 0:
                E[self.indices.index(-j), self.indices.index(-i)] = -1
            elif j != -i:
                E[self.indices.index(-j), self.indices.index(-i)] = 1
            check(E * E == 0)
            self.basis[i, j] = E
        J = matrix(ring, 2 * n)
        for i in range(n):
            J[i, n + i], J[n + i, i] = 1, -1
        for r in self.roots:
            X = self.x(r, ring.one())
            check(X.transpose() * J * X == J)

    def height(self, r):
        i, j = r
        return i - j if j > 0 else i - j - 1

    def x(self, r, t):
        return self.I + t * self.basis[r]

    def inverse(self, X):
        N = self.I - X
        result, term = self.I, self.I
        for _ in range(1, 2 * self.n + 1):
            term = term * N
            result += term
        check(term == 0)
        return result

    def commutator(self, X, Y):
        return self.inverse(X) * self.inverse(Y) * X * Y

    def factors(self, X):
        remaining = X
        result = []
        for r in self.roots:
            i, j = r
            t = remaining[self.indices.index(i), self.indices.index(j)]
            if t:
                result.append((r, t))
                remaining = self.x(r, -t) * remaining
        check(remaining == self.I)
        return result

    def relation_check(self, image, name):
        elements = list(self.ring)
        images = {(r, t): image(r, t) for r in self.roots for t in elements}
        inverses = {key: self.inverse(X) for key, X in images.items()}
        for r in self.roots:
            for t in elements:
                for u in elements:
                    check(images[r, t] * images[r, u] == images[r, t + u])
        pair_count = 0
        for ir, r in enumerate(self.roots):
            for s in self.roots[ir + 1:]:
                for t in elements:
                    for u in elements:
                        source_comm = self.commutator(self.x(r, t), self.x(s, u))
                        mapped_comm = self.I
                        for root, parameter in self.factors(source_comm):
                            mapped_comm *= images[root, parameter]
                        target_comm = (inverses[r, t] * inverses[s, u]
                                       * images[r, t] * images[s, u])
                        if mapped_comm != target_comm:
                            raise AssertionError((name, r, s, t, u, mapped_comm, target_comm))
                        check(mapped_comm == target_comm)
                        pair_count += 1
        print(f'{name}: all root additions and {pair_count} parameterized pairs')


# Verify the matrix signs against the printed C_n commutator in Lemma 3.
P = PolynomialRing(ZZ, names=('t', 'u'))
t, u = P.gens()
model = Symplectic(P, 3)
check(model.commutator(model.x((3, 2), t), model.x((2, -2), u))
      == model.I + t * u * model.basis[3, -2]
      - t ** 2 * u * model.basis[3, -3])


def mu_checks(ring, n, mu, mu1, name):
    """Equation (14), then every defining root relation under equation (15)."""
    elements = list(ring)
    a, two = mu(ring.one()), ring(2)
    for x in elements:
        check(2 * mu(x) == 0)
        check(2 * mu1(x) == mu(x) - a * x ** 2)
        for y in elements:
            check(mu1(x + y) == mu1(x) + mu1(y) + mu1(two) * x * y)
            check(mu(x * y) == a * x * y + y * mu(x) + mu(y) * x)
            check(2 * mu1(x) * (y ** 2 - y) == 0)
    M = Symplectic(ring, n)

    def image(r, y):
        if r == (n, n - 1):
            return M.x(r, y) * M.x((n, -n + 2), mu(y) + a * y)
        if r == (n - 1, n - 2):
            return (M.x((n - 1, -n + 1), mu(y))
                    * M.x((n, -n + 1), mu1(y))
                    * M.x((n, -n + 2), -mu1(two) * y) * M.x(r, y))
        if r == (n, n - 2):
            return (M.x(r, y) * M.x((n, -n + 1), mu(y))
                    * M.x((n, -n), y ** 2 * a))
        return M.x(r, y)

    M.relation_check(image, f'(14)/(15) {name}, n={n}')


mu_checks(GF(2), 3, lambda x: x, lambda x: 0, 'F2')
mu_checks(Integers(4), 3, lambda x: 2 * x ** 2, lambda x: 0, 'Z/4')
mu_checks(GF(4, 'w'), 4, lambda x: 0, lambda x: x ** 2, 'F4')


def psi_checks(ring, n, psi, name, corrected=True):
    """Equation (17), including the weak n=3 and strong n>=4 hypotheses."""
    elements = list(ring)
    for x in elements:
        check(2 * psi(x) == 0)
        for y in elements:
            check(psi(x + y) == psi(x) + psi(y))
            if n == 3:
                check(y * psi(x ** 2 - x) == psi(y ** 2 * (x ** 2 - x)))
            else:
                check(psi(y ** 2 * x) == y * psi(x))
    M = Symplectic(ring, n)

    def image(r, z):
        i, j = r
        if r == (1, -1):
            return M.x(r, z) * M.x((n, -1), psi(z ** 2 - z))
        if 1 < i < n and j == -i:
            return M.x(r, z) * M.x((n, -i), psi(z))
        if 1 < i < n and j == -1:
            coefficient = psi(z ** 2) if corrected else psi(ring.one()) * z
            return M.x(r, z) * M.x((n, -i), coefficient)
        return M.x(r, z)

    M.relation_check(image, f'(17) {name}, n={n}')
    # In characteristic 2 these shears square to the identity on all roots.
    for r in M.roots:
        for z in elements:
            twice = M.I
            for s, t0 in M.factors(image(r, z)):
                twice *= image(s, t0)
            check(twice == M.x(r, z))
    return M, image


F4 = GF(4, 'w')
for n in (3, 4):
    psi_checks(F4, n, lambda x: x ** 2, 'F4 inverse Frobenius')

# Printed missing psi on p. 332: psi=0, varpi=0 is admissible over F4.
w = F4.gen()
printed_varpi = w ** 2 - w
corrected_varpi = F4.zero()
check(printed_varpi != corrected_varpi)
check(corrected_varpi == (w ** 2 - w) * F4.zero())

# Perfect Boolean ring F2 x F2, realized as F2[e]/(e^2-e).
# Frobenius is bijective (indeed identity), and the factor swap is e -> 1+e.
B = PolynomialRing(GF(2), 'e')
e0 = B.gen()
R = B.quotient(e0 ** 2 - e0, 'e')
e = R.gen()


def swap(x):
    polynomial = x.lift()
    return R(polynomial(1 + e))


check(len({x ** 2 for x in R}) == len(list(R)))
check(all(x ** 2 == x for x in R))
check(swap(e) == 1 + e)
M, image = psi_checks(R, 3, swap, 'perfect Boolean product, factor swap')
c = swap(R.one())
printed_sqrt = c * e  # sqrt(e)=e since Frobenius is the identity.
check(swap(e) != printed_sqrt)
check(image((2, -2), e)
      == M.x((2, -2), e) * M.x((3, -2), 1 + e))
check(image((2, -2), e)
      != M.x((2, -2), e) * M.x((3, -2), printed_sqrt))
# The printed coefficient psi(1)*z in (17) already fails one relation.
# [x_21(1),x_1,-1(e)]=x_2,-1(e)x_2,-2(e) in characteristic two.
source_comm = M.commutator(M.x((2,1), R.one()), M.x((1,-1), e))
check(source_comm == M.x((2,-1), e) * M.x((2,-2), e))
printed_image_comm = (M.x((2,-1), e) * M.x((3,-2), c*e)
                      * image((2,-2), e))
check(printed_image_comm != source_comm)
check(image((2,-1), e) * image((2,-2), e) == source_comm)

# Equation (16), a nontrivial shear on the dual-number ring of four elements.
D = PolynomialRing(GF(2), 'd')
d0 = D.gen()
dual = D.quotient(d0 ** 2, 'd')
d = dual.gen()
check(all(d * (x ** 2 - x) == 0 for x in dual))
check((1+d) * (1+d) == 1)
shear = Symplectic(dual, 3)


def shear_image(r, x):
    if r[0] == 2 and r[1] in (-1,-2):
        return shear.x(r, x) * shear.x((2,-2), d*x)
    if r[0] == 3 and r[1] in (-1,-3):
        return (shear.x(r, x) * shear.x((3,-2), d*x)
                * shear.x((3,-3), d*x))
    return shear.x(r, x)


shear.relation_check(shear_image, '(16) dual numbers over F2, a=d')
for r in shear.roots:
    for x in dual:
        twice = shear.I
        for s, parameter in shear.factors(shear_image(r,x)):
            twice *= shear_image(s,parameter)
        check(twice == shear.x(r,x))
psi_checks(Integers(4), 3, lambda x: 2*x, 'Z/4')
psi_checks(dual, 3, lambda x: dual(x.lift()[0]), 'dual-number constant projection')

# The corrected n>=4 statement follows for every perfect char-2 ring:
# put x=1 and y=sqrt(t) in psi(y^2*x)=y*psi(x).
for degree in (1, 2, 3):
    field = GF(2 ** degree, 'v')
    for c in field:
        psi = lambda x: c * x ** (2 ** (degree - 1))
        for x in field:
            for y in field:
                check(psi(y ** 2 * x) == y * psi(x))


def exceptional(rank):
    L = RootSystem(['E', rank]).root_lattice()
    simple = L.simple_roots()
    roots = {tuple(r.to_vector()) for r in L.positive_roots()}
    check(len(roots) == {6: 36, 7: 63, 8: 120}[rank])
    check(max(map(sum, roots)) == {6: 11, 7: 17, 8: 29}[rank])
    # Check the Bourbaki Cartan matrix against literal plate edges.
    edges = {(1, 3), (2, 4), (3, 4), (4, 5), (5, 6)}
    edges |= {(i, i + 1) for i in range(6, rank)}
    expected = matrix(ZZ, rank)
    for i in range(rank):
        expected[i, i] = 2
    for i, j in edges:
        expected[i - 1, j - 1] = expected[j - 1, i - 1] = -1
    check(L.cartan_type().cartan_matrix() == expected)
    # Euclidean simple roots copied from Bourbaki plates V–VII, not from Sage.
    coordinate_basis = [vector(QQ, [int(i == j) for i in range(8)])
                        for j in range(8)]
    euclidean = [(coordinate_basis[0]+coordinate_basis[7]
                  -sum(coordinate_basis[1:7]))/2,
                 coordinate_basis[0]+coordinate_basis[1]]
    euclidean += [coordinate_basis[i]-coordinate_basis[i-1]
                  for i in range(1, rank-1)]
    check(matrix(QQ, [[a.dot_product(b) for b in euclidean]
                      for a in euclidean]) == expected)
    add = lambda r, s: tuple(a + b for a, b in zip(r, s))
    highest = {r for r in roots if sum(r) == max(map(sum, roots))}
    T = lambda i: {r for r in roots if r[i - 1] > 0}
    gamma = lambda i: {r for r in roots if sum(r) >= i}
    centralizer = lambda S, modulo=set(): {
        r for r in roots
        if all(add(r, s) not in roots or add(r, s) in modulo for s in S)
    }
    commutator = lambda A, B: {add(r, s) for r in A for s in B} & roots
    upper = lambda s: {r for r in roots if all(a >= b for a, b in zip(r, s))}
    if rank == 6:
        check(centralizer(gamma(10)) == set().union(*(T(i) for i in (1,3,4,5,6))))
        extra = (1, 0, 1, 1, 1, 1)
        check(extra in roots and sum(extra) == 5)
        check(centralizer(gamma(6), highest) == T(2) | {extra})
        check(centralizer(gamma(6), highest) != T(2))
        check(gamma(6) <= T(2))
        check((T(2)|{extra}) | gamma(2) == T(2) | gamma(2))
        check(centralizer(gamma(5), highest) != T(2))
        check(T(2) & centralizer(gamma(10)) == upper((0,1,0,1,0,0)))
        u, v = (0,1,0,1,0,0), (0,1,1,1,1,0)
        check(u in roots and v in roots)
        check(add(extra,u) in roots)
        check(add(add(extra,u),v) in highest)
        check(commutator(commutator(T(2),T(2)),T(2)) == set())
        alpha2 = (0,1,0,0,0,0)
        reachable = {alpha2}
        for height in range(2,11):
            for r in T(2):
                if r[1] != 1 or sum(r) != height:
                    continue
                predecessors = {
                    tuple(r[k]-(1 if j==k else 0) for k in range(6))
                    for j in range(6) if j != 1
                }
                check(bool(predecessors & reachable))
                reachable.add(r)
        check(reachable == {r for r in T(2) if r[1]==1})
        check({r for r in T(2) if r[1]==2} == highest)
        # delta is the highest A5 root and commutes with that whole subsystem.
        check(commutator({extra}, roots-T(2)) == set())
    if rank == 7:
        check(commutator(T(7), T(7)) == set())
        check(gamma(12) <= T(7))
        check(centralizer(gamma(12)) == T(7)
              | upper((0,1,0,1,1,1,0)) | upper((0,1,1,2,1,0,0)))
        extra = (1,2,2,3,2,1,0)
        check(extra in roots and sum(extra) == 11)
        check(centralizer(T(7) & gamma(7)) == T(7) | {extra})
        check(centralizer(T(7) & gamma(7)) != T(7))
        check(centralizer(T(7) & gamma(6)) == T(7))
        # Bounds used by the same normality descent down through height six:
        # seed is alpha7 modulo Gamma4; the root outside T7 can never survive
        # i-1 additions without exceeding the E6 subsystem's maximal height 11.
        for i in range(11,5,-1):
            allowed = centralizer(T(7)&gamma(i+1)) & centralizer(gamma(12))
            outside = allowed - T(7)
            check(all(sum(r)>=4 and sum(r)+i-1>11 for r in outside))
        alpha7 = (0,0,0,0,0,0,1)
        reachable = {alpha7}
        for height in range(2,18):
            for r in T(7):
                if sum(r) != height:
                    continue
                predecessors = {
                    tuple(r[k]-(1 if j==k else 0) for k in range(7))
                    for j in range(6)
                }
                check(bool(predecessors & reachable))
                reachable.add(r)
        check(reachable == T(7))
        check(centralizer(gamma(10), highest) == T(1) | gamma(7))
        check(centralizer(commutator(T(1), gamma(3)), highest) == T(1))
        # A normal nontrivial H and a central highest-root element refute H⊂[x,H].
        H = T(7)
        central_comm = commutator(highest, H)
        check(H != set() and central_comm == set())
        check(not H <= central_comm)
        check(central_comm <= H)
    if rank == 8:
        check(gamma(18) <= T(8))
        check(commutator(T(8), T(8)) <= highest)
        check(centralizer(gamma(18), highest) - T(8) <= gamma(10))
        check(commutator(T(8), gamma(8)) == T(8) & gamma(9))
        check(centralizer(T(8) & gamma(9), highest) == T(8))
        check(centralizer(gamma(28)) == set().union(*(T(i) for i in range(1,8))))
        check(T(8) & centralizer(gamma(28)) == upper((0,0,0,0,0,0,1,1)))
        check(len(roots - T(8)) == 63)
    print(f'E{rank}: exact root supports, Bourbaki numbering')


for rank in (6, 7, 8):
    exceptional(rank)

# Universal integral E6 triple commutator, needed for the local class-two
# repair of the false centralizer equality on p. 334.  The adjoint matrices
# are integral divided exponentials; no characteristic is inverted.
lie = LieAlgebra(ZZ, cartan_type='E6')
basis = lie.basis()
keys = list(basis.keys())
root_parent = keys[0].parent()
positive = {tuple(dict(r).get(i,0) for i in range(1,7)): r for r in keys
            if r.parent()==root_parent and all(c>=0 for _,c in r)}
Z = PolynomialRing(ZZ,'z')
z = Z.gen()
unit = identity_matrix(Z,78,sparse=True)
operators = {}
delta, u, v = (1,0,1,1,1,1), (0,1,0,1,0,0), (0,1,1,1,1,0)
theta = (1,2,2,3,2,1)
for r in (delta,u,v,theta):
    element = basis[positive[r]]
    ad = matrix(ZZ, [[element.bracket(basis[k]).monomial_coefficients().get(j,0)
                     for j in keys] for k in keys], sparse=True).transpose()
    check(ad**3 == 0)
    check(all(a%2==0 for a in (ad**2).list()))
    operators[r] = (ad.change_ring(Z), matrix(ZZ,ad**2/2).change_ring(Z))


def exceptional_x(r,t):
    ad,divided = operators[r]
    return unit+t*ad+t**2*divided


def unipotent_inverse(X):
    N, term, result = unit-X, unit, unit
    for _ in range(1,30):
        term = term*N
        result += term
        if term == 0:
            return result
    raise AssertionError('nilpotence bound')


def exceptional_comm(X,Y):
    return unipotent_inverse(X)*unipotent_inverse(Y)*X*Y


triple = exceptional_comm(exceptional_comm(exceptional_x(delta,z),
                                          exceptional_x(u,Z.one())),
                          exceptional_x(v,Z.one()))
check(triple in (exceptional_x(theta,z),exceptional_x(theta,-z)))
check(triple != unit)
print('E6: integral 78x78 adjoint triple commutator has coefficient ±z')

script = Path(__file__).resolve()
source = script.parents[3] / 'content' / 'papers' / 'l1990-chevalley' / '03-part.typ'
print(f'ok symplectic-exceptional: {checks} exact assertions; finite root-relation '
      'checks (14)–(17), perfect-ring counterexample, E6/E7/E8 root supports')
print('Limits: no general-ring classification, no proof of the omitted '
      'E7 characteristic descent or characteristic-subgroup theorems.')
print('SageVersion:', SAGE_VERSION)
print('UTC:', datetime.now(timezone.utc).isoformat())
print('elapsed_seconds:', round(perf_counter() - started, 3))
print('script_sha256:', sha256(script.read_bytes()).hexdigest())
print('content_sha256:', sha256(source.read_bytes()).hexdigest())
