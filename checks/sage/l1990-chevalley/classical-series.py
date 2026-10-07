"""Exact bounded checks of lemmas 7, 11 and formulas (12), (13).

Signed matrix units define C_n root groups; no tables of claimed central
series are used to construct the groups. Finite checks do not prove the
general central-series or automorphism classification statements.
"""

from itertools import product
from time import perf_counter
from sage.all import GF, ZZ, Zmod, PolynomialRing, identity_matrix, matrix

START = perf_counter()
CHECKS = 0


def check(condition):
    global CHECKS
    assert condition
    CHECKS += 1


def frozen(m):
    m.set_immutable()
    return m


def comm(a, b):
    return frozen(a.inverse() * b.inverse() * a * b)


class Symplectic:
    def __init__(self, n, ring):
        self.n, self.ring = n, ring
        self.labels = list(range(-n, 0)) + list(range(1, n + 1))
        self.pos = {v: k for k, v in enumerate(self.labels)}
        self.one = frozen(identity_matrix(ring, 2 * n))
        self.roots = [(i, j) for i in range(1, n + 1)
                      for j in range(-i, i) if j != 0]
        self.roots.sort(key=lambda r: (self.height(r), r))
        self.eps = {r: self.epsilon(*r) for r in self.roots}

    def unit(self, i, j):
        e = matrix(self.ring, 2 * self.n)
        e[self.pos[i], self.pos[j]] = 1
        return e

    def epsilon(self, i, j):
        e = self.unit(i, j)
        if j != -i:
            e += (-1 if j > 0 else 1) * self.unit(-j, -i)
        return frozen(e)

    @staticmethod
    def height(r):
        i, j = r
        return i - j if j > 0 else i - j - 1

    def x(self, r, t):
        return frozen(self.one + self.ring(t) * self.eps[r])

    def decomposition(self, m):
        rest, coordinates = m, []
        for r in self.roots:
            t = rest[self.pos[r[0]], self.pos[r[1]]]
            coordinates.append((r, t))
            rest = self.x(r, -t) * rest
        check(rest == self.one)
        return coordinates


def subgroup(one, generators):
    generators = list(set(generators) - {one})
    found, queue = {one}, [one]
    for a in queue:
        for b in generators:
            c = frozen(a * b)
            if c not in found:
                found.add(c)
                queue.append(c)
    return found


def normal_closure(one, seeds, generators):
    orbit, queue = set(seeds) - {one}, list(set(seeds) - {one})
    inverses = [g.inverse() for g in generators]
    for a in queue:
        for g, inverse in zip(generators, inverses):
            c = frozen(inverse * a * g)
            if c != one and c not in orbit:
                orbit.add(c)
                queue.append(c)
    return subgroup(one, orbit)


def lemma7(n, q):
    f = GF(q, 'a')
    c = Symplectic(n, f)
    generators = [c.x(r, t) for r in c.roots for t in f if t]
    group = subgroup(c.one, generators)
    check(len(group) == q ** (n * n))
    gamma = group
    sizes = [len(group)]
    upper = {c.one}
    upper_series = [upper]
    for i in range(1, 2 * n):
        upper = {a for a in group
                 if all(comm(a, b) in upper for b in generators)}
        upper_series.append(upper)
    for i in range(2, 2 * n + 1):
        gamma = normal_closure(c.one,
                               [comm(a, b) for a in gamma for b in generators],
                               generators)
        sizes.append(len(gamma))
        diagonal = {(t, -t) for t in range(1, min(i, n) + 1)}
        base = [c.x(r, a) for r in c.roots
                if c.height(r) >= i and r not in diagonal
                for a in f if a]
        extras = []
        if i <= n:
            extras = [comm(c.x((i, 1), a), c.x((1, -1), b))
                      for a in f for b in f]
        printed = subgroup(c.one, base + extras)
        corrected = subgroup(c.one,
                             [c.x(r, a) for r in c.roots
                              if c.height(r) >= i and r not in diagonal
                              and not (i <= n and r == (i, -1))
                              for a in f if a] + extras)
        check(gamma == corrected)
        if q == 2 and i <= n:
            check(printed != gamma)
            check(c.x((i, -1), 1) in printed)
            check(c.x((i, -1), 1) not in gamma)
        else:
            check(printed == gamma)
        if n == 3 and i == 2:
            l2 = subgroup(c.one, [c.x(r, a) for r in c.roots
                                 if c.height(r) >= 2 for a in f if a])
            check(subgroup(c.one, list(gamma | upper_series[3])) == l2)
            cross = subgroup(c.one, [c.x(r, a) for r in c.roots
                                     if r[1] < 0 for a in f if a])
            t2 = subgroup(c.one, [c.x(r, a) for r in c.roots
                                  if r[0] >= 2 and r[1] < 0
                                  for a in f if a])
            check(cross & l2 == t2)
    for i in range(1, 2 * n - 1):
        # In characteristic two Ann(2)=K, so L_{2n-i-1} includes L_{2n-i}.
        predicted = subgroup(c.one, [c.x(r, a) for r in c.roots
                                    if c.height(r) >= 2 * n - i - 1
                                    for a in f if a])
        check(predicted == upper_series[i])
    print('lemma7 C_%s GF(%s): lower orders %s; upper orders %s' %
          (n, q, sizes, [len(z) for z in upper_series]), flush=True)


def polynomial_checks():
    r = PolynomialRing(ZZ, 'x,y,u,v')
    x, y, u, v = r.gens()
    c = Symplectic(4, r)
    # Carter §5.2: rank-two B2/C2 root-string commutator, with the
    # publication's A^-1 B^-1 A B convention and signed basis.
    check(comm(c.x((2, 1), x), c.x((1, -1), y)) ==
          c.x((2, -1), x * y) * c.x((2, -2), -x * x * y))
    check(comm(c.x((2, 1), x), c.x((2, -1), y)) ==
          c.x((2, -2), 2 * x * y))
    # All summands in (12) have negative column indices: their matrices
    # multiply to zero, hence addition equals multiplication of I+M.
    cross = [c.eps[root] for root in c.roots if root[1] < 0]
    for a, b in product(cross, repeat=2):
        check(a * b == matrix(r, 8))
    check((c.one + x * c.eps[(4, -1)]) *
          (c.one + y * c.eps[(3, -1)]) ==
          c.one + x * c.eps[(4, -1)] + y * c.eps[(3, -1)])
    # Printed third lhs in (13) is constant. At c=d=0 its rhs takes
    # different values at t=0 and t=1; corrected lhs is the identity.
    check(c.x((2, 1), 0) != c.x((2, 1), 1))
    for t in (r(0), r(1), x):
        check(c.x((2, 1), t) == c.one + t * c.eps[(2, 1)])
    check((3, 5) not in c.roots)
    check((3, -3) in c.roots)
    # Universal matrix identity for lemma 5(d). Here xb=bar(x),
    # yb=bar(y), T=tilde(y), S=tilde(xy), and bar(T)=y*yb-T.
    u = PolynomialRing(ZZ, 'x,xb,y,yb,T,S')
    x, xb, y, yb, t, s = u.gens()
    labels = [-2, -1, 0, 1, 2]
    pos = {v: j for j, v in enumerate(labels)}
    def e(i, j):
        out = matrix(u, 5)
        out[pos[i], pos[j]] = 1
        return out
    one = identity_matrix(u, 5)
    a = one + xb * e(2, 1) - x * e(-1, -2)
    b = one + yb * e(1, 0) + y * e(0, -1) + t * e(1, -1)
    xy = one + xb * yb * e(2, 0) + x * y * e(0, -2) + s * e(2, -2)
    cross = one + xb * t * e(2, -1) - x * (y * yb - t) * e(1, -2)
    central = one + (x * xb * (y * yb - t) - s) * e(2, -2)
    check(comm(a, b) == xy * cross * central)


def larger_lower(n, q):
    f, c = GF(q), Symplectic(n, GF(q))
    generators = [c.x(r, t) for r in c.roots for t in f if t]
    # [G,G] is the normal closure of commutators of generators; there is
    # no need to enumerate G to compute its successive lower central terms.
    gamma = normal_closure(c.one, [comm(a, b) for a in generators
                                   for b in generators], generators)
    sizes = []
    for i in range(2, 2 * n + 1):
        if i > 2:
            gamma = normal_closure(c.one, [comm(a, b) for a in gamma
                                          for b in generators], generators)
        sizes.append(len(gamma))
        diagonal = {(t, -t) for t in range(1, min(i, n) + 1)}
        base = [c.x(r, a) for r in c.roots if c.height(r) >= i
                and r not in diagonal for a in f if a]
        extra = [c.x((t, -t), 2 * a) for t in range(1, n + 1)
                 if 2 * t > i and (i > n or t < i) for a in f]
        if i <= n:
            extra += [comm(c.x((i, 1), a), c.x((1, -1), b))
                      for a in f for b in f]
        printed = subgroup(c.one, base + extra)
        corrected = subgroup(c.one, [c.x(r, a) for r in c.roots
                                    if c.height(r) >= i and r not in diagonal
                                    and not (i <= n and r == (i, -1))
                                    for a in f if a] + extra)
        check(corrected == gamma)
        check((printed != gamma) == (q == 2 and i <= n))
    print('lemma7 C_%s GF(%s): lower orders from Gamma2 %s' %
          (n, q, sizes), flush=True)


def split_sl2():
    r = PolynomialRing(ZZ, 'a,b,c,d')
    a, b, c, d = r.gens()
    det_relation = a * d - b * c - 1
    # Universal integer polynomial certificates; a*b=c*d=0 and det=1.
    check((a * d) ** 2 - a * d == a * d * det_relation + a * b * c * d)
    check((-b * c) ** 2 + b * c == -b * c * det_relation + a * b * c * d)
    check(a * (a * d) - a == a * det_relation + a * b * c)
    check(d * (a * d) - d == d * det_relation + b * c * d)
    check(b * (-b * c) - b == b * det_relation - a * b * d)
    check(c * (-b * c) - c == c * det_relation - a * c * d)
    k = Zmod(6)
    count = 0
    for a, b, c, d in product(k, repeat=4):
        if a * d - b * c != 1 or a * b or c * d:
            continue
        e, f = a * d, -b * c
        check(e + f == 1 and e * f == 0 and e * e == e and f * f == f)
        ideal = lambda t: {z * t for z in k}
        check(ideal(a) == ideal(d) == ideal(e))
        check(ideal(b) == ideal(c) == ideal(f))
        count += 1
    print('lemma11 SL2 Z/6: %s admissible matrices' % count, flush=True)


def eq13():
    k, n = Zmod(4), 4
    c = Symplectic(n, k)
    j2 = {x * x - x for x in k}
    pairs = [(a, b) for a in k for b in k
             if 2 * a == 0 and all(b * z == 0 for z in j2)
             and all(a * z * w == 0 for z in j2 for w in j2)]
    for a, b in pairs:
        def image(r, t):
            v = t * c.eps[r]
            if r == (4, 3):
                v += b * t * c.eps[(2, -1)]
            elif r == (3, 2):
                v += a * t * c.eps[(4, -1)]
            elif r == (2, 1):
                v += b * t * c.eps[(2, -2)]
                v += a * (t * t - t) * c.eps[(4, -2)]
            elif r == (4, 2):
                v += b * t * (c.eps[(3, -1)] + c.eps[(4, -1)])
            elif r == (3, 1):
                v += b * t * (c.eps[(3, -2)] + c.eps[(3, -3)])
                v += a * t * c.eps[(4, -2)]
                v += a * t * t * c.eps[(4, -3)]
            elif r == (4, 1):
                v += b * t * (c.eps[(3, -2)] + c.eps[(4, -3)]
                              + c.eps[(4, -4)])
            return frozen(c.one + v)

        def phi(m):
            out = c.one
            for r, t in c.decomposition(m):
                out = out * image(r, t)
            return frozen(out)

        for r in c.roots:
            for t in k:
                coords = dict(c.decomposition(image(r, t)))
                check(coords[r] == t)
                check(all(not value for s, value in coords.items()
                          if s != r and c.height(s) <= c.height(r)))
            for t, u in product(k, repeat=2):
                check(image(r, t + u) == image(r, t) * image(r, u))
        for r, s in product(c.roots, repeat=2):
            for t, u in product(k, repeat=2):
                check(phi(comm(c.x(r, t), c.x(s, u))) ==
                      comm(image(r, t), image(s, u)))
    print('eq13 C4 Z/4: %s admissible (c,d); all root pairs and parameters' %
          len(pairs), flush=True)


def traces():
    for q, p in ((4, 2), (9, 3)):
        k = GF(q, 'a')
        for sign in (1, -1):
            image = {x + sign * x ** p for x in k}
            kernel = {x for x in k if x - sign * x ** p == 0}
            check(image == kernel)
            ann = {x for x in kernel if all(x * z == 0 for z in image)}
            check(ann == {k(0)})
    k = Zmod(4)
    check({x - x for x in k} != {x for x in k if x + x == 0})
    check({x + x for x in k} != set(k))


def unitary_relations():
    k = GF(9, 'a')
    bar = lambda x: x ** 3
    labels = [-2, -1, 0, 1, 2]
    pos = {v: j for j, v in enumerate(labels)}
    one = identity_matrix(k, 5)
    def e(i, j):
        out = matrix(k, 5)
        out[pos[i], pos[j]] = 1
        return out
    def root(i, j, x):
        if j == -i:
            return one + x * e(i, j)
        if j > 0:
            return one + bar(x) * e(i, j) - x * e(-j, -i)
        return one - bar(x) * e(i, j) + x * e(-j, -i)
    tilde = {x: next(z for z in k if z + bar(z) == x * bar(x))
             for x in k}
    tilde[k(0)] = k(0)
    def short(i, x):
        return one + bar(x) * e(i, 0) + x * e(0, -i) + tilde[x] * e(i, -i)
    anti = [z for z in k if z + bar(z) == 0]
    # Explicit printed counterexample using the valid global choice
    # tilde(x)=norm(x)/2 (division is by the unit 2 in GF9).
    canonical = {x: x * bar(x) * k(2).inverse() for x in k}
    check(all(z + bar(z) == x * bar(x) for x, z in canonical.items()))
    check(canonical[k(0)] == 0 and canonical[k(1)] == k(2))
    check(bar(canonical[k(1)]) - 1 == 1 and k(1) + bar(k(1)) != 0)
    refuted = 0
    for x, y in product(k, repeat=2):
        check(comm(short(1, x), short(2, y)) == root(2, -1, bar(x) * y))
        check(comm(root(2, 1, x), root(2, -1, y)) ==
              root(2, -2, bar(x) * y - x * bar(y)))
        check(short(2, x) * short(2, y) == short(2, x + y) *
              root(2, -2, tilde[x] + tilde[y] - tilde[x + y] + bar(x) * y))
        corrected = x * bar(x) * bar(tilde[y]) - tilde[x * y]
        printed = x * bar(x) * bar(tilde[y]) - x * y
        lhs = comm(root(2, 1, x), short(1, y))
        check(lhs == short(2, x * y) * root(2, -1, -x * bar(tilde[y])) *
              root(2, -2, corrected))
        check(corrected + bar(corrected) == 0)
        if printed != corrected:
            check(lhs != short(2, x * y) * root(2, -1, -x * bar(tilde[y])) *
                  root(2, -2, printed))
            refuted += 1
        for z in anti:
            check(comm(root(2, 1, x), root(1, -1, z)) ==
                  root(2, -1, x * z) * root(2, -2, -bar(x) * x * z))
    check(refuted > 0)
    print('lemma5 unitary GF9: all 81 (x,y); printed (d) refuted %s times' %
          refuted, flush=True)
    # Lemmas 8 and 10: Frobenius involution has surjective trace onto
    # its fixed field and image(1-sigma)=ker(1+sigma). Compute the lower
    # series independently in the resulting rank-two unitary group.
    root_groups = [(1, [root(2, 1, x) for x in k]),
                   (1, [short(1, x) for x in k]),
                   (2, [short(2, x) for x in k]),
                   (2, [root(1, -1, z) for z in anti]),
                   (3, [root(2, -1, x) for x in k]),
                   (4, [root(2, -2, z) for z in anti])]
    one = frozen(one)
    gens = [frozen(g) for _, roots in root_groups for g in roots if g != one]
    hermitian = matrix(k, 5)
    for i in labels:
        hermitian[pos[i], pos[-i]] = -1 if i == 0 else 1
    for g in gens:
        conjugate_transpose = matrix(k, 5, 5,
                                    [bar(z) for z in g.transpose().list()])
        check(conjugate_transpose * hermitian * g == hermitian)
        check(g.det() == 1)
    gamma = normal_closure(one, [comm(a, b) for a in gens for b in gens], gens)
    orders = []
    for i in range(2, 6):
        if i > 2:
            gamma = normal_closure(one, [comm(a, b) for a in gamma for b in gens],
                                   gens)
        expected = subgroup(one, [frozen(g) for h, roots in root_groups
                                  if h >= i for g in roots])
        check(gamma == expected)
        orders.append(len(gamma))
    print('lemma8 unitary A4 GF9: lower orders from Gamma2 %s' % orders,
          flush=True)


polynomial_checks()
split_sl2()
traces()
unitary_relations()
eq13()
lemma7(2, 2)
lemma7(3, 2)
lemma7(2, 4)
larger_lower(4, 2)
larger_lower(3, 3)
print('ok classical-series: %s checks; %.3fs' %
      (CHECKS, perf_counter() - START))
