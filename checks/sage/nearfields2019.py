"""Exact bounded checks for Questions of the structure of finite near-fields.

Passages: eq:l2019-nearfields-descending-chain,
lem:l2019-nearfields-metacyclic, th:l2019-nearfields-spectrum,
exm:l2019-nearfields-order25, exm:l2019-nearfields-lattice.
This checks arithmetic and two finite multiplicative group models;
it does not prove classification or the center/kernel theorem.
"""

from collections import Counter
from datetime import datetime, timezone
from hashlib import sha256
from pathlib import Path

from sage.all import GF, SL, ZZ, divisors, gcd, prime_divisors, version


def model(q, n):
    m = ZZ((q**n - 1) // n)
    t = m // (q - 1)
    assert m * n == q**n - 1 and t * (q - 1) == m
    assert (q**n - 1) % m == 0 and ((q - 1) * t) % m == 0
    elements = [(k, s) for k in range(m) for s in range(n)]

    def mul(x, y):
        k, s = x
        ell, r = y
        return ((k + q**s * ell + t * ((s + r) // n)) % m,
                (s + r) % n)

    def power(x, z):
        result = (0, 0)
        for _ in range(z):
            result = mul(result, x)
        return result

    def order(x):
        return next(z for z in divisors(m * n) if power(x, z) == (0, 0))

    for x in elements:
        assert mul(x, (0, 0)) == x == mul((0, 0), x)
        assert any(mul(x, y) == (0, 0) == mul(y, x) for y in elements)
        for y in elements:
            for z in elements:
                assert mul(mul(x, y), z) == mul(x, mul(y, z))
    a, b = (1, 0), (0, 1)
    assert power(a, m) == (0, 0)
    assert power(b, n) == power(a, t)
    assert mul(b, a) == mul(power(a, q), b)
    for x in elements:
        k, s = x
        actual = order(x)
        expected = next(z for z in divisors(m * n)
                        if z * s % n == 0
                        and (k * sum(q**(i * s) for i in range(z))
                             + t * (z * s // n)) % m == 0)
        assert actual == expected
    center = [x for x in elements if all(mul(x, y) == mul(y, x)
                                        for y in elements)]
    assert set(center) == {power(a, t * k) for k in range(q - 1)}
    return elements, mul, power, order, center, m, t


E5, mul5, pow5, order5, C5, m5, t5 = model(ZZ(5), 2)
assert Counter(map(order5, E5)) == {1: 1, 2: 1, 3: 2, 4: 2, 6: 2, 8: 12, 12: 4}
assert Counter(x.order() for x in SL(2, GF(3))) == {
    1: 1, 2: 1, 3: 8, 4: 6, 6: 8}
# The printed Q*/Z(Q*) is not cyclic: ab and ba differ modulo the center.
ab, ba = mul5((1, 0), (0, 1)), mul5((0, 1), (1, 0))
assert ab not in [mul5(ba, z) for z in C5]
E7, mul7, pow7, order7, C7, m7, t7 = model(ZZ(7), 2)
# The printed spectrum condition omits n | zs. All printed assumptions hold.
q, n, k, s, z = ZZ(7), 2, 22, 1, 1
assert all((q - 1) % r == 0 for r in prime_divisors(n))
assert (q**n - 1) % z == 0
assert (k * (q**(z*s) - 1) // (q**s - 1) + ZZ(z*s*t7)/n) % m7 == 0
assert pow7((k, s), z) != (0, 0)
assert pow7((k, s), 2) == (12, 0) and order7((k, s)) == 4


def subpairs(p, ell, n):
    out = {}
    for h in divisors(ell * n):
        j = ((p**(ell*n) - 1) // (p**h - 1)) % n
        j = j or n
        z = gcd(j * ell, h)
        out[h] = (z, h // z)
    return out


def maximal_fields(p, ell, n):
    fields = [h for h, (_, degree) in subpairs(p, ell, n).items()
              if degree == 1]
    return [h for h in fields if not any(k > h and k % h == 0 for k in fields)]


assert maximal_fields(ZZ(2), 4, 15) == [4, 10, 15]
assert maximal_fields(ZZ(2), 4, 45) == [12, 30, 45]
assert subpairs(ZZ(2), 4, 45)[90] == (10, 9)
assert subpairs(ZZ(2), 4, 45)[36] == (4, 9)
assert subpairs(ZZ(2), 4, 45)[60] == (12, 5)
assert maximal_fields(ZZ(5), 3, 2) == [3]
assert maximal_fields(ZZ(5), 2, 3) == [2, 3]
# Check the first part of Theorem 2 on a finite explicitly bounded set.
cases = 0
for p in (ZZ(2), ZZ(3), ZZ(5), ZZ(7)):
    for ell in range(1, 5):
        q = p**ell
        for n in range(2, 37):
            if any((q - 1) % r for r in prime_divisors(n)):
                continue
            if q % 4 == 3 and n % 4 == 0:
                continue
            pairs = subpairs(p, ell, n)
            for r in prime_divisors(n):
                h = ell * n // r
                expected = (ell, n // r) if n % (r*r) else (ell*r, n // (r*r))
                assert pairs[h] == expected, (p, ell, n, r, pairs[h], expected)
                assert ell * n // h == r
                cases += 1
print({'system': version(), 'utc': datetime.now(timezone.utc).isoformat(),
       'sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
       'finite_groups': [len(E5), len(E7)], 'theorem2_cases': cases,
       'scope': 'finite pair models, full order counts, finite subfield arithmetic',
       'corrections': ['descending quotient', 'noncyclic central quotient',
                       'spectrum needs n divides zs']})
