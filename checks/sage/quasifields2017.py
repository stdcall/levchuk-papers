"""Exact limited checks for the 2017 quasifield paper.

Passages: sec:l2017-quasifields-orders (the displayed field K);
lem:l2017-quasifields-single-square-power (binary-tree shape, through 10
leaves); th:l2017-quasifields-order16-isomorphism (index-list audit only).
These checks do not prove classification or the general loop statements.
"""
from functools import lru_cache
from hashlib import sha256
from pathlib import Path
from datetime import datetime, timezone
from sage.all import GF, identity_matrix, matrix
from sage.env import SAGE_VERSION

F = GF(3)
I = identity_matrix(F, 2)
A = matrix(F, [[1, 1], [1, 0]])
K = [a * A + b * I for a in F for b in F]
assert len({tuple(x.list()) for x in K}) == 9
zero = 0 * I
assert all(x.det() != 0 for x in K if x != zero)
assert all(x * y in K for x in K for y in K)
assert all(x + y in K for x in K for y in K)
assert all(x * y == y * x for x in K for y in K)
assert A * A == A + I

@lru_cache(None)
def trees(n):
    if n == 1:
        return (None,)
    return tuple((l, r) for k in range(1, n)
                 for l in trees(k) for r in trees(n-k))

def cherries(t):
    if t is None:
        return 0
    l, r = t
    return int(l is None and r is None) + cherries(l) + cherries(r)

def comb(t):
    if t is None:
        return True
    l, r = t
    return (l is None and comb(r)) or (r is None and comb(l))

count = 0
for n in range(2, 11):
    for t in trees(n):
        count += 1
        if cherries(t) <= 1:
            assert comb(t), (n, t)

left = [1, 3, 4, 8, 11, 15]
opposite = [6, 7, 5, 9, 14, 16]
self_opposite = [2, 10, 12, 13, 17, 18]
assert sorted(left + opposite + self_opposite) == list(range(1, 19))
assert len({24, 25, 35, 45, 50}) == 5
table3 = [[1,961,961,180,186,186],
          [0,0,0,6,0,7], [0,0,0,6,7,0], [0,0,0,1,0,0]]
assert sum(map(sum, table3)) - 1 == 2501

print("Sage", SAGE_VERSION)
print("UTC", datetime.now(timezone.utc).isoformat())
print("script SHA256", sha256(Path(__file__).read_bytes()).hexdigest())
print("K: all 81 products, 81 sums, 8 nonzero determinants checked")
print("single-cherry binary trees: all", count, "bracketings, 2–10 leaves")
print("classification index partition and Table 3 count: checked")
