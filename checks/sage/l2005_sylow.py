"""Exact bounded checks for Proposition 1, printed pp. 228–229.

Test series inverses over a noncommutative division ring and intermediate
ideals of two truncated series rings. These finite checks do not prove
strong maximality over arbitrary division rings or the article's group
classifications.
"""

import json

from sage.all import GF, QQ, QuaternionAlgebra, VectorSpace


checks = 0


def check(statement):
    global checks
    assert statement
    checks += 1


D = QuaternionAlgebra(QQ, -1, -1)
i, j, k = D.gens()
precision = 7


def multiply(a, b):
    return [
        sum((a[r] * b[n - r] for r in range(n + 1)), D.zero())
        for n in range(precision)
    ]


one = [D.one()] + [D.zero()] * (precision - 1)
for a in (
    [D(2), i, j, k, i + j, j + k, k + i],
    [i, 1 + j, k, 2, i * j, j * k, k * i],
    [1 + i + j, 2 * k, i - j, 1, 2, 3, k],
):
    b = [~a[0]]
    for n in range(1, precision):
        b.append(
            -(~a[0])
            * sum((a[r] * b[n - r] for r in range(1, n + 1)), D.zero())
        )
    check(multiply(a, b) == one)
    check(multiply(b, a) == one)
    for t in range(precision):
        f = [D.zero()] * t + a[: precision - t]
        check(next((r for r, c in enumerate(f) if c), precision) == t)

models = []
for p, precision in [(2, 5), (3, 4)]:
    F = GF(p)
    V = VectorSpace(F, precision)

    def shift(v):
        return V([0] + list(v)[:-1])

    ideals = [
        V.subspace([V.gen(r) for r in range(t, precision)])
        for t in range(precision + 1)
    ]
    count = 0
    for dimension in range(precision + 1):
        for T in V.subspaces(dimension):
            if not all(shift(v) in T for v in T.basis()):
                continue
            count += 1
            JT = V.subspace([shift(v) for v in T.basis()])
            for S in ideals:
                if JT.is_subspace(S) and S.is_subspace(T):
                    check(S == JT or S == T)
    models.append(
        {"p": p, "truncation": precision, "stable_subspaces": count}
    )

print(f"ok l2005-sylow: {checks} checks")
print(json.dumps({"assertions": checks, "models": models}))
