"""Exact checks for printed pages 155--159; no classification theorem is proved.

The F4 checks use its integral Chevalley adjoint representation, with the
positive-root coordinates used in the article. In characteristic two the signs
of the Chevalley basis disappear. A and B denote bar(a) and bar(b). Applying
bar to a squared barred variable uses bar(bar(x))^2 = x, as required in §6.
The matrices are compared over F2[a,A,b,B], so the main relation checks are
polynomial identities rather than tests at a few finite-field values.
"""

from itertools import product
from datetime import datetime, timezone
from hashlib import sha256
from pathlib import Path
import json
from sage.version import version as sage_version
from sage.all import (
    GF, ZZ, LieAlgebra, PolynomialRing, factorial, identity_matrix, matrix,
    prod, vector,
)

lie = LieAlgebra(ZZ, cartan_type="F4")
basis = lie.basis()
keys = list(basis.keys())
root_parent = keys[0].parent()
positive = {
    tuple(dict(r).get(i, 0) for i in range(1, 5)): r
    for r in keys
    if r.parent() == root_parent and all(c >= 0 for _, c in r)
}
roots = {
    "p21": (0, 0, 1, 0), "q21": (0, 1, 0, 0),
    "p32": (0, 0, 0, 1), "q32": (1, 0, 0, 0),
    "p2n1": (0, 1, 1, 0), "q2n1": (0, 1, 2, 0),
    "p31": (0, 0, 1, 1), "q31": (1, 1, 0, 0),
    "p3n1": (0, 1, 1, 1), "q3n1": (1, 1, 2, 0),
    "p3n2": (0, 1, 2, 1), "q3n2": (1, 2, 2, 0),
    "p43": (1, 1, 1, 0), "q43": (0, 1, 2, 2),
    "p42": (1, 1, 1, 1), "q42": (1, 1, 2, 2),
    "p41": (1, 1, 2, 1), "q41": (1, 2, 2, 2),
    "p4n1": (1, 2, 2, 1), "q4n1": (1, 2, 4, 2),
    "p4n2": (1, 2, 3, 1), "q4n2": (1, 3, 4, 2),
    "p4n3": (1, 2, 3, 2), "q4n3": (2, 3, 4, 2),
}
assert set(roots.values()) == set(positive)
integral = {}
for name, root in roots.items():
    e = basis[positive[root]]
    ad = matrix(
        ZZ,
        [[e.bracket(basis[k]).monomial_coefficients().get(j, 0)
          for j in keys] for k in keys],
        sparse=True,
    ).transpose()
    assert (ad**3).is_zero()
    assert all(c % 2 == 0 for c in (ad * ad).list())
    integral[name] = ad, (ad * ad) / 2

ring = PolynomialRing(GF(2), names=("a", "A", "b", "B"))
a, A, b, B = ring.gens()
unit = identity_matrix(ring, 52, sparse=True)
operators = {
    name: (ad.change_ring(ring), divided.change_ring(ring))
    for name, (ad, divided) in integral.items()
}
extra = {"21": "p2n1", "43": "p4n3", "31": "p42", "3n1": "p4n2"}


def x(name, t):
    ad, divided = operators[name]
    return unit + t * ad + t * t * divided


def R(name, t, barred):
    result = x("p" + name, barred) * x("q" + name, t)
    if name in extra:
        result *= x(extra[name], t * barred)
    return result


def inverse_R(name, t, barred):
    result = unit
    if name in extra:
        result *= x(extra[name], t * barred)
    return result * x("q" + name, t) * x("p" + name, barred)


def comm(n, t, T, m, u, U):
    return inverse_R(n, t, T) * inverse_R(m, u, U) * R(n, t, T) * R(m, u, U)


# Page 155: q31 in the first displayed commutator must be q21.
printed155 = x("p2n1", a * b) * x("q2n1", a * b * b)
assert x("q31", a) * x("p21", b) * x("q31", a) * x("p21", b) != printed155
assert x("q21", a) * x("p21", b) * x("q21", a) * x("p21", b) == printed155

# Page 156, formulas (10)/(11): zero parameters in the printed leading
# root substitutions collapse two distinct root elements. GF4 satisfies
# Ann(J2)=0, whereas GF2 satisfies J2=0.
field4 = GF(4, "v")
j2_4 = [t * t - t for t in field4]
assert any(j2_4)
assert [s for s in field4 if all(s * j == 0 for j in j2_4)] == [field4(0)]
field2 = GF(2)
assert all(t * t == t for t in field2)
for field, left, right in [
    (field4, "p3n1", "q3n1"), (field2, "q32", "p32"),
]:
    def root_element(name):
        ad, divided = integral[name]
        return identity_matrix(field, 52) + ad.change_ring(field) + divided.change_ring(field)
    assert root_element(left) != root_element(right)

# The two overlines in §6 distinguish inverse Tits from inverse Frobenius.
field8 = GF(8, "w")
assert all(((t**2)**2)**2 == t for t in field8)
assert any((t**2)**2 != t for t in field8)

# Lemma 4(1): all nonadditive root groups, with both possible extra roots.
for name, target in [("21", "2n1"), ("43", "4n3"), ("31", "42"), ("3n1", "4n2")]:
    assert R(name, a, A) * R(name, b, B) == (
        R(name, a + b, A + B) * R(target, a * B * B, A * b)
    )
for name in ["32", "2n1", "3n2", "42", "41", "4n1", "4n2", "4n3"]:
    assert R(name, a, A) * R(name, b, B) == R(name, a + b, A + B)

names = {
    (2, 1): "21", (2, -1): "2n1", (3, 2): "32", (3, 1): "31",
    (3, -1): "3n1", (3, -2): "3n2", (4, 3): "43", (4, 2): "42",
    (4, 1): "41", (4, -1): "4n1", (4, -2): "4n2", (4, -3): "4n3",
}
zero_count = 0
for (i, k), n in names.items():
    for (j, m), v in names.items():
        zero = (
            {i, abs(k), abs(m), j} == {1, 2, 3, 4}
            or (i == j != 3 and k != m)
            or (i == j == 3 and k * m in (-1, 2))
            or (i == 4 and j == 3 and k == m)
            or (k < 0 and m < 0 and (i, k) != (3, -1))
            or k == -j
        )
        if zero:
            assert comm(n, a, A, v, b, B) == unit
            zero_count += 1

# Lemma 4(3) and (8).
for (i, sigma), n in names.items():
    for j in range(2, i):
        if 1 <= abs(sigma) < j and (i, sigma) != (3, 1):
            assert comm(n, a, A, names[j, -sigma], b, B) == R(names[i, -j], a*b, A*B)
for sigma in [-2, -1, 1, 2]:
    assert comm("43", a, A, names[3, sigma], b, B) == R(names[4, sigma], a*b, A*B)

lhs5a = comm("32", a, A, "3n1", b, B)
prefix5a = R("42", A*A*b, a*B) * R("41", a*B*B, A*b)
lhs5b = comm("3n2", a, A, "31", b, B)
prefix5b = R("4n2", A*A*b, a*B) * R("4n1", a*B*B, A*b)
assert lhs5a != prefix5a * R("4n3", a*A*A*b, A*a*B)
# If the weak first stroke in 5(a) is another overline, the parameter is
# A^3 b. In GF8 bar(bar(a))=a^4, so its barred value is a^5 B.
w = field8.gen()
evaluate8 = ring.hom([w, w**2, w**2, w**4], field8)
assert lhs5a.apply_map(evaluate8) != (prefix5a * R("4n3", A**3*b, a**5*B)).apply_map(evaluate8)
assert lhs5b != prefix5b * R("4n3", A*A*a*b, a*A*B)

lhs6 = comm("31", a, A, "21", b, B)
printed6 = R("3n2", a*b*B*B, A*b*B) * inverse_R("43", A*A*b, a*B) * R("3n1", a*B*B, A*b)
assert lhs6 != printed6

lhs7 = comm("41", a, A, "21", b, B)
prefix7 = R("4n1", a*B*B, A*b) * R("4n2", a*b*B*B, A*b*B)
# The original last parameter a bar(b) involves a second barred variable.
# Test it directly at a=b=1, where every barred value is 1.
one = {a: 1, A: 1, b: 1, B: 1}
def specialize(M):
    return M.apply_map(lambda t: t.subs(one))
assert specialize(lhs7) != specialize(prefix7 * R("4n1", 1, 1))

lhs10 = comm("32", a, A, "21", b, B)
printed10 = R("43", b*A*A*B*B, a*b*B) * inverse_R("31", a*b, A*B) * R("3n2", a*B*B*b*b, A*b*B*B)
assert lhs10 != printed10

lhs11 = comm("32", a, A, "2n1", b, B)
prefix11 = R("3n1", a*b, A*B) * inverse_R("43", A*A*b, a*B)
suffix11 = R("41", a*A*A*B*B, A*a*b) * R("42", A*A*a*b, a*A*B)
assert lhs11 != prefix11 * R("3n1", a*B*B, A*b) * suffix11

identities = {
    "4a": (comm("31", a, A, "2n1", b, B),
           R("3n2", a*b, A*B) * R("4n2", a*A*A*B*B, A*a*b) * R("4n3", A*A*a*a*b, a*A*A*B)),
    "4b": (comm("32", a, A, "3n2", b, B),
           R("41", A*A*b, a*B) * R("4n1", a*B*B, A*b)),
    "5a": (lhs5a, prefix5a * R("4n3", a*B*B*b, A*b*B)),
    "5b": (lhs5b, prefix5b * R("4n3", a*B*B*b, A*b*B)),
    "6": (lhs6, printed6 * R("41", A*A*a*b, a*A*B)),
    "7": (lhs7, prefix7 * R("4n3", A*A*b, a*B)),
    "9a": (comm("42", a, A, "21", b, B),
           R("41", a*b, A*B) * R("4n2", a*b*b*B*B, A*B*B*b) * R("4n3", A*A*B*B*b, a*b*B)),
    "9b": (comm("42", a, A, "2n1", b, B),
           R("4n1", a*b, A*B) * R("4n2", a*B*B, A*b) * R("4n3", A*A*b, a*B)),
    "10": (lhs10, printed10 * R("4n1", a*A*A*b*b*B**4, a*A*b*b*B*B)
           * R("4n2", a*A*A*b**3*B**4, a*A*b*b*B**3)),
    "11": (lhs11, prefix11 * R("3n2", a*B*B, A*b) * suffix11),
}
for name, (left, right) in identities.items():
    assert left == right, name
print(f"F4: 24 integral root operators; all lemma 4 relations, including {zero_count} zero cases.")

# Page 159: the matrices in (12) act faithfully as the full S4.
F = GF(2)
def satisfies12(mat):
    if any(prod(mat[i, j] for j in range(3)) for i in range(3)):
        return False
    for i in range(3):
        for j in range(3):
            if i != j and sum(
                mat[i, k]*mat[j, (k+1)%3]*mat[j, (k+2)%3]
                + mat[j, k]*mat[i, (k+1)%3]*mat[i, (k+2)%3]
                for k in range(3)
            ):
                return False
    return True

sl = [matrix(F, 3, 3, entries) for entries in product(F, repeat=9)
      if matrix(F, 3, 3, entries).det() == 1]
group = [mat for mat in sl if satisfies12(mat)]
odd = [vector(F, entries) for entries in product(F, repeat=3) if sum(entries) == 1]
actions = {tuple(odd.index(mat*v) for v in odd) for mat in group}
assert len(sl) == 168 and len(group) == 24 and len(actions) == factorial(4)
for mat in group:
    assert vector(F, [1, 1, 1])*mat == vector(F, [1, 1, 1])
    assert mat.inverse() in group
    for other in group:
        assert mat*other in group

# Cramer's sum, with every hypothesis and coordinate equation enforced.
poly = PolynomialRing(F, "e")
e = poly.gen()
dual = poly.quotient(e*e, "eps")
eps = dual.gen()
beta = matrix(dual, [[1, 1, 0], [1, 0, 1], [1, 0, 0]])
assert beta.det() == 1 and satisfies12(beta)
cofactor = matrix(dual, 3, 3, lambda i, j: (-1)**(i+j) *
    beta.matrix_from_rows_and_columns(
        [k for k in range(3) if k != i], [k for k in range(3) if k != j]
    ).det())
j2 = [t*t-t for t in dual]
assert set(j2) == {dual(0), eps} and all(x*y == 0 for x in j2 for y in j2)
coefficients = []
for k in range(3):
    options = [sum(cofactor[i, m]*beta[i, m]*beta[i, k] for i in range(3))
               for m in range(3) if m != k]
    assert options[0] == options[1]
    coefficients.append(options[0])
assert coefficients == [dual(1), dual(0), dual(0)]
for t in dual:
    lam = [(t*t-t)*v for v in coefficients]
    for i in range(3):
        for m in range(3):
            for k in range(3):
                if m == k:
                    continue
                assert beta[i, m]*lam[k]+beta[i, k]*lam[m] == beta[i, m]*beta[i, k]*(t*t-t)
                for z in dual:
                    coordinate = lam[k]*beta[i, m]*z+lam[m]*beta[i, k]*z+beta[i, m]*beta[i, k]*z*z*t
                    assert coordinate == beta[i, m]*beta[i, k]*(z*t)**2
for c in coefficients:
    assert all(((x+y)**2-(x+y))*c == (x*x-x)*c+(y*y-y)*c for x in dual for y in dual)
sum_value = sum(cofactor[i, 1]*beta[i, 1]*beta[i, 0] for i in range(3))
product_value = prod(cofactor[i, 1]*beta[i, 1]*beta[i, 0] for i in range(3))
assert sum_value == 1 and product_value == 0
assert (eps*eps-eps)*sum_value == eps and (eps*eps-eps)*product_value == 0
print("D4: 168 matrices, 24 distinct S4 actions; admissible dual-number counterexample to the product.")

script = Path(__file__)
chapter = script.resolve().parents[3] / "content/papers/l1990-small/03-part.typ"
print(json.dumps({
    "status": "ok",
    "sage_version": sage_version,
    "utc": datetime.now(timezone.utc).isoformat(),
    "script_sha256": sha256(script.read_bytes()).hexdigest(),
    "chapter_sha256": sha256(chapter.read_bytes()).hexdigest(),
    "scope": [
        "Integral F4 root operators and polynomial identities of lemma 4",
        "Counterexamples to printed root images in (10) and (11)",
        "Faithful S4 action of the matrices in (12)",
        "Cramer cofactor sum with all dual-number coordinate constraints",
    ],
    "limitations": "No proof of the automorphism classification theorems",
}, ensure_ascii=False))
