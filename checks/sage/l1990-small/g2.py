"""Exact bounded checks for the additive condition (5), printed page 147.

The field is GF(9), mu is inverse Frobenius, and psi is zero, as allowed
by the explicit observation on page 148. This does not prove theorem 2.
"""
from datetime import datetime, timezone
from hashlib import sha256
from pathlib import Path
from sage.all import GF, matrix, identity_matrix
from sage.env import SAGE_VERSION

K = GF(9, name="a")
mu = lambda x: x**3
psi = lambda x: K(0)

# mu is nonzero, additive, and is inverse Frobenius in this exact field.
for x in K:
    assert mu(x)**3 == x
    for y in K:
        assert mu(x+y) == mu(x)+mu(y)
assert mu(K(1)) == 1

def corrected(x, sigma):
    assert x**3 != x
    return mu(sigma*x**3/(x-x**3))-mu(sigma/(x-x**3))*x

def printed_second(x, sigma):
    assert x**3 != x
    return mu(sigma*x/(x-x**3))-mu(sigma/(x-x**3))*x

allowed = [x for x in K if x**3 != x]
count = 0
for c in allowed:
    for t in allowed:
        for sigma in K:
            assert corrected(c, sigma) == corrected(t, sigma) == psi(sigma)
            count += 1

# Retain the literal asymmetric numerator as an explicitly refuted check.
c = K.gen()
sigma = K(1)
assert c**3 != c
assert corrected(c, sigma) == 0
assert printed_second(c, sigma) != corrected(c, sigma)
assert printed_second(c, sigma) == mu(sigma)
print("GF(9):", count, "corrected triples; printed numerator refuted at",
      "c=t=", c, "sigma=1:", printed_second(c, sigma))

# Carter, Simple groups of Lie type (1972), p. 211:
# c_(2a+b,a+b)=-3. Only the sum 3a+2b is a root of this pair;
# the corresponding rank-two unipotent subgroup is the Heisenberg group.
# In characteristic 2, -3=1, so UT(3) gives its exact relation.
L = GF(4, name="b")
I = identity_matrix(L, 3)
E12 = matrix(L, 3, 3, {(0, 1): 1})
E23 = matrix(L, 3, 3, {(1, 2): 1})
E13 = matrix(L, 3, 3, {(0, 2): 1})
x2 = lambda s: I+s*E12
xab = lambda m: I+m*E23
xhighest = lambda s: I+s*E13
for s in L:
    for m in L:
        g = xab(m)*x2(m)
        assert g.inverse()*x2(s)*g == x2(s)*xhighest(m*s)
t = L.gen()
u = L(1)
m = L(1)
s = u*(t**2+t)
assert s == 1
g = xab(m)*x2(m)
corrected_image = g.inverse()*x2(s)*g
assert corrected_image == x2(s)*xhighest(m*s)
# Literal page-147 LHS has no image exponent and fails in this subgroup.
assert x2(s) != corrected_image
print("GF(4): 16 Heisenberg conjugation checks; omitted phi refuted at s=m=1")

print("Sage", SAGE_VERSION, "UTC", datetime.now(timezone.utc).isoformat())
print("script SHA256", sha256(Path(__file__).read_bytes()).hexdigest())
passage = Path(__file__).resolve().parents[3] / "content/papers/l1990-small/01-part.typ"
print("checked text SHA256", sha256(passage.read_bytes()).hexdigest())
print("ok g2: 324 additive-condition triples and 16 conjugation pairs")
