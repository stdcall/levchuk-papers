"""Exact bounded checks for the seven-dimensional Ree representation.

Passages: sec:l1985-ree-representation, lem:l1985-ree-free-product,
lem:l1985-ree-nonsolvable. This does not verify subgroup classification.
"""
from sage.all import GF, PolynomialRing, matrix, identity_matrix, ZZ
from sage.env import SAGE_VERSION

F = GF(3)
R = PolynomialRing(F, names=("t", "u"))
t, u = R.gens()
I = identity_matrix(R, 7)


def unit(i, j):
    E = matrix(R, 7)
    E[i - 1, j - 1] = 1
    return E


def root(v, linear, quadratic=None):
    return I + v * sum((c * unit(i, j) for c, i, j in linear), matrix(R, 7)) - (
        v ** 2 * unit(*quadratic) if quadratic else matrix(R, 7)
    )


xa = lambda v: root(v, [(1, 6, 7), (2, 4, 5), (-1, 3, 4), (-1, 1, 2)], (3, 5))
xb = lambda v: root(v, [(1, 5, 6), (-1, 2, 3)])
xab = lambda v: root(v, [(1, 1, 3), (-1, 2, 4), (2, 4, 6), (-1, 5, 7)], (2, 6))
x2ab = lambda v: root(v, [(2, 4, 7), (1, 3, 6), (-1, 2, 5), (-1, 1, 4)], (1, 7))
x3ab = lambda v: root(v, [(1, 1, 5), (-1, 3, 7)])
x3a2b = lambda v: root(v, [(1, 2, 7), (-1, 1, 6)])

alpha = matrix(R, [
    [1, -u, -u*t, 0, u**3*t, 0, u**4*t**2],
    [0, 1, -t, -u*t, -u**2*t, u**2*t**2, u**3*t**2],
    [0, 0, 1, -u, -u**2, u**2*t, -u**3*t],
    [0, 0, 0, 1, -u, u*t, 0],
    [0, 0, 0, 0, 1, t, -u*t],
    [0, 0, 0, 0, 0, 1, u],
    [0, 0, 0, 0, 0, 0, 1],
])
beta = matrix(R, [
    [1, 0, u, 0, t, 0, -u*t],
    [0, 1, 0, -u, 0, -u**2, 0],
    [0, 0, 1, 0, 0, 0, -t],
    [0, 0, 0, 1, 0, -u, 0],
    [0, 0, 0, 0, 1, 0, -u],
    [0, 0, 0, 0, 0, 1, 0],
    [0, 0, 0, 0, 0, 0, 1],
])
gamma = matrix(R, [
    [1, 0, 0, -u, 0, -t, -u**2],
    [0, 1, 0, 0, -u, 0, t],
    [0, 0, 1, 0, 0, u, 0],
    [0, 0, 0, 1, 0, 0, -u],
    [0, 0, 0, 0, 1, 0, 0],
    [0, 0, 0, 0, 0, 1, 0],
    [0, 0, 0, 0, 0, 0, 1],
])
assert alpha == xa(u) * xb(t) * xab(u*t) * x2ab(u**2*t)
assert beta == xab(u) * x3ab(t)
assert gamma == x2ab(u) * x3a2b(t)
tau = -matrix(R, 7, lambda i, j: 1 if i+j == 6 else 0)
B = matrix(R, [
    [1, 1, 0, -1, 1, 1, 1],
    [-1, 0, 1, -1, 0, 0, 1],
    [0, -1, 0, 0, 1, 0, 1],
    [1, 0, 0, 0, 0, 1, 1],
    [0, 0, -1, 0, 0, 1, 0],
    [0, -1, 0, 0, -1, 0, 1],
    [-1, 0, 0, -1, 0, -1, 1],
])
assert B**2 == I and B != I
assert B == gamma.apply_map(lambda v: v(1, 1)) * tau * gamma.apply_map(lambda v: v(-1, -1))
# Every product of rank-one generators remains a nonzero scalar multiple
# of E_{i,j} B because all four B_{i,j}, i,j in {1,7}, are nonzero.
for i in (1, 7):
    for j in (1, 7):
        assert B[i-1, j-1] != 0
        assert (unit(i, i)*B)*(unit(j, j)*B) == B[i-1, j-1]*unit(i, j)*B
        assert B[j-1, 6 if i == 1 else 0] != 0

S = PolynomialRing(ZZ, "q")
q = S.gen()
# A2*A3=(q+1)^2-3q=q^2-q+1; A0*A1=(q^2-1)/8.
assert (q-1)*(q+1)*(q*q-q+1) == (q-1)*(q**3+1)
for n in (1, 2, 3):
    qn = ZZ(3)**(2*n+1)
    hall_product = ((qn-1)//2)*((qn+1)//4)*(qn+1-3**(n+1))*(qn+1+3**(n+1))
    assert 8*qn**3*hall_product == qn**3*(qn-1)*(qn**3+1)
    assert 8*3**3*hall_product != qn**3*(qn-1)*(qn**3+1)
print(f"Sage {SAGE_VERSION}: three symbolic root products, B involution/conjugate,")
print("four rank-one transitions, order-factor identity and n=1,2,3 typo checks passed.")
