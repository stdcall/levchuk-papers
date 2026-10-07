"""Products and squares differ in the ring F2[e]/(e^2).

The paragraph in the proof of the normal/Lie correspondence uses
K=K^2 to write every coefficient as a sum of x_t*y_t. Squares alone
do not express that hypothesis, even in a commutative ring with 1.
"""
from sage.all import GF, PolynomialRing

polynomials = PolynomialRing(GF(2), 'x')
x = polynomials.gen()
ring = polynomials.quotient(x*x, 'e')
e = ring.gen()
elements = tuple(ring)
assert len(elements) == 4
assert e != 0 and e*e == 0
assert all(ring(1)*a == a for a in elements)
squares = {a*a for a in elements}
assert squares == {ring(0), ring(1)}
assert all(a+b in squares for a in squares for b in squares)
assert e not in squares
products = {a*b for a in elements for b in elements}
assert products == set(elements)
print('Products span the whole four-element ring; squares span {0,1}.')
