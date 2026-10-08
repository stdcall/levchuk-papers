"""Exact coefficient-sign certificate for an almost-annihilator automorphism.

The concrete ring is R_3(Z/16,2(Z/16)). Conjugation by 1+E31 supplies
lambda(y)=y, mu(y)=-y and sigma(y)=-y. This finite certificate verifies
the two positive signs in condition (4), not a general classification.
"""
from sage.all import Zmod, matrix, identity_matrix


def check():
    ring = Zmod(16)
    nilpotent = matrix(ring, 3, 3, {(2, 0): 1})
    unit = identity_matrix(ring, 3)
    assert nilpotent * nilpotent == 0
    assert (unit - nilpotent) * (unit + nilpotent) == unit
    y = z = ring(2)
    original = matrix(ring, 3, 3, {(0, 2): y})
    image = (unit - nilpotent) * original * (unit + nilpotent)
    assert image == matrix(ring, 3, 3, {
        (0, 2): y, (0, 0): y, (2, 2): -y, (2, 0): -y,
    })
    assert image * image == 0
    assert y * (-z) + y * z == 0
    assert (-y) * z + (-y) * (-z) == 0
    assert y * (-z) - y * z == 8
    assert (-y) * z - (-y) * (-z) == 8
    print("PASS: R3(Z16,2Z16) almost-annihilator coefficient signs")


if __name__ == "__main__":
    check()
