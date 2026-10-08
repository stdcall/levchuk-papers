"""Exact bounded checks for radical matrix rings and their ideal formulas."""

from itertools import product
from sage.all import GF, Integers, PolynomialRing, QQ, matrix, identity_matrix, vector

checks = 0


def verify(condition):
    global checks
    assert condition
    checks += 1


def unit(ring, n, i, j, coefficient=1):
    result = matrix(ring, n)
    result[i, j] = coefficient
    return result


# The determinant obstruction is visible in actual two-by-two matrices.
ring = Integers(8)
a = ring(2)
upper = unit(ring, 2, 0, 1, a)
lower = unit(ring, 2, 1, 0)
one = identity_matrix(ring, 2)
bracket = upper * lower - lower * upper
verify((one + upper).det() == 1)
verify((one + lower).det() == 1)
verify((one + bracket).det() == 1 - a * a)
verify((one + bracket).det() != 1)
verify(a * a != 0)
verify(all((1 + ring(x)).is_unit() for x in (0, 2, 4, 6)))
# For n=1 the determinant kernel is {0}, contradicting the unqualified claim.
verify([x for x in (0, 2, 4, 6) if 1 + ring(x) == 1] == [0])

# Independently check matrix isolation, used in the projection inclusions.
for n in range(2, 7):
    symbolic = PolynomialRing(QQ, n * n, 'a')
    entries = symbolic.gens()
    generic = matrix(symbolic, n, entries)
    for i in range(n):
        for j in range(n):
            for u in range(n):
                for v in range(n):
                    verify(unit(symbolic, n, i, u) * generic *
                           unit(symbolic, n, v, j) ==
                           unit(symbolic, n, i, j, generic[u, v]))

# Over fields J=0, enumerate every subspace, then test associative ideal and
# commutativity using its actual matrix basis. These are bounded cases only.
for characteristic, n in ((2, 2), (2, 3), (3, 3), (2, 4)):
    field = GF(characteristic)
    positions = [(i, j) for i in range(n) for j in range(i)]
    dimension = len(positions)
    ambient = field ** dimension
    basis = [unit(field, n, i, j) for i, j in positions]

    def as_matrix(vector):
        return sum((vector[k] * basis[k] for k in range(dimension)),
                   matrix(field, n))

    def as_vector(value):
        return ambient([value[i, j] for i, j in positions])

    abelian_ideals = []
    for subspace in (space for d in range(dimension + 1)
                     for space in ambient.subspaces(d)):
        matrices = [as_matrix(vector) for vector in subspace.basis()]
        ideal = all(as_vector(x * y) in subspace and
                    as_vector(y * x) in subspace
                    for x in matrices for y in basis)
        if ideal and all(x * y == y * x for x in matrices for y in matrices):
            abelian_ideals.append(subspace)
    maximal = [space for space in abelian_ideals
               if not any(space.is_subspace(larger) and space != larger
                          for larger in abelian_ideals)]
    verify(len(maximal) == (n - 2) * characteristic + 1)
    for space in maximal:
        verify(all(as_matrix(x) * as_matrix(y) == as_matrix(y) * as_matrix(x)
                   for x in space.basis() for y in space.basis()))

# Exhaust every additive subgroup of R_2(Z/4Z, (2)), not just vector spaces.
moduli = (2, 2, 2, 4)
elements = tuple(product(*(range(modulus) for modulus in moduli)))
zero = (0, 0, 0, 0)


def add(x, y):
    return tuple((a + b) % modulus for a, b, modulus in zip(x, y, moduli))


def cyclic(x):
    values = {zero}
    y = x
    while y != zero:
        values.add(y)
        y = add(y, x)
    return values


subgroups = {frozenset((zero,))}
pending = list(subgroups)
while pending:
    subgroup = pending.pop()
    for element in elements:
        if element not in subgroup:
            generated = frozenset(add(x, y) for x in subgroup for y in cyclic(element))
            if generated not in subgroups:
                subgroups.add(generated)
                pending.append(generated)

ring = Integers(4)


def radical_matrix(x):
    return matrix(ring, [[2 * x[0], 2 * x[1]], [x[3], 2 * x[2]]])


def radical_coordinates(value):
    return (int(value[0, 0]) // 2, int(value[0, 1]) // 2,
            int(value[1, 1]) // 2, int(value[1, 0]))


generators = [radical_matrix(tuple(int(i == j) for i in range(4)))
              for j in range(4)]
abelian_ideals = []
associative_ideals = []
for subgroup in subgroups:
    matrices = [radical_matrix(x) for x in subgroup]
    ideal = all(radical_coordinates(x * y) in subgroup and
                radical_coordinates(y * x) in subgroup
                for x in matrices for y in generators)
    if ideal:
        associative_ideals.append(subgroup)
    if ideal and all(x * y == y * x for x in matrices for y in matrices):
        abelian_ideals.append(subgroup)
maximal = [space for space in abelian_ideals
           if not any(space < larger for larger in abelian_ideals)]
verify(len(maximal) == 1)
verify(maximal[0] == frozenset(x for x in elements if x[3] % 2 == 0))

# Construct the canonical boundary H∩B and its generated ideal for every
# associative ideal in this bounded ring, preserving dependent corner entries.
positions = tuple(product(range(2), repeat=2))


def strictly_before(a, b):
    return a != b and a[0] <= b[0] and b[1] <= a[1]


for ideal in associative_ideals:
    matrices = [radical_matrix(x) for x in ideal]
    projections = {position: {value[position] for value in matrices}
                   for position in positions}
    bottom = projections[(1, 0)]
    candidates = [position for position in positions
                  if projections[position] == bottom]
    primary = [position for position in candidates
               if not any(strictly_before(other, position) for other in candidates)]
    jt = {ring(2) * value for value in bottom}
    secondary_candidates = [position for position in positions
                            if position[0] < min(p[0] for p in primary) and
                            position[1] > max(p[1] for p in primary) and
                            projections[position] == jt]
    secondary = [] if jt == {ring(0)} else [
        position for position in secondary_candidates
        if not any(strictly_before(other, position) for other in secondary_candidates)]
    boundary = {x for x in ideal if all(
        radical_matrix(x)[position] in
        (bottom if position in primary else jt if position in secondary else {ring(0)})
        for position in positions)}
    generated = set(boundary)
    while True:
        enlarged = generated | {add(x, y) for x in generated for y in generated}
        for x in generated:
            value = radical_matrix(x)
            for y in generators:
                enlarged.add(radical_coordinates(value * y))
                enlarged.add(radical_coordinates(y * value))
        if enlarged == generated:
            break
        generated = enlarged
    verify(generated == set(ideal))

# Centralizer formulas in the proof of Theorem 3.1, including the annihilator
# term over a ring with zero divisors. Compare membership in actual matrices.
for i, j in product(range(2), repeat=2):
    rectangle = [unit(ring, 2, u, v, 2)
                 for u in range(i, 2) for v in range(j + 1)]
    for x in elements:
        value = radical_matrix(x)
        actual = all(value * y == y * value for y in rectangle)
        expected = any(all(
            (u >= j + 1 and v <= i - 1) or
            (value[u, v] - (scalar if u == v else 0)) * 2 == 0
            for u, v in product(range(2), repeat=2)) for scalar in (0, 2))
        verify(actual == expected)

for n in range(2, 7):
    positions = [(u, v) for u in range(n) for v in range(u)]
    basis = [unit(QQ, n, u, v) for u, v in positions]
    for i in range(1, n):
        for j in range(i):
            rectangle = [unit(QQ, n, u, v)
                         for u in range(i, n) for v in range(j + 1)]
            equations = matrix(QQ, [
                [(x * y - y * x)[u, v] for x in basis]
                for y in rectangle for u, v in product(range(n), repeat=2)])
            centralizer = equations.right_kernel()
            expected = [k for k, (u, v) in enumerate(positions)
                        if u >= j + 1 and v <= i - 1]
            verify(centralizer.dimension() == len(expected))
            for k in expected:
                basis_vector = vector(QQ, [int(index == k) for index in range(len(basis))])
                verify(basis_vector in centralizer)

print(f'{checks} exact assertions passed; {len(subgroups)} additive subgroups of R_2(Z/4Z,(2)) examined; {len(associative_ideals)} associative ideals checked')
