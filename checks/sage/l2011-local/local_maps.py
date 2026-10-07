"""Exact bounded checks for the 2011 article; general proofs are in the report.

Run with Sage 10.9. No repository paths, output files, randomness, or packages.
The integer matrices construct the structure constants before reduction.
"""
from sage.all import ZZ, GF, Integers, matrix, vector, identity_matrix
from itertools import product, combinations
import json

checks = 0
inventory = {}

def verify(condition, group):
    global checks
    assert condition, group
    checks += 1
    inventory[group] = inventory.get(group, 0) + 1

def classical(kind, n, base=ZZ):
    indices = list(range(1, n + 1)) + ([0] if kind == 'B' else []) + list(range(-1, -n - 1, -1))
    def E(i, j):
        a = matrix(base, len(indices)); a[indices.index(i), indices.index(j)] = 1
        return a
    roots = [(i, j) for i in range(1, n + 1) for j in range(1, i)]
    if kind == 'B':
        roots += [(i, 0) for i in range(1, n + 1)]
    roots += [(i, -j) for i in range(1, n + 1) for j in range(1, i + (kind == 'C'))]
    basis = []
    for i, j in roots:
        if j > 0:
            a = E(i, j) - E(-j, -i)
        elif j == 0:
            a = E(i, 0) + 2 * E(0, -i)
        elif i == -j:
            a = E(i, j)
        else:
            a = E(i, j) + (1 if kind == 'C' else -1) * E(-j, -i)
        basis.append(a)
    def coordinates(a):
        return vector(base, [a[indices.index(i), indices.index(j)] for i, j in roots])
    return roots, basis, coordinates

def bracket(a, b):
    return a * b - b * a

def derivation_space(basis, coordinates, F, associative=False):
    d = len(basis)
    C = {(a, b): coordinates(basis[a] * basis[b] if associative else bracket(basis[a], basis[b]))
         for a in range(d) for b in range(d)}
    rows = []
    for a in range(d):
        for b in range(d):
            for k in range(d):
                row = {}
                def add(i, j, c):
                    v = row.get((i, j), F(0)) + F(c)
                    if v: row[i, j] = v
                    elif (i, j) in row: del row[i, j]
                for j in range(d):
                    add(k, j, C[a, b][j])
                    add(j, a, -C[j, b][k]); add(j, b, -C[a, j][k])
                if row: rows.append(row)
    equations = matrix(F, len(rows), d * d, sparse=True)
    for r, row in enumerate(rows):
        for (i, j), c in row.items(): equations[r, i * d + j] = c
    return [matrix(F, d, d, v) for v in equations.right_kernel().basis()]

def niltriangular(n, base):
    roots = [(i, j) for i in range(1, n) for j in range(i)]
    basis = []
    for i, j in roots:
        a = matrix(base, n); a[i, j] = 1; basis.append(a)
    return roots, basis, lambda a: vector(base, [a[i, j] for i, j in roots])

# Closure and the exact signed general witness formula, over ZZ.
for kind in ['B', 'C', 'D']:
    for n in ([3, 4, 5, 6] if kind != 'D' else [5, 6]):
        roots, basis, coords = classical(kind, n)
        q = roots.index((n, n - 2))
        rho = roots.index((n, -n if kind == 'C' else -n + 1))
        beta = basis[roots.index((n, -n + 2) if kind == 'C' else (n - 1, -n + 2))]
        s = roots.index((n - 1, n - 2) if kind == 'C' else (n, n - 1))
        w = roots.index((n, -n + 1) if kind == 'C' else (n, -n + 2))
        multiplier = 2 if kind == 'C' else -1
        verify(beta * beta == 0, 'integer-witness-square')
        for a, b in product(basis, repeat=2):
            c = bracket(a, b); cc = coords(c)
            reconstructed = sum((x * e for x, e in zip(cc, basis)), matrix(ZZ, a.nrows()))
            verify(c == reconstructed, 'integer-Chevalley-closure')
            verify(cc[s] == 0, 'simple-root-functional-kills-brackets')
        for j, a in enumerate(basis):
            expected = (multiplier * basis[rho] if j == q else matrix(ZZ, a.nrows()))
            if j == s: expected += basis[w]
            verify(bracket(a, beta) == expected, 'signed-classical-witness')
            verify(beta * a * beta == 0, 'no-conjugation-quadratic-term')

# C3 in characteristic two: a full derivation-space countercertificate.
roots, basis, coords = classical('C', 3, GF(2))
q = roots.index((3, 1)); rho = roots.index((3, -3))
for a, b in product(basis, repeat=2):
    verify(coords(bracket(a, b))[rho] == 0, 'C3-char2-derived-obstruction')
u = basis[roots.index((2, 1))]; v = basis[roots.index((3, 2))]
verify(bracket(u, v) == basis[q], 'C3-char2-q-is-bracket')
ds = derivation_space(basis, coords, GF(2))
verify(len(ds) == 22, 'C3-full-derivation-space')
for D in ds: verify(D[rho, q] == 0, 'C3-full-derivation-space')
images = matrix(GF(2), [D.column(q) for D in ds])
target = vector(GF(2), len(basis)); target[rho] = 1
verify(images.rank() == 4, 'C3-counterexample-rank')
verify(matrix(GF(2), list(images.rows()) + [target]).rank() == 5, 'C3-counterexample-rank')

# General sufficient witnesses tested over finite fields and nonreduced rings.
for kind, n, p, power in [('B', 3, 2, 2), ('B', 4, 3, 1), ('C', 3, 3, 2),
                           ('C', 4, 5, 1), ('D', 5, 2, 2), ('D', 6, 3, 1)]:
    R = Integers(p ** power); t = R(p ** (power - 1))
    roots, basis, coords = classical(kind, n, R); d = len(roots)
    q = roots.index((n, n - 2)); rho = roots.index((n, -n if kind == 'C' else -n + 1))
    b = basis[roots.index((n, -n + 2) if kind == 'C' else (n - 1, -n + 2))]
    s = roots.index((n - 1, n - 2) if kind == 'C' else (n, n - 1))
    m = R(2 if kind == 'C' else -1); scalar = t * m.inverse_of_unit()
    I = identity_matrix(R, b.nrows())
    for size in range(3):
        for support in combinations(range(d), size):
            for values in product(sorted(set([R(1), t, R(2)])), repeat=size):
                a = vector(R, d)
                for j, value in zip(support, values): a[j] = value
                alpha = sum((x * e for x, e in zip(a, basis)), matrix(R, b.nrows()))
                target = t * a[q] * basis[rho]
                if t * a[s] == 0:
                    verify(scalar * bracket(alpha, b) == target, 'classical-local-derivation-witness')
                    verify((I - scalar * b) * alpha * (I + scalar * b) == alpha + target,
                           'classical-local-automorphism-witness')
                else:
                    k = a[s].inverse_of_unit(); c = t * k * a[q]
                    verify(c * a[s] * basis[rho] == target, 'classical-central-witness')

# Associative NT(3/4) socle scaling: exhaustive all input matrices.
for n, p, power in [(3, 2, 1), (3, 2, 2), (3, 2, 3), (3, 3, 1), (3, 3, 2),
                    (4, 2, 2), (4, 3, 1)]:
    R = Integers(p ** power); c = R(p ** (power - 1)); one_plus = 1 + c
    roots, basis, coords = niltriangular(n, R)
    I = identity_matrix(R, n)
    for values in product(R, repeat=len(roots)):
        alpha = sum((x * e for x, e in zip(values, basis)), matrix(R, n))
        target = matrix(R, n); target[n - 1, 0] = c * alpha[n - 1, 0]
        adjacent = [alpha[i + 1, i] for i in range(n - 1)]
        if all(c * x == 0 for x in adjacent):
            diagonal = [c, R(0), R(0)] if n == 3 else [R(0), -c, R(0), -c]
            D = matrix.diagonal(R, diagonal)
            verify(bracket(alpha, D) == target, 'socle-scaling-diagonal-derivation')
            if one_plus.is_unit():
                diagonal = [one_plus, R(1), R(1)] if n == 3 else [R(1), one_plus.inverse_of_unit(), R(1), one_plus.inverse_of_unit()]
                U = matrix.diagonal(R, diagonal)
                verify(U.inverse() * alpha * U == alpha + target, 'socle-scaling-diagonal-automorphism')
        else:
            i = next(i for i, x in enumerate(adjacent) if c * x != 0)
            coefficient = c * adjacent[i].inverse_of_unit() * alpha[n - 1, 0]
            verify(coefficient * adjacent[i] == target[n - 1, 0], 'socle-scaling-central-witness')

# Both noncentral coefficient maps in NT4: exhaustive inputs over Z/4.
R = Integers(4); t = R(2); n = 4
roots, basis, coords = niltriangular(n, R); I = identity_matrix(R, n)
for values in product(R, repeat=len(roots)):
    alpha = sum((x * e for x, e in zip(values, basis)), matrix(R, n))
    for q, beta in [((2, 0), -t * basis[roots.index((3, 2))]),
                    ((3, 1), t * basis[roots.index((1, 0))])]:
        target = matrix(R, n); target[3, 0] = t * alpha[q]
        if t * alpha[2, 1] == 0:
            verify(bracket(alpha, beta) == target, 'NT4-inner-local-derivation')
            verify((I - beta) * alpha * (I + beta) == alpha + target, 'NT4-inner-local-automorphism')
        else:
            coefficient = t * alpha[2, 1].inverse_of_unit() * alpha[q]
            verify(coefficient * alpha[2, 1] == target[3, 0], 'NT4-central-local-witness')

# The adjacent-coordinate map is not an ordinary diagonal derivation.
roots, basis, coords = niltriangular(3, ZZ)
e21, e31, e32 = basis
def delta21(a):
    b = matrix(ZZ, 3); b[1, 0] = a[1, 0]; return b
verify(delta21(e32 * e21) != delta21(e32) * e21 + e32 * delta21(e21), 'adjacent-delta-original-error')

# Lie-derivation necessity, including characteristic two, full spaces.
for n in [5, 6]:
    roots, basis, coords = niltriangular(n, GF(2)); ds = derivation_space(basis, coords, GF(2))
    for k, m in roots:
        if not (1 < k - m < n - 1) or (k, m) in [(2, 0), (n - 1, n - 3)]: continue
        alpha = basis[roots.index((k, m))]
        if m == 0: alpha += basis[roots.index((k, 1))]
        if k == n - 1: alpha += basis[roots.index((n - 2, m))]
        target = vector(GF(2), len(roots)); target[roots.index((n - 1, 0))] = 1
        images = matrix(GF(2), [D * coords(alpha) for D in ds])
        verify(target not in images.row_space(), 'full-Lie-derivation-necessity')

print(json.dumps({'status': 'pass', 'checks': checks, 'inventory': inventory,
                  'scope': 'exact bounded inputs and integer structural identities; general proofs are separate',
                  'C3_char2': {'derivation_dimension': 22, 'image_rank': 4, 'augmented_rank': 5}}, sort_keys=True))
