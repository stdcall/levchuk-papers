"""F4 diagrams: exact finite root and cover semantics over ZZ.

The 1990 printed figure selects 33 covers; the completed rendering and
the 2012 figure have all 34. Dashes do not encode Chevalley magnitudes.
No central-series or automorphism classification is claimed here.
"""
from itertools import combinations, product
from pathlib import Path
import re

from sage.all import LieAlgebra, QQ, RootSystem, ZZ, vector

checks = 0


def check(statement):
    global checks
    assert statement
    checks += 1


project = Path(__file__).resolve().parents[3]
table_path = project / 'content/papers/l1990-small/diagrams/b-f4-roots.typ'
source = table_path.read_text()
table = re.search(r'#let positive-roots\s*=\s*\((.*?)\n\)', source, re.S)
check(table is not None)
rows = re.findall(r'\(\((\d),\s*(\d),\s*(\d),\s*(\d)\),\s*\$(.*?)\$\)',
                  table.group(1))
coefficients = [tuple(map(int, row[:4])) for row in rows]
check(len(coefficients) == len(set(coefficients)) == 24)

# Independently generate twice the standard Euclidean F4 root vectors.
standard = set()
for i in range(4):
    for sign in (-1, 1):
        standard.add(tuple(2*sign if k == i else 0 for k in range(4)))
for i, j in combinations(range(4), 2):
    for s, t in product((-1, 1), repeat=2):
        standard.add(tuple(2*s if k == i else 2*t if k == j else 0
                           for k in range(4)))
standard.update(product((-1, 1), repeat=4))
check(len(standard) == 48)
simple_vectors = ((0, 2, -2, 0), (0, 0, 2, -2),
                  (0, 0, 0, 2), (1, -1, -1, -1))


def transform(c):
    return tuple(sum(c[i]*simple_vectors[i][j] for i in range(4))
                 for j in range(4))


images = {transform(c) for c in coefficients}
negative = {tuple(-x for x in v) for v in images}
check(len(images) == 24)
check(images.isdisjoint(negative))
check(images | negative == standard)
root_lattice = RootSystem(['F', 4]).root_lattice()
positive = set(root_lattice.positive_roots())
all_roots = set(root_lattice.roots())
literal = {tuple(r[i] for i in range(1, 5)) for r in positive}
check(set(coefficients) == literal)
check({transform(tuple(r[i] for i in range(1, 5))) for r in all_roots}
      == standard)

# Check every actual p/q alias in the shared table, in its own coordinate basis.
epsilon = [None, vector(QQ, [0, QQ(1)/2, 0, 0]),
           vector(QQ, [0, QQ(1)/2, 1, 0]),
           vector(QQ, [0, QQ(1)/2, 1, 1]),
           vector(QQ, [1, QQ(3)/2, 2, 1])]
eta = [None, vector(QQ, [0, 0, 1, 0]), vector(QQ, [0, 1, 1, 0]),
       vector(QQ, [1, 1, 1, 0]), vector(QQ, [1, 2, 3, 2])]
for row, target in zip(rows, coefficients):
    for alias in row[4].split(' = '):
        match = re.fullmatch(r'([pq])_(?:\((\d),(-?\d)\)|(\d)(\d))', alias)
        check(match is not None)
        i, j = int(match[2] or match[4]), int(match[3] or match[5])
        basis = epsilon if match[1] == 'p' else eta
        v = basis[i] if j == 0 else basis[i]-basis[j] if j > 0 \
            else basis[i]+basis[-j]
        check(tuple(v) == target)

# The renderer's predicate is precisely nonnegative unit coefficient difference.
predicate = re.search(r'#let covers\(a, b\) = \{(.*?)\n\}', source, re.S)
check(predicate is not None)
normalized = re.sub(r'\s+', '', predicate.group(1))
check(normalized == 'letd=b.zip(a).map(p=>p.at(0)-p.at(1))'
                   'd.all(v=>v>=0)andd.sum()==1')
renderer = source.split('#let root-canvas', 1)[1]
compact_renderer = re.sub(r'\s+', '', renderer)
check('if(covers(a.at(0),b.at(0))){line(' in compact_renderer)
check('stroke:ifa.at(0)==(0,1,2,0)ora.at(0)==(0,1,1,0)'
      'andb.at(0)==(0,1,2,0)' in compact_renderer)
english = (project / 'content/papers/l2012-extremal-en/diagrams/f4-roots.typ').read_text()
check('#let f4-roots() = root-canvas()' in english)
check('../../l1990-small/diagrams/b-f4-roots.typ' in english)
units = {tuple(int(i == j) for i in range(4)) for j in range(4)}
drawn = {(a, b) for a in coefficients for b in coefficients
         if all(y >= x for x, y in zip(a, b))
         and sum(y-x for x, y in zip(a, b)) == 1}
independent = {(a, b) for a in literal for b in literal
               if tuple(y-x for x, y in zip(a, b)) in units}
check(drawn == independent)
check(len(drawn) == 34)


def strictly_below(a, b):
    return a != b and all(x <= y for x, y in zip(a, b))


hasse = {(a, b) for a in literal for b in literal
         if strictly_below(a, b)
         and not any(strictly_below(a, c) and strictly_below(c, b)
                     for c in literal)}
check(hasse == independent)
check(len(hasse) == 34)
omitted = ((0, 1, 1, 0), (0, 1, 2, 0))
historical = drawn - {omitted}
check(omitted in drawn)
check(len(historical) == 33)
check(drawn - historical == {omitted})

lie = LieAlgebra(ZZ, cartan_type=['F', 4])
chevalley = lie.basis()
simple = root_lattice.simple_roots()
magnitudes = {}
for alpha in positive:
    a = tuple(alpha[i] for i in range(1, 5))
    for i in range(1, 5):
        beta = alpha + simple[i]
        if beta not in positive:
            continue
        b = tuple(beta[j] for j in range(1, 5))
        p = 0
        while alpha - (p+1)*simple[i] in all_roots:
            p += 1
        bracket = chevalley[simple[i]].bracket(chevalley[alpha])
        terms = bracket.monomial_coefficients()
        check(set(terms) == {beta})
        check(abs(terms[beta]) == p+1)
        check((a, b) in drawn)
        magnitudes[a, b] = abs(terms[beta])
check(set(magnitudes) == drawn)
double_edges = {edge for edge, magnitude in magnitudes.items() if magnitude == 2}
check(len(double_edges) == 6)
check(all(magnitude in (1, 2) for magnitude in magnitudes.values()))
dashes = {omitted, ((0, 1, 2, 0), (1, 1, 2, 0)),
          ((0, 1, 2, 0), (0, 1, 2, 1))}
check([magnitudes[edge] for edge in sorted(dashes)] == [2, 1, 1])
check(len(double_edges - dashes) == 5)
check(magnitudes[omitted] == 2)
print(f'ok l1990-small F4 cover semantics: {checks} exact checks; '
      '48 roots, 24 positive, 34 covers, historical selection 33; '
      '6 magnitude-two brackets; dashes have magnitudes 2,1,1')
