"""Exact root combinatorics for §2 (lemmas 2–3, corollaries 3.1–3.2).

Rank-two support tests use necessary root-string commutator implications
C_(n,1) A_r^n A_s <= A_(nr+s). Thus they enumerate a superset of possible
group carpets; no finite-field sampling or carpet classification is used.
Classical ranks 2..8 and all exceptional types are checked explicitly;
these computations do not constitute a proof for unbounded rank.
"""
from sage.all import RootSystem, QQ, matrix, vector
from sage.env import SAGE_VERSION
from datetime import datetime, timezone
from hashlib import sha256
from pathlib import Path
from math import factorial
import json

checks = 0
counts = {}
representations = {}


def check(value):
    global checks
    assert value
    checks += 1


def scalar(r, s):
    return r.to_ambient().scalar(s.to_ambient())


def reflection(r, s):
    return s - int(2 * scalar(r, s) / scalar(r, r)) * r


def rank_two(name):
    Q = RootSystem(name).root_lattice()
    roots = list(Q.roots())
    rootset = set(roots)
    positive = {r for r in roots if all(r[i] >= 0 for i in Q.index_set())}
    reached = {roots[0]}
    while True:
        expanded = reached | {t for t in roots if any(t-r in rootset for r in reached)}
        if expanded == reached:
            break
        reached = expanded
    check(reached == rootset)
    rho = max(scalar(r, r) / scalar(s, s) for r in roots for s in roots)
    chambers = {frozenset(positive)}
    todo = list(chambers)
    while todo:
        C = todo.pop()
        for i in Q.index_set():
            D = frozenset(r.simple_reflection(i) for r in C)
            if D not in chambers:
                chambers.add(D)
                todo.append(D)
    check(len(chambers) == {"A2": 6, "B2": 8, "G2": 12}[str(name[0])+str(name[1])])
    implications = []
    for r in roots:
        for s in roots:
            if r + s in rootset:
                p = 0
                while s - (p + 1) * r in rootset:
                    p += 1
                implications.append((r, s, r + s, p + 1))
                # Coefficient of u^n*v: iterated root-string brackets / n!.
                # These coefficients are independent of the order chosen
                # for higher factors, since their v-degree is one.
                product = 1
                n = 1
                while s+n*r in rootset:
                    previous = s+(n-1)*r
                    p = 0
                    while previous-(p+1)*r in rootset:
                        p += 1
                    product *= p+1
                    coefficient = QQ(product)/factorial(n)
                    check(coefficient.denominator() == 1)
                    check(coefficient in (1,2,3))
                    implications.append((r,s,s+n*r,int(coefficient)))
                    n += 1
    for char in (0, 2, 3, 5):
        supports = 0
        for mask in range(1 << len(roots)):
            S = {r for i, r in enumerate(roots) if mask & (1 << i)}
            if any(r in S and s in S and t not in S and
                   (char == 0 or n % char != 0) for r, s, t, n in implications):
                continue
            supports += 1
            sigma = {r for r in S if -r in S}
            sigma_plus = {r for r in S if -r not in S}
            check(any(sigma_plus <= C for C in chambers))
            for r in sigma:
                for s in sigma:
                    assert reflection(r, s) in sigma, (name, char, S, r, s)
                    check(True)
                    if r+s in rootset and r+s not in sigma:
                        check(char == rho and scalar(r, r) == scalar(s, s)
                              and scalar(r, r) < scalar(r+s, r+s))
        counts[f"{name}:supports:char{char}"] = supports
    # The printed r != s is false for r=-s. The corrected r != +/-s
    # and the weaker sufficient positive-r version are both checked.
    def coord(r):
        return vector(QQ, [r[i] for i in Q.index_set()])
    def basis(q, s):
        M = matrix(QQ, [coord(q), coord(s)]).transpose()
        if M.det() == 0:
            return False
        cs = [M.solve_right(coord(r)) for r in roots]
        return all(all(z in QQ and z.denominator() == 1 for z in c) and
                   (all(z >= 0 for z in c) or all(z <= 0 for z in c)) for c in cs)
    for length in {scalar(r, r) for r in roots}:
        s = max((r for r in positive if scalar(r,r) == length),
                key=lambda r: sum(coord(r)))
        record = {}
        check(not any(matrix(QQ,[coord(q),coord(s)]).transpose()
                      .solve_right(coord(-s))[0] > 0
                      for q in rootset-positive if basis(q,s)))
        for r in roots:
            if r in (s,-s):
                continue
            witnesses = []
            for q in rootset-positive:
                M = matrix(QQ, [coord(q), coord(s)]).transpose()
                if basis(q,s):
                    c = M.solve_right(coord(r))
                    if all(z.denominator() == 1 for z in c) and c[0] > 0 and c[1] >= 0:
                        witnesses.append((q,tuple(c)))
            check(bool(witnesses))
            if r in positive:
                check(bool(witnesses))
            record[str(r)] = [str(witnesses[0][0]),list(map(int,witnesses[0][1]))]
        representations[f"{name}:s={s}"] = record
    # Products in the displayed A2/B2/G2 ring chains have these root sums.
    a, b = Q.simple_roots()[1], Q.simple_roots()[2]
    chain = [(a+b, -b, a), (a+b, -a, b)]
    if rho >= 2:
        # Sage B2 numbers its long simple root first, unlike the article.
        if scalar(a,a) > scalar(b,b):
            a,b = b,a
        chain += [(a+b,a,2*a+b), (2*a+b,-a,a+b)]
    if rho == 3:
        chain += [(2*a+b,-a,a+b), (a+b,2*a+b,3*a+2*b),
                  (3*a+2*b,-a-b,2*a+b)]
    for r,s,t in chain:
        check(r in rootset and s in rootset and t in rootset and r+s == t)


def general_roots(name):
    Q = RootSystem(name).root_lattice()
    roots = list(Q.roots())
    rootset = set(roots)
    positive = {r for r in roots if all(r[i] >= 0 for i in Q.index_set())}
    for length in {scalar(r,r) for r in roots}:
        s = max((r for r in positive if scalar(r,r) == length),
                key=lambda r: sum(r[i] for i in Q.index_set()))
        ones = (rootset-positive) | {s}
        while True:
            expanded = ones | {r+t for r in ones for t in ones if r+t in rootset}
            if expanded == ones:
                break
            ones = expanded
        check(ones == rootset)
    # An irreducible root system of rank>1 has a nonorthogonal independent
    # partner for each root. Its full planar intersection is closed under
    # reflection and addition, and is an irreducible rank-two subsystem.
    for r in roots:
        partners = [s for s in roots if s != r and s != -r and scalar(r,s) != 0]
        check(bool(partners))
        s = partners[0]
        def c(t):
            return [t[i] for i in Q.index_set()]
        plane = {t for t in roots if matrix(QQ, [c(r),c(s),c(t)]).rank() == 2}
        check(len(plane) in (6,8,12))
        for t in plane:
            check(reflection(r,t) in plane)
        for t in plane:
            for u in plane:
                if t+u in rootset:
                    check(t+u in plane)
    counts[str(name)] = len(roots)


def all_planar_types(name):
    """All root pairs, not just a selected partner of each root.

    Classical coordinate reduction: roots of A are e_i-e_j, those of
    B/C/D have at most two nonzero coordinates. A pair has support at
    most four, and its plane cannot acquire another coordinate. Thus
    A3 and B4/C4/D4 exhaust pair geometries of unbounded classical rank.
    Exceptional root systems are enumerated completely here.
    """
    roots = list(RootSystem(name).root_lattice().roots())
    N = len(roots)
    gram = [[int(2*scalar(r,s)) for s in roots] for r in roots]
    check(all(gram[i][j] == 2*scalar(roots[i],roots[j])
              for i in range(N) for j in range(N)))
    planes = set()
    for i in range(N):
        for j in range(i+1,N):
            rr,ss,rs = gram[i][i],gram[j][j],gram[i][j]
            det = rr*ss-rs*rs
            if det == 0:
                continue
            plane = frozenset(k for k in range(N) if
                gram[k][k]*det == ss*gram[i][k]**2
                -2*rs*gram[i][k]*gram[j][k]+rr*gram[j][k]**2)
            planes.add(plane)
    for plane in planes:
        check(len(plane) in (4,6,8,12))
        lengths = {gram[i][i] for i in plane}
        ratio = QQ(max(lengths))/min(lengths)
        check((len(plane),ratio) in ((4,1),(4,2),(4,3),(6,1),(8,2),(12,3)))
        S = {roots[i] for i in plane}
        for r in S:
            for s in S:
                check(reflection(r,s) in S)
                if r+s in roots:
                    check(r+s in S)
    counts[f"{name}:all-root-pair-planes"] = len(planes)


for typ in (["A",2],["B",2],["G",2]):
    rank_two(typ)
for family in "ABCD":
    for rank in range(2 if family != "D" else 4, 9):
        general_roots([family,rank])
for typ in (["E",6],["E",7],["E",8],["F",4],["G",2]):
    general_roots(typ)
for typ in (["A",3],["B",4],["C",4],["D",4],
            ["E",6],["E",7],["E",8],["F",4],["G",2]):
    all_planar_types(typ)
print(json.dumps({"sage": SAGE_VERSION, "utc": datetime.now(timezone.utc).isoformat(),
                  "sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
                  "cases": counts, "representations": representations,
                  "checks": checks}, sort_keys=True))
print(f"ok l1983-root-carpets: {checks} checks")
