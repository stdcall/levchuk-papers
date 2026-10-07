"""Exact checks of rank-two matrix identities and the F4 root diagram.

These checks do not establish any automorphism classification theorem.
"""
from itertools import product
from datetime import datetime, timezone
from hashlib import sha256
from pathlib import Path
from sage.all import QQ, GF, PolynomialRing, matrix, vector, identity_matrix
from sage.env import SAGE_VERSION

checks = 0


def checked(condition):
    global checks
    assert condition
    checks += 1


# In U(G2)/U3 in characteristic 3, the alpha, beta, alpha+beta
# coordinates form this Heisenberg multiplication. The coordinate of
# the product of the t and z images uses both lambda_1 coordinates;
# the unrelated lambda_2 coordinate in the printed first equality
# on page 148 cannot occur.
R = PolynomialRing(GF(3), names="t0,tp,t1,z0,zp,z1,z2")
t0,tp,t1,z0,zp,z1,z2 = R.gens()


def quotient_image(x,y,z):
    return matrix(R, [[1,0,0],[x,1,0],[z,y,1]])


quotient_product = quotient_image(t0,tp,t1)*quotient_image(z0,zp,z1)
checked(quotient_product[2,0] == t1+z1+z0*tp)
checked(quotient_product[2,0] != t1+z2+z0*tp)  # Printed lambda_2.
checked(quotient_product[1,0] == t0+z0)
checked(quotient_product[2,1] == tp+zp)
print("G2/U3: lambda_1 product coordinate checked over GF(3) polynomials")


def code(v):
    return "".join(str(int(x)) for x in v)


# Bourbaki simple roots; coefficients of the highest root are (2342).
e = [vector(QQ, [int(i == j) for i in range(4)]) for j in range(4)]
simple = [e[1] - e[2], e[2] - e[3], e[3], (e[0]-e[1]-e[2]-e[3])/2]
basis = matrix(QQ, simple).transpose()
roots = {tuple(s * v) for v in e for s in [-1, 1]}
roots |= {tuple(s*e[i]+t*e[j]) for i in range(4) for j in range(i+1,4)
          for s,t in product([-1,1], repeat=2)}
roots |= {tuple(vector(QQ, signs)/2) for signs in product([-1,1], repeat=4)}
checked(len(roots) == 48)
positive = {tuple(basis.solve_right(vector(QQ, r))) for r in roots
            if all(x >= 0 for x in basis.solve_right(vector(QQ, r)))}
checked(len(positive) == 24)
printed_nodes = set("1000 0100 0010 0001 1100 0110 0011 1110 0120 0111 "
                    "1120 1111 0121 1220 1121 0122 1221 1122 1231 1222 "
                    "1232 1242 1342 2342".split())
checked({code(r) for r in positive} == printed_nodes)
unit = [tuple(int(i == j) for i in range(4)) for j in range(4)]
covers = {(code(r), code(tuple(r[i]+u[i] for i in range(4))))
          for r in positive for u in unit
          if tuple(r[i]+u[i] for i in range(4)) in positive}
printed_edges = set(tuple(s.split("-")) for s in (
    "1000-1100 0100-1100 0100-0110 0010-0110 0010-0011 0001-0011 "
    "1100-1110 0110-1110 0110-0111 0011-0111 "
    "1110-1120 1110-1111 0120-1120 0120-0121 0111-1111 0111-0121 "
    "1120-1220 1120-1121 1111-1121 0121-1121 0121-0122 "
    "1220-1221 1121-1221 1121-1122 0122-1122 "
    "1221-1231 1221-1222 1122-1222 1231-1232 1222-1232 "
    "1232-1242 1242-1342 1342-2342"
).split())
checked(printed_edges <= covers)
missing = covers - printed_edges
checked(missing == {("0110", "0120")})
# The publication does not claim to draw all root-poset covers. Its
# omitted 0110 -> 0120 cover is retained as a graphic choice, not errata.
print("F4: 24 positive roots; covers", len(covers), "missing printed edges", sorted(missing))

# Realize B4 and C4 in the same Euclidean F4 space. The C4 coordinate
# vectors have squared norm 1/2, fixing the relative scale of the systems.
eb = [e[3], e[2], e[1], e[0]]
ec = [(e[2]-e[3])/2, (e[2]+e[3])/2, (e[0]-e[1])/2, (e[0]+e[1])/2]


def root_from_coordinates(b, i, j):
    return b[i-1] if j == 0 else b[i-1] - (1 if j > 0 else -1)*b[abs(j)-1]


def q(i,j):
    return tuple(root_from_coordinates(eb,i,j))


def p(i,j):
    return tuple(root_from_coordinates(ec,i,j))


aliases = {
    "1000": [q(3,2)], "0100": [q(2,1),p(1,-1)],
    "0010": [q(1,0),p(2,1)], "0001": [p(3,2)],
    "1100": [q(3,1)], "0110": [q(2,0),p(2,-1)],
    "0011": [p(3,1)], "1110": [p(4,3),q(3,0)],
    "0120": [q(2,-1),p(2,-2)], "0111": [p(3,-1)],
    "1120": [q(3,-1)], "1111": [p(4,2)],
    "0121": [p(3,-2)], "1220": [q(3,-2)],
    "1121": [p(4,1)], "0122": [p(3,-3),q(4,3)],
    "1221": [p(4,-1)], "1122": [q(4,2)],
    "1231": [p(4,-2)], "1222": [q(4,1)],
    "1232": [p(4,-3),q(4,0)], "1242": [q(4,-1)],
    "1342": [q(4,-2)], "2342": [q(4,-3),p(4,-4)],
}
checked(set(aliases) == printed_nodes)
alias_checks = 0
for coefficients, names in aliases.items():
    expected = tuple(basis*vector(QQ, [int(c) for c in coefficients]))
    for name in names:
        checked(name == expected)
        alias_checks += 1
print("F4:", alias_checks, "root labels checked from their defining coordinates")


B = {q(i,j) for i in range(1,5) for j in range(-i+1,i)}
C = {p(i,j) for i in range(1,5) for j in range(-i,i) if j != 0}
checked(len(B) == len(C) == 16)
checked(len(B & C) == 8)
checked(B | C == {tuple(basis*vector(QQ,r)) for r in positive})
checked(B & C == {q(i,0) for i in range(1,5)} | {p(i,-i) for i in range(1,5)})
subsystems = []
for s in [-1,1]:
    subsystems += [
        {p(3,-s),q(3,2*s),p(4,2*s),q(4,s)},
        {p(3,2*s),q(3,-s),p(4,s),q(4,2*s)},
        {p(3,s),q(3,s),p(4,2*s),q(4,2*s)},
        {p(3,2*s),q(3,-2*s),p(4,-s),q(4,s)},
    ]
for S in subsystems:
    checked(len(S) == 4 and S <= B | C)
    full = S | {tuple(-vector(QQ,r)) for r in S}
    checked(len(full) == 8)
    for r,t in product(full,repeat=2):
        a,b = vector(QQ,r),vector(QQ,t)
        reflection = tuple(b-2*(a*b)/(a*a)*a)
        checked(reflection in full)
triples = 0
for r,s in product(B | C, repeat=2):
    t = tuple(vector(QQ,r)+vector(QQ,s))
    if t not in B | C:
        continue
    triple = {r,s,t}
    if triple <= B or triple <= C:
        continue
    checked(any(triple <= S for S in subsystems))
    triples += 1
print("F4: B4/C4 union, intersection, eight B2 subsystems and", triples, "mixed triples checked")

# The matrices are exactly those given for U(2 A3) on printed page 149.
K = GF(9, name="a")
I = identity_matrix(K, 4)


def E(i,j):
    z = matrix(K,4,4)
    z[i-1,j-1] = 1
    return z


def xa(t):
    return I + t*E(2,1) - t**3*E(4,3)


def xb(u):
    checked(u**3 == u)
    return I + u*E(3,2)


def xab(t):
    return I + t*E(3,1) + t**3*E(4,2)


def x2(u):
    checked(u**3 == u)
    return I + u*E(4,1)


# This diagonal conjugation preserves every displayed root subgroup.
D = matrix.diagonal(K, [1,1,2,2])


def phi(M):
    return D*M*D.inverse()


for t in K:
    checked(phi(xa(t)) == xa(t))
    checked(phi(xab(t)) == xab(2*t))
for u in K:
    if u**3 == u:
        checked(phi(xb(u)) == xb(2*u))
        checked(phi(x2(u)) == x2(2*u))
# Printed left sides lack phi: the chosen diagonal image refutes both.
checked(xb(K(1)) != xb(K(2)))
checked(x2(K(1)) != x2(K(2)))
checked(phi(xb(K(1))) == xb(K(2)))
checked(phi(x2(K(1))) == x2(K(2)))
print("U(2 A3): two omitted image exponents refuted and corrected over GF(9)")

# Equation (8), with lambda=id, mu=psi=2 and mu_1=mu_0=0.
# Its central correction vanishes. The printed extra phi on the right
# is refuted at u=t=1; removing that exponent gives the exact image.
checked(phi(xab(K(1))) != phi(xab(K(2))))
equation8_cases = 0
for u in K:
    if u**3 != u:
        continue
    for t in K:
        central = 2*u*t*t**3 - 2*u*t*t**3
        checked(central == 0)
        checked(phi(xab(u*t)) == xab(2*u*t)*x2(central))
        equation8_cases += 1
print("U(2 A3): equation (8) corrected image checked in", equation8_cases,
      "cases; printed right image refuted")

# A second example satisfies the proof's normalization 1^lambda=1^mu=1.
# Frobenius has lambda(t)=t^3, mu=psi=id on GF(3), all other maps zero.
def frobenius(M):
    return M.apply_map(lambda z: z**3)


checked(frobenius(xab(K.gen())) != frobenius(xab(K.gen()**3)))
normalized_cases = 0
for u in K:
    if u**3 != u:
        continue
    for t in K:
        central = u*t**3*t**9 - u*t*t**3
        checked(central == 0)
        checked(frobenius(xab(u*t)) == xab(u*t**3)*x2(central))
        normalized_cases += 1
print("U(2 A3): normalized Frobenius equation (8) checked in",
      normalized_cases, "cases; printed right image refuted")

print("Sage", SAGE_VERSION, "UTC", datetime.now(timezone.utc).isoformat())
print("script SHA256", sha256(Path(__file__).read_bytes()).hexdigest())
passage = Path(__file__).resolve().parents[3] / "content/papers/l1990-small/02-part.typ"
print("checked text SHA256", sha256(passage.read_bytes()).hexdigest())
print(f"ok rank-two-f4: {checks} checks")
