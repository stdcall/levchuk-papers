"""Exact checks for Egorychev--Levchuk (1996), Lemmas 1, 5--7.

Root-poset enumeration is independent of the lattice-path formulas.
It checks untwisted ordinary root-poset ideals, not the classification
of characteristic subgroups or the exceptional characteristic-two case.
All binomial expected values are the formulas on printed pp.50--51,
57,59,62. Finite ranges are explicit below; none proves all ranks.
"""
from functools import lru_cache
from sage.all import RootSystem, QQ, GF, PolynomialRing, matrix, identity_matrix, binomial

checks = 0


def check(a, b):
    global checks
    assert a == b, (a, b)
    checks += 1


def antichains(kind, n):
    roots = RootSystem([kind, n]).root_lattice().positive_roots()
    vectors = [tuple(r.to_vector()) for r in roots]
    conflicts = []
    for a in vectors:
        mask = 0
        for j, b in enumerate(vectors):
            if all(x <= y for x, y in zip(a, b)) or all(
                y <= x for x, y in zip(a, b)):
                mask |= 1 << j
        conflicts.append(mask)

    @lru_cache(None)
    def count(mask):
        if not mask:
            return 1
        bit = mask & -mask
        i = bit.bit_length() - 1
        return count(mask ^ bit) + count(mask & ~conflicts[i])

    return count((1 << len(vectors)) - 1)


for n in range(2, 8):
    check(antichains('A', n-1), binomial(2*n, n-1)/n)
    for kind in ('B', 'C'):
        check(antichains(kind, n), binomial(2*n, n))
    if n >= 4:
        check(antichains('D', n), binomial(2*n-1, n)+binomial(2*n-2, n))


def paths(x, y, strict):
    counts = {0: 1}
    for step in range(1, x+1):
        nxt = {}
        for height, value in counts.items():
            for new in (height-1, height+1):
                if new >= (1 if strict else 0):
                    nxt[new] = nxt.get(new, 0) + value
        counts = nxt
    return counts.get(y, 0)


for x in range(1, 25):
    for y in range(x+1):
        if (x+y) % 2 == 0:
            check(paths(x,y,True), QQ(y)/x*binomial(x,(x+y)//2))
            check(paths(x,y,False), QQ(y+1)/(x+1)*binomial(x+1,(x+y+2)//2))


def n2(m,n):
    return QQ(m)/(2*n-m)*binomial(2*n-m,n)


for n in range(3, 41):
    triple = sum(binomial(t-2,t-i)*n2(m,n)
                 for i in range(2,n) for t in range(i,n)
                 for m in range(t+1,n+1))
    check(triple, binomial(2*n-2,n-3))
    double = sum((m-i+2)*binomial(m-1,m-i)*n2(m,n)
                 for i in range(1,n+1) for m in range(i,n+1))
    check(double, 4**(n-1)+binomial(2*n-1,n))
    # Formula (10) plus Lemma 6 yields the D_n formula in Theorem 2.
    catalan = lambda k: QQ(binomial(2*k,k))/(k+1)
    check(binomial(2*n-1,n-1)+triple+catalan(n)-catalan(n-1),
          binomial(2*n-1,n)+binomial(2*n-2,n))

# The printed inverse x=(1+sqrt(1-4w))/2 sends w=0 to x=1.
# This refutes precisely the printed branch claim '0 -> 0' on p.61.
check(QQ(1+1)/2, 1)
check(QQ(1-1)/2, 0)
assert QQ(1+1)/2 != 0

# Independent symplectic root-matrix normality check in characteristic two.
# We enumerate all root-coordinate supports, not arbitrary subgroups.
# Each commutator is a polynomial matrix over GF(2)[x,y], so its support
# is valid over arbitrary extensions. Completeness as D-invariant
# subgroups is the separate root-generation theorem cited in Lemma 3.
P = PolynomialRing(GF(2), names=('x','y'))
x, y = P.gens()
for n in range(1,5):
    roots = []
    positions = []
    for i in range(n):
        for j in range(i+1,n):
            a = matrix(P,2*n)
            a[i,j], a[n+j,n+i] = 1, -1
            roots.append(a)
            positions.append((i,j))
            a = matrix(P,2*n)
            a[i,n+j], a[j,n+i] = 1, 1
            roots.append(a)
            positions.append((i,n+j))
        a = matrix(P,2*n)
        a[i,n+i] = 1
        roots.append(a)
        positions.append((i,n+i))
    one = identity_matrix(P,2*n)
    dependencies = []
    for a in roots:
        needed = 0
        for b in roots:
            comm = (one-x*a)*(one-y*b)*(one+x*a)*(one+y*b)-one
            coefficients = [comm[i,j] for i,j in positions]
            # Verify these matrix entries ARE the collected root coordinates.
            # For this rank-two commutator its supported root matrices have
            # zero pairwise products; hence their root factors multiply to
            # one plus their linear sum, with no hidden cross terms.
            check(comm, sum((c*r for c,r in zip(coefficients,roots)),
                            matrix(P,2*n)))
            support = [r for c,r in zip(coefficients,roots) if c]
            for r in support:
                for s in support:
                    check(r*s, matrix(P,2*n))
            for k, (i,j) in enumerate(positions):
                if comm[i,j]:
                    needed |= 1 << k
        dependencies.append(needed)
    total = 0
    for mask in range(1 << len(roots)):
        if all(not (mask & (1<<k)) or not (deps & ~mask)
               for k, deps in enumerate(dependencies)):
            total += 1
    check(total, [2,7,26,99][n-1])
    check(total, 4**(n-1)+binomial(2*n-1,n))
print(f'ok l1996-enumeration: {checks} checks')
