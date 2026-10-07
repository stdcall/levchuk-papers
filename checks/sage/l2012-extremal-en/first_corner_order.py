"""Levchuk–Suleimanova2012, p.114, Lemma6.2: full projections need an inequality.

Exact counterexample UT(3,F4), all cyclic subgroups represented by every
element of UT(3,Fq), q=2,3,4,5,8. Conditional leading projections give the
filtration equality; full projections give the proved upper bound.
Checks the triangular quotient identity for every pair in UT(3,Fq),
q=2,3,4. This checks finite examples, not the full Lie-type classification.
"""
from sage.all import GF, matrix, identity_matrix, prod, RootSystem

checks = 0

def check(condition):
    global checks
    assert condition
    checks += 1

def canonical(g):
    # Order alpha1, alpha2, alpha1+alpha2, agreeing with root height.
    r, s = g[0, 1], g[1, 2]
    return (r, s, g[0, 2] - r*s)

def cyclic(g):
    I = identity_matrix(g.base_ring(), 3)
    elements = [I]
    h = g
    while h != I:
        elements.append(h)
        h = h*g
    return elements

def first(v):
    return next((i for i,x in enumerate(v) if x != 0), None)

def inspect(elements):
    vectors = [canonical(g) for g in elements]
    leading = set(first(v) for v in vectors) - {None}
    full = {i: set(v[i] for v in vectors) for i in leading}
    restricted = {i: set(v[i] for v in vectors if all(v[j] == 0 for j in range(i)))
                  for i in leading}
    check(len(elements) <= prod(len(full[i]) for i in leading))
    check(len(elements) == prod(len(restricted[i]) for i in leading))
    projected = [tuple(v[i] for i in sorted(leading)) for v in vectors]
    check(len(set(projected)) == len(elements))
    return leading, full, restricted

K = GF(4, 'a')
a = K.gen()
g = matrix(K, [[1,1,a],[0,1,1],[0,0,1]])
M = cyclic(g)
L, F, conditional = inspect(M)
check(len(M) == 4)
check(L == {0,2})
check(len(F[0]) == 2 and len(F[2]) == 4)
check(prod(len(F[i]) for i in L) == 8)
check(len(M) != prod(len(F[i]) for i in L))  # Refuted printed equality.
check(len(conditional[0]) == 2 and len(conditional[2]) == 2)
check(g*g == matrix(K, [[1,0,1],[0,1,0],[0,0,1]]))
print('counterexample UT(3,F4): |M|=4, L1={alpha1,alpha1+alpha2}, full projections=2,4, product=8')

for q in [2,3,4,5,8]:
    K = GF(q, 'z')
    for r in K:
        for s in K:
            for t in K:
                inspect(cyclic(matrix(K, [[1,r,t],[0,1,s],[0,0,1]])))

for q in [2,3,4]:
    K = GF(q, 'z')
    elements = [matrix(K, [[1,r,t],[0,1,s],[0,0,1]])
                for r in K for s in K for t in K]
    for g in elements:
        r,s,t = canonical(g)
        for h in elements:
            r0,s0,t0 = canonical(h)
            check(canonical(h.inverse()*g) ==
                  (r-r0, s-s0, t-t0+(r-r0)*s0))

# The p-abelian paragraph on p.114 needs r+s not in Phi, not merely Psi.
root = RootSystem(['A',2]).root_lattice()
simple = root.simple_roots()
r, s = simple[1], simple[2]
Psi = {r,s}
Phi = set(root.roots())
check(r+s not in Psi)
check(r+s in Phi)
print(f'ok l2012-extremal-en first-corner-order: {checks} checks')
