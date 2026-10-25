"""Counterexample to Theorem 1's characteristic-two C2 count.

Exhaustively checks an automorphism of U(C2,GF(4)) on all 65536 ordered
pairs, using explicit symplectic 4x4 matrices. In particular its action
on the two central root groups refutes the assertion that all seven
D-invariant normal subgroups are characteristic. No classification of
all automorphisms or all characteristic subgroups is claimed here.
"""
from sage.all import GF, matrix, identity_matrix, diagonal_matrix, PolynomialRing

F = GF(4, 'z')
I = identity_matrix(F,4)
A = matrix(F,4); A[0,1] = 1; A[3,2] = 1
B = matrix(F,4); B[1,3] = 1
C = matrix(F,4); C[0,3] = 1; C[1,2] = 1
D = matrix(F,4); D[0,2] = 1
checks = 0


def check(a,b):
    global checks
    assert a == b
    checks += 1


def elt(s,t,u,v):
    return (I+s*A)*(I+t*B)*(I+u*C)*(I+v*D)


def coordinates(g):
    s,t,u = g[0,1],g[1,3],g[1,2]
    return s,t,u,g[0,2]+s*u


def graph(g):
    s,t,u,v = coordinates(g)
    return (I+s**2*B)*(I+t*A)*(I+u**2*D)*(I+v*C)


# Symbolic bridge to the four-coordinate model formalized in Lean.
# Both identities hold as polynomial matrices in eight independent
# indeterminates over GF(2), before any finite-field specialization.
P = PolynomialRing(GF(2), names=('s','t','u','v','S','T','U','V'))
s,t,u,v,S,T,U,V = P.gens()
AA,BB,CC,DD = [r.change_ring(P) for r in (A,B,C,D)]
II = identity_matrix(P,4)


def symbolic_elt(s,t,u,v):
    return (II+s*AA)*(II+t*BB)*(II+u*CC)*(II+v*DD)


check(symbolic_elt(s,t,u,v)*symbolic_elt(S,T,U,V),
      symbolic_elt(s+S,t+T,u+U+S*t,v+V+S**2*t))
check((II+s**2*BB)*(II+t*AA)*(II+u**2*DD)*(II+v*CC),
      symbolic_elt(t,s**2,v+t*s**2,u**2+t**2*s**2))

elements = [elt(s,t,u,v) for s in F for t in F for u in F for v in F]
keys = {tuple(g.list()) for g in elements}
check(len(keys),256)
images = {tuple(graph(g).list()) for g in elements}
check(images,keys)
for g in elements:
    check(elt(*coordinates(g)),g)
    for h in elements:
        check(graph(g*h),graph(g)*graph(h))

# Explicit symplectic form, with basis e1,e2,f1,f2.
J = matrix(F,4)
for i in range(2):
    J[i,i+2] = 1
    J[i+2,i] = 1
for g in elements:
    check(g.transpose()*J*g,J)

short_centre = {tuple((I+u*C).list()) for u in F}
long_centre = {tuple((I+v*D).list()) for v in F}
check(F.characteristic(),2)
check(F.cardinality(),4)
for u in F:
    root_element = I+u*C
    for g in elements:
        check(root_element*g,g*root_element)
    for l in F:
        for m in F:
            if l and m:
                torus = diagonal_matrix(F,[l,m,l**(-1),m**(-1)])
                check(tuple((torus**(-1)*root_element*torus).list())
                      in short_centre,True)
check({tuple(graph(I+u*C).list()) for u in F},long_centre)
check(short_centre == long_centre,False)
check(graph(I+C),I+D)
print(f'ok l1996-c2-characteristic-counterexample: {checks} checks')
