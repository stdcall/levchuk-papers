"""Exact checks of Levchuk (1976), printed pages 573–576.

eq:prime-abelian, eq:prime-lie-abelian: the commutator of the corner
terms, the Delta multiplication, its normality condition in characteristic
two, and annihilation by the lower-left rectangle. Free associative
coefficient algebras preserve the order of noncommuting factors. Matrix
ranks are 3 through 7, and all admissible interior indices are checked.

lem:division-pair: a pair product commutes with its reverse precisely
when its two coordinates coincide; mere containment in the ambient pair
ring, as printed on page 575, is insufficient.

The final integral example refutes the printed condition "arbitrary"
for the pair set at rank three, page 574, while preserving all assumptions
of (7). The checks do not prove the classification or general maximality
assertions of Lemmas 7–11.
"""
from sage.all import FreeAlgebra, GF, QQ, ZZ, matrix, vector, zero_matrix

F = FreeAlgebra(QQ, 6, names='a,b,c,d,x,y')
a,b,c,d,x,y = F.gens()
checks = 0

def E(base, n, i, j, coefficient=1):
    result = zero_matrix(base, n)
    result[i-1,j-1] = coefficient
    return result

for n in range(3,8):
    for i in range(2,n):
        A = E(F,n,i,1,a) + E(F,n,n,i,b)
        B = E(F,n,i,1,c) + E(F,n,n,i,d)
        assert A*B-B*A == E(F,n,n,1,b*c-d*a)
        checks += 1

# Printed (K,K) is the whole ambient set and hence cannot express
# commutativity: these two rational pairs refute its sufficiency.
p,q = (1,0),(0,1)
delta = lambda u,v: (u[1]*v[0],v[1]*u[0])
assert delta(p,q) != delta(q,p)
assert delta(p,q)[0] != delta(p,q)[1]
checks += 1

F2 = FreeAlgebra(GF(2), 9, names='a11,a12,a21,a22,b11,b12,b21,b22,x')
a11,a12,a21,a22,b11,b12,b21,b22,x = F2.gens()
for n in range(4,8):
    for i in range(2,n-1):
        A = (E(F2,n,i,1,a11) + E(F2,n,n,i,a12)
             + E(F2,n,i+1,1,a21) + E(F2,n,n,i+1,a22))
        B = (E(F2,n,i,1,b11) + E(F2,n,n,i,b12)
             + E(F2,n,i+1,1,b21) + E(F2,n,n,i+1,b22))
        diagonal_first = a12*b11 + a22*b21
        diagonal_second = b12*a11 + b22*a21
        assert A*B-B*A == E(F2,n,n,1,
                           diagonal_first-diagonal_second)
        X = E(F2,n,i+1,i,x)
        assert A*X-X*A == (E(F2,n,n,i,a22*x)
                           + E(F2,n,i+1,1,x*a11))
        # The low-left rectangle in (8) annihilates all four corner terms.
        for k in range(i+2,n+1):
            for l in range(1,i):
                U = E(F2,n,k,l,x)
                assert U*A == 0 and A*U == 0
        checks += 3

print(f'ok pairs: {checks} identity groups; free algebras QQ/GF(2)')

# Printed "arbitrary when n=3" fails even under the constraints of (7).
# Both coordinate annihilators of M=2ZZ*(1,1) in ZZ are zero.
basis = [E(ZZ,3,3,1), 2*(E(ZZ,3,2,1)+E(ZZ,3,3,2))]
coordinates = lambda X: vector(ZZ,[X[1,0],X[2,0],X[2,1]])
H = matrix(ZZ,[coordinates(B) for B in basis]).row_module()
larger_basis = [E(ZZ,3,3,1), E(ZZ,3,2,1)+E(ZZ,3,3,2)]
H_larger = matrix(ZZ,[coordinates(B) for B in larger_basis]).row_module()
assert H.is_submodule(H_larger) and H != H_larger
for X in basis:
    for Y in basis:
        assert X*Y-Y*X == 0
    for i,j in [(2,1),(3,1),(3,2)]:
        U = E(ZZ,3,i,j)
        assert coordinates(X*U) in H and coordinates(U*X) in H
for X in larger_basis:
    for Y in larger_basis:
        assert X*Y-Y*X == 0
    for i,j in [(2,1),(3,1),(3,2)]:
        U = E(ZZ,3,i,j)
        assert coordinates(X*U) in H_larger
        assert coordinates(U*X) in H_larger
print('ok pairs: admissible ZZ counterexample to arbitrary M at n=3')
