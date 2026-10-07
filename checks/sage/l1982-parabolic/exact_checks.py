"""Exact bounded checks for Levchuk 1982, printed pp. 510, 514–515, 519–523.

Uses Sage 10.9. These finite computations do not prove the general theorems,
ring hypotheses, root-folding extension to all lattices, or lemma 14.
Expected root bounds come from lemma 12 and folded types from lemma 7;
the GF(4) example is the author's example after lemma 14.
"""
from itertools import combinations, permutations
from sage.all import CartanType, FreeGroup, GF, Matrix, RootSystem, ZZ, gcd, identity_matrix

checks = 0

def verify(statement):
    global checks
    assert statement
    checks += 1

# Printed p. 510 suppresses all factors after the second despite r > 1.
# Keep the literal printed two-factor equality as a refuted check.
F = FreeGroup(4, names=('a', 'b', 'c', 't'))
a, b, c, t = F.gens()
phi = lambda x: t * x * t**-1
lhs = phi(a*b*c) * (a*b*c)**-1
printed_two_factors = phi(a)*phi(b)*b**-1*a**-1
verify(lhs != printed_two_factors)
verify(lhs == phi(a)*phi(b)*phi(c)*c**-1*b**-1*a**-1)
verify(phi(a*b)* (a*b)**-1 == (phi(a)*a**-1)*(a*(phi(b)*b**-1)*a**-1))

# Lemma 7: projection of simple-root coordinates onto diagram orbits.
folds = []
for k in range(2, 5):
    folds.append((['A', 2*k-1], [[i, 2*k-i] for i in range(1,k)]+[[k]], 2*k*k))
for k in range(1, 5):
    folds.append((['A', 2*k], [[i, 2*k+1-i] for i in range(1,k+1)], 2*k*(k+1)))
for l in range(4, 9):
    folds.append((['D', l], [[i] for i in range(1,l-1)]+[[l-1,l]], 2*(l-1)**2))
folds += [(['D', 4], [[1,3,4],[2]], 12), (['E',6], [[1,6],[3,5],[2],[4]],48)]
for ct, orbits, expected in folds:
    roots = RootSystem(ct).root_lattice().roots()
    image = {tuple(sum(r[i] for i in orbit) for orbit in orbits) for r in roots}
    verify(len(image) == expected)
    verify(tuple(0 for _ in orbits) not in image)
    A = CartanType(ct).cartan_matrix()
    B = Matrix(ZZ, [[sum(A[orbit[0]-1,j-1] for j in other) for other in orbits] for orbit in orbits])
    if ct[0] == 'A' and ct[1] % 2 == 0:
        verify(B.det() == 1)
    print('fold', ct, 'roots', len(image), 'det', B.det())

# Lemma 12: root and full weight lattices, all independent root pairs.
# Primitive r generates the kernel equation for characters chi(r)=1.
# d is gcd of 2x2 minors / gcd(r); this is the Smith invariant of s mod Zr.
types = ([['A', l] for l in range(2,9)] + [['B',l] for l in range(3,9)]
         + [['C',l] for l in range(2,9)] + [['D',l] for l in range(4,9)]
         + [['E',6],['E',7],['E',8],['F',4],['G',2]])
pair_count = 0
for ct in types:
    system = RootSystem(ct)
    roots = list(system.root_lattice().roots())
    rho = {'A':1,'B':2,'C':2,'D':1,'E':1,'F':2,'G':3}[ct[0]]
    for lattice_name, lattice in [('root',system.root_lattice()),('weight',system.weight_lattice())]:
        rows = [tuple(ZZ(x) for x in lattice(r).to_vector()) for r in roots]
        maximum = 0
        for r,s in permutations(rows,2):
            minors = [r[i]*s[j]-r[j]*s[i] for i,j in combinations(range(len(r)),2)]
            g = gcd(minors)
            if g == 0:
                continue
            d = g // gcd(r)
            bound = rho
            if lattice_name == 'weight':
                if ct == ['A',2]: bound = 3
                elif ct == ['A',3] or ct[0] == 'D': bound = 2
            verify(1 <= d <= bound)
            maximum = max(maximum,d)
            pair_count += 1
        if lattice_name == 'root':
            verify(maximum == rho)
        if lattice_name == 'weight' and (ct[0] == 'A' and ct[1]>=4 or ct[0]=='E'):
            verify(maximum == 1)
        print('isolation', ct, lattice_name, 'max d', maximum)
print('independent pairs',pair_count)

# Printed p. 523: admissible elementary carpet over GF(4) with A21={0,1},
# A12={0,a}, which cannot extend to a full carpet (lemma 6).
K = GF(4, 'a')
a = K.gen()
I = identity_matrix(K,2)
lower = Matrix(K,[[1,0],[1,1]])
upper = Matrix(K,[[1,a],[0,1]])
for x in (I,lower,upper): x.set_immutable()
group = {I}
frontier = [I]
while frontier:
    x = frontier.pop()
    for y in (lower,upper):
        z = x*y
        z.set_immutable()
        if z not in group:
            group.add(z)
            frontier.append(z)
verify(len(group)==10)
lower_parameters = {x[1,0] for x in group if x[0,0]==1 and x[1,1]==1 and x[0,1]==0}
upper_parameters = {x[0,1] for x in group if x[0,0]==1 and x[1,1]==1 and x[1,0]==0}
verify(lower_parameters == {K(0),K(1)})
verify(upper_parameters == {K(0),a})
verify(K(1)*a*K(1) not in lower_parameters)
print('GF(4) group order',len(group),'root intersections',lower_parameters,upper_parameters)
print(f'ok l1982-parabolic: {checks} checks')
