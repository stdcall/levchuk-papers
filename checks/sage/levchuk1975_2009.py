"""Bounded exact checks: additive GF4 exception, annihilator supports,
G2 root-lattice obstruction and SU3(q) largest abelian subgroups (q=2,3).
No classification of arbitrary-rank groups or their automorphisms is asserted.
Run with sage -python; output records execution provenance.
Passages: pass:l1975-automorphisms-additive-field-map,
pass:l1975-automorphisms-annihilator-identity,
tab:l2009-finitary-large-normal-abelian,
pass:l2009-finitary-unitary-conjugation,
eq:l2009-finitary-weyl-long-root-obstruction.
"""
from sage.all import GF, ZZ, matrix, vector, identity_matrix, cartesian_product
import hashlib, json, pathlib, datetime
from sage.env import SAGE_VERSION

checks = 0
def check(value):
    global checks
    assert value
    checks += 1

# GF4 has just two additive bijections fixing 1, and both are multiplicative.
E = GF(4, 'a'); a = E.gen()
fixed = []
for image in E:
    if image in (E(0), E(1)):
        continue
    def f(t):
        v = t.vector()
        return E(v[0]) + E(v[1])*image
    check(f(E(1)) == 1)
    check(len({f(t) for t in E}) == 4)
    check(all(f(x*y) == f(x)*f(y) for x in E for y in E))
    fixed.append(image)
check(len(fixed) == 2)
all_additive = 0
for first in E:
    if first == 0:
        continue
    for second in E:
        if second in (E(0), first):
            continue
        def additive(t):
            v = t.vector()
            return E(v[0])*first + E(v[1])*second
        check(any(all(additive(t) == first*t**power for t in E)
                  for power in (1,2)))
        all_additive += 1
check(all_additive == 6)

# Powers of the strictly lower triangular ring have support row-col >= p.
# Ann_r(R^(n-i)) means R^(n-i) A=0; Ann_l(R^i) means A R^i=0.
for n in range(3, 9):
    support = {(r,c) for r in range(n) for c in range(r)}
    for i in range(1,n):
        # A nonzero product B*A needs B.column = A.row.
        right = {(r,c) for r,c in support if
                 not any(l == r for k,l in support if k-l >= n-i)}
        left = {(r,c) for r,c in support if
                not any(k == c for k,l in support if k-l >= i)}
        check(right & left == {(r,c) for r,c in support if r >= i and c < i})

# Reflections on the G2 root lattice with a short, b long.
sa = matrix(ZZ,[[-1,3],[0,1]])
sb = matrix(ZZ,[[1,0],[1,-1]])
weyl = {tuple(identity_matrix(ZZ,2).list())}
pending = [identity_matrix(ZZ,2)]
while pending:
    w = pending.pop()
    for s in (sa,sb):
        v = w*s; key = tuple(v.list())
        if key not in weyl:
            weyl.add(key); pending.append(v)
check(len(weyl) == 12)
longs = {(3,1), (3,2)}
for key in weyl:
    w = matrix(ZZ,2,2,key)
    if w*vector(ZZ,(1,0)) == vector(ZZ,(2,1)):
        images = set()
        for root in longs:
            images.add(tuple(w*vector(ZZ,root)))
        check(images != longs)

# Explicit SU3(q) upper-unipotent matrices with Hermitian form J.
# u(t,z)=[[1,-bar(t),z],[0,1,t],[0,0,1]], z+bar(z)=-bar(t)t.
# Every commuting pair has t,s in the same GF(q)-line in GF(q^2).
unitary = {}
for q in (2,3):
    E = GF(q*q,'a'); bar = lambda t: t**q
    elements = []
    J = matrix(E,[[0,0,1],[0,1,0],[1,0,0]])
    for t in E:
        for z in E:
            if z+bar(z) == -bar(t)*t:
                u = matrix(E,[[1,-bar(t),z],[0,1,t],[0,0,1]])
                check(u.determinant() == 1)
                check(u.apply_map(bar).transpose()*J*u == J)
                elements.append((t,u))
    check(len(elements) == q**3)
    lines = {frozenset(E(k)*a for k in range(q)) for a in E if a != 0}
    check(len(lines) == q+1)
    groups = [tuple(u for t,u in elements if t in line) for line in lines]
    for group in groups:
        check(len(group) == q*q)
        keys = {tuple(u.list()) for u in group}
        for u in group:
            for v in group:
                check(u*v == v*u)
                check(tuple((u*v).list()) in keys)
        for _,g in elements:
            for u in group:
                check(tuple((g*u*g.inverse()).list()) in keys)
    for t,u in elements:
        for s,v in elements:
            check((u*v == v*u) == (bar(t)*s == bar(s)*t))
    # The centralizer of a noncentral element is exactly its line preimage;
    # every abelian subgroup is therefore bounded by q^2, attained above.
    for t,u in elements:
        if t != 0:
            check(sum(u*v == v*u for s,v in elements) == q*q)
    unitary[str(q)] = {'order_U': q**3, 'largest_abelian_order':q*q,
                       'number_largest':len(groups), 'all_normal':True}

# T10/T1,-1 is K^n; its commutator has coefficients
# v_i*bar(w_j)-w_i*bar(v_j). This verifies only this quotient model,
# not that every largest subgroup of the whole U lies in T10.
line_models = {}
for q,n in ((2,1),(2,2),(2,3),(3,1),(3,2)):
    E = GF(q*q,'a'); bar = lambda t:t**q
    vectors = [tuple(v) for v in cartesian_product([list(E)]*n)]
    nonzero = [v for v in vectors if any(v)]
    lines = {frozenset(tuple(E(c)*x for x in v) for c in range(q))
             for v in nonzero}
    check(len(lines) == (q**(2*n)-1)//(q-1))
    for v in nonzero:
        real_line = {tuple(E(c)*x for x in v) for c in range(q)}
        for w in vectors:
            commutes = all(v[i]*bar(w[j]) == w[i]*bar(v[j])
                           for i in range(n) for j in range(n))
            check(commutes == (w in real_line))
    line_models[f'{q}:{n}'] = len(lines)

# Parameter a in the twisted-D even-characteristic family is redundant
# modulo Fq*. Check the displayed subgroup sets themselves, not just orders.
orthogonal_scalar_families = {}
for q in (2,4):
    E = GF(q*q,'a')
    fixed = [x for x in E if x**q == x]
    check(len(fixed) == q)
    parameter_lines = {frozenset(a*x for x in fixed) for a in E if a != 0}
    check(len(parameter_lines) == q+1)
    families = {frozenset(tuple(a*x for x in v)
                         for v in cartesian_product([fixed]*4))
                for a in E if a != 0}
    check(len(families) == q+1)
    check(all(len(family) == q**4 for family in families))
    for a in E:
        for x in fixed:
            for y in fixed:
                check((a*x)*(a*y)**q + (a*x)**q*(a*y) == 0)
    orthogonal_scalar_families[str(q)] = len(families)

project = pathlib.Path(__file__).resolve().parents[2]
checked_text = {}
for article in ('l1975-automorphisms', 'l2009-finitary'):
    for file in sorted((project/'content'/'papers'/article).glob('*.typ')):
        checked_text[str(file.relative_to(project))] = hashlib.sha256(file.read_bytes()).hexdigest()
print(json.dumps({'checks':checks, 'sage':SAGE_VERSION,
 'script_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
 'executed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'GF4_fix_one_additive_automorphisms':2,'G2_weyl_order':len(weyl),
 'GF4_additive_automorphisms_all_semilinear':all_additive,
 'SU3':unitary, 'T10_real_lines':line_models,
 'twisted_D_even_scalar_families':orthogonal_scalar_families,
 'checked_text_sha256':checked_text},sort_keys=True))
