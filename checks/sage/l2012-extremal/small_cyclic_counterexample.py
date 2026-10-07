"""Bounded counterexample to the unrestricted SL(n,K) example, p. 166.

Checks only SL(2, F_2); does not repair the author's assertion for all n,K.
All elements are explicit 2-by-2 matrices, with exact field arithmetic.
"""
from itertools import product
from sage.all import GF, matrix, identity_matrix
from sage.version import version

F = GF(2)
G = [matrix(F,2,2,a) for a in product(F,repeat=4)
     if matrix(F,2,2,a).det() == 1]
one = identity_matrix(F,2)
def token(g): return tuple(g.list())
def cyclic(g):
    result = {token(one)}
    h = g
    while token(h) not in result:
        result.add(token(h))
        h *= g
    return result

C = [cyclic(g) for g in G]
H = next(H for H in C if len(H)==3)
checks=0
def check(value):
    global checks
    assert value
    checks+=1
check(len(G)==6)
check(max(map(len,C))==3)
check(len({token(g) for g in G if all(g*h==h*g for h in G)})==1)
for g in G:
    for h in G:
        if token(h) in H:
            check(token(g*h*g.inverse()) in H)
print(f"SL(2,F2): order 6; center order 1; normal cyclic subgroup order 3 "
      f"attains the largest cyclic order. {checks} assertions; Sage {version}.")

# A concrete valid replacement of the illustrative example.
G3 = [matrix(F,3,3,a) for a in product(F,repeat=9)
      if matrix(F,3,3,a).det() == 1]
one3 = identity_matrix(F,3)
def cyclic3(g):
    result = {token(one3)}
    h = g
    while token(h) not in result:
        result.add(token(h))
        h *= g
    return frozenset(result)

cyclic_subgroups = set(map(cyclic3,G3))
check(len(G3)==168)
check(max(map(len,cyclic_subgroups))==7)
normal_cyclic = []
conjugates_checked = 0
for H in cyclic_subgroups:
    matrices = [matrix(F,3,3,h) for h in H]
    bad = None
    for g in G3:
        for h in matrices:
            conjugates_checked += 1
            if token(g*h*g.inverse()) not in H:
                bad = (g,h)
                break
        if bad is not None:
            break
    if bad is None:
        normal_cyclic.append(H)
    else:
        g,h = bad
        check(token(g*h*g.inverse()) not in H)
check(normal_cyclic == [frozenset({token(one3)})])
check(len([g for g in G3 if all(g*h==h*g for h in G3)])==1)
print(f"SL(3,F2): order 168; {len(cyclic_subgroups)} distinct cyclic subgroups; "
      f"center order 1; only normal cyclic subgroup is 1; largest cyclic order 7. "
      f"{conjugates_checked} conjugates tested; {checks} cumulative assertions; Sage {version}.")
