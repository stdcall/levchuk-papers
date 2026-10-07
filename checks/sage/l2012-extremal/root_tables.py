"""Exact audit of the article's E6/E7/E8 root lists, printed pp. 162–163.

Readings are literal data from the Russian article. Root numbering is
Bourbaki's: alpha_2 branches at alpha_4, as on printed p. 157.
Literature: Carter, Simple Groups of Lie Type (1972), §3.6 (root systems),
§3.4 (Dynkin diagrams); the article's formula (2) fixes r+r'+p=rho.

Checks all listed normal commutative subsets and independently enumerates
all abelian root ideals. Proves exhaustion of the maximal ones, and detects
the two non-maximal rows literally printed under the maximality heading.
It does NOT prove the classification of group subgroups, theorem 2.6,
twisted groups, or the conjugacy statements of §4.
"""
from sage.all import RootSystem
from sage.version import version
import re

checks = 0
def check(value):
    global checks
    assert value
    checks += 1

def decode(s, n):
    m = re.fullmatch(r"(\d)(\d)\[(\d)(\d)\]'(\d+)", s)
    assert m
    a,c,d,b,tail = m.groups()
    v = tuple(map(int, a+b+c+d+tail))
    assert len(v) == n
    return v

def unit(i,n):
    return tuple(int(j==i) for j in range(1,n+1))

def plus(a,b):
    return tuple(x+y for x,y in zip(a,b))

A = {
 6: [ ['a1'], ["01[21]'10"],
      ["11[10]'11","11[21]'10","01[21]'11"],
      ["11[10]'10","01[21]'21"] ],
 7: [ ['a7'], ["12[32]'210","00[11]'111"], ["12[21]'100"],
      ["12[31]'210","01[21]'111"], ["01[21]'210"],
      ["11[21]'210","01[21]'211"],
      ["12[21]'210","12[21]'111","01[21]'211"],
      ["12[21]'110","01[21]'221"] ],
 8: [ ["12[32]'2100"], ["12[31]'3210"],
      ["12[32]'3210","12[31]'3211"],
      ["12[32]'2210","12[31]'3321"],
      ["12[42]'3210","12[31]'2221"],
      ["13[42]'3210","12[21]'2221"],
      ["23[42]'3210","11[21]'2221"],
      ["12[32]'3210","12[32]'2221","12[31]'3221"],
      ["01[21]'2221"] ]
}
B = {
 6: ["11[11]'00","11[11]'10","01[21]'10"],
 7: ["11[10]'111","12[21]'100","12[21]'110","11[21]'210","11[21]'111","11[11]'111"],
 8: ["12[32]'2111","12[32]'2211","12[31]'3211","12[32]'3211","12[21]'2221","11[21]'2221","01[21]'2221"]
}
C = {
 6: [("11[11]'00",'a5'),("11[11]'10",'a6'),("11[11]'10",'a4')],
 7: [("12[21]'110","11[21]'111"),("12[21]'100","11[21]'211"),
      ("12[21]'110","11[21]'210"),("11[21]'210","11[21]'111"),
      ("12[21]'210","11[11]'111"),("12[31]'210","11[10]'111")],
 8: [("12[31]'3221","12[32]'2111"),("12[31]'3211","12[32]'2211"),
      ("12[31]'2221","12[31]'3211"),("12[31]'2221","12[32]'2211"),
      ("12[21]'2221","12[32]'3211"),("11[21]'2221","12[42]'3211")]
}
D = {6:["11[10]'10","01[10]'11"],7:["01[21]'210","01[21]'111"],8:["12[31]'3210","12[32]'2210"]}
E = {6:["11[11]'10","01[21]'10","01[11]'11"],7:["12[21]'110","11[21]'210","11[21]'111"],8:["12[31]'2221","12[31]'3211","12[32]'2211"]}

for n, count, h in [(6,36,12),(7,63,18),(8,120,30)]:
    lattice = RootSystem(['E',n]).root_lattice()
    roots = set(tuple(r[i] for i in range(1,n+1)) for r in lattice.positive_roots())
    rho = max(roots,key=sum)
    check(len(roots)==count)
    check(sum(rho)+1==h)
    def parse(s):
        return unit(int(s[1:]),n) if s.startswith('a') else decode(s,n)
    upper = {r:frozenset(s for s in roots if all(b>=a for a,b in zip(r,s))) for r in roots}
    incompatible = {r:frozenset(s for s in roots if plus(r,s) in roots) for r in roots}
    def abelian(I):
        return all(not (incompatible[r] & I) for r in I)
    listed = []
    for row in A[n]:
        generators = [parse(s) for s in row]
        for r in generators: check(r in roots)
        I = frozenset().union(*(upper[r] for r in generators))
        check(abelian(I))
        for r in roots-I:
            expected_extension = (
                n == 7 and row == A[7][5] and r == decode("01[21]'210",7)
                or n == 8 and row == A[8][2] and r == decode("12[31]'3210",8)
            )
            check(abelian(I | upper[r]) == expected_extension)
        listed.append(I)
    # Independent enumeration by adjoining each positive-root upper cone.
    ideals = {frozenset()}
    queue = [frozenset()]
    while queue:
        I = queue.pop()
        for r in roots-I:
            J = I | upper[r]
            if J not in ideals and abelian(J):
                ideals.add(J)
                queue.append(J)
    check(len(ideals)==2**n)
    maximal = {I for I in ideals if not any(I<J for J in ideals)}
    if n == 6:
        # Diagram involution 1<->6, 3<->5, with 2,4 fixed.
        def mirror(r):
            return (r[5],r[1],r[4],r[3],r[2],r[0])
        listed += [frozenset(mirror(r) for r in I) for I in listed]
    check(maximal <= set(listed))
    nonmaximal = set(listed)-maximal
    check(len(nonmaximal) == (0 if n == 6 else 1))
    if n == 7:
        check(listed[5] < listed[4])
        check(nonmaximal == {listed[5]})
    if n == 8:
        check(listed[2] < listed[1])
        check(nonmaximal == {listed[2]})
    for token in B[n]:
        r = parse(token)
        check(r in roots)
        check(tuple(a-b for a,b in zip(rho,r)) in roots)
    c_simple = []
    for rtoken,stoken in C[n]:
        r,s = parse(rtoken),parse(stoken)
        check(r in roots)
        check(s in roots)
        if n == 6:
            p = s
            rprime = tuple(a-b-c for a,b,c in zip(rho,r,p))
        else:
            rprime = s
            p = tuple(a-b-c for a,b,c in zip(rho,r,rprime))
            # Refutes literal heading {r,p} for these printed pairs.
            check(s not in {unit(i,n) for i in range(1,n+1)})
        check(p in {unit(i,n) for i in range(1,n+1)})
        check(rprime in roots)
        check(plus(r,p) in roots)
        check(plus(rprime,p) in roots)
        c_simple.append(p.index(1)+1)
    for token in D[n]+E[n]: check(parse(token) in roots)
    print(f"E{n}: {len(roots)} positive roots; {len(ideals)} abelian normal root ideals; "
          f"{len(maximal)} maximal, exhausted by A (E6 with symmetry); "
          f"{len(nonmaximal)} non-maximal printed rows; C simple p indices {c_simple}")
print(f"ok l2012-extremal root tables: {checks} assertions; Sage {version}")
