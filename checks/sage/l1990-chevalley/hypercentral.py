"""Bounded exact checks for Levchuk, §1 and lemmas 2–4.

Root coordinates are those printed in lemma 2, not an unspecified Sage
Chevalley basis. Matrices use the ordered basis n,...,1,0,-1,...,-n (omit
0 outside B). The group commutator is A^-1B^-1AB, as in Carter §5.2.
Finite cases below verify defining root relations, not the classification.
"""
from itertools import product
from time import perf_counter
from sage.all import GF, QQ, ZZ, PolynomialRing, Zmod, identity_matrix, matrix

COUNTS = {}


def checked(name, condition):
    assert condition, name
    COUNTS[name] = COUNTS.get(name, 0) + 1


class Classical:
    def __init__(self, kind, n, ring):
        self.kind, self.n, self.R = kind, n, ring
        self.indices = list(range(n, 0, -1))
        if kind == 'B':
            self.indices += [0]
        if kind != 'A':
            self.indices += list(range(-1, -n-1, -1))
        self.pos = {v: i for i, v in enumerate(self.indices)}
        self.dim = len(self.indices)
        self.I = identity_matrix(ring, self.dim)
        self.roots = {}
        for i in range(1, n+1):
            for j in range(1, i):
                e = self.E(i, j)
                if kind != 'A':
                    e -= self.E(-j, -i)
                self.roots[self.root(i, j)] = e
                if kind in 'BCD':
                    e = self.E(i, -j) + self.E(j, -i)
                    if kind in 'BD':
                        e = -self.E(i, -j) + self.E(j, -i)
                    self.roots[self.root(i, -j)] = e
            if kind == 'B':
                self.roots[self.root(i, 0)] = self.E(i, 0)-2*self.E(0, -i)
            if kind == 'C':
                self.roots[self.root(i, -i)] = self.E(i, -i)
        self.order = sorted(self.roots, key=lambda r: (self.height(r), r))
        self.pivots = {}
        for r, e in self.roots.items():
            # An integral coefficient ±1 allows extraction over any ring.
            self.pivots[r] = next((i, j, e[i,j]) for i in range(self.dim)
                                 for j in range(self.dim) if e[i,j] in [1,-1])

    def root(self, i, j):
        r = [0]*self.n
        r[i-1] += 1
        if j:
            r[abs(j)-1] += -1 if j > 0 else 1
        return tuple(r)

    def E(self, i, j):
        e = matrix(self.R, self.dim)
        e[self.pos[i], self.pos[j]] = 1
        return e

    def height(self, r):
        if self.kind == 'A':
            return sum((i+1)*x for i, x in enumerate(r))
        shift = {'B': 0, 'C': QQ(1)/2, 'D': 1}[self.kind]
        return sum((i+1-shift)*x for i, x in enumerate(r))

    def X(self, r, t):
        e = self.roots[r]
        g = self.I + t*e
        if self.kind == 'B' and sum(r) == 1:
            i = r.index(1)+1
            g -= t*t*self.E(i, -i)
        return g

    def x(self, i, j, t):
        return self.X(self.root(i, j), t)

    def factors(self, g):
        result = []
        for r in self.order:
            i, j, sign = self.pivots[r]
            t = sign*g[i,j]
            if t:
                result.append((r, t))
                g = self.X(r, -t)*g
        assert g == self.I, ('not a root normal form', self.kind, g)
        return result

    def apply(self, g, images):
        result = self.I
        for r, t in self.factors(g):
            result *= images(r, t)
        return result

    def comm(self, a, b):
        return a.inverse()*b.inverse()*a*b


def relations(name, model, images, values):
    vals = list(values)
    for r in model.order:
        for t, u in product(vals, repeat=2):
            checked(name+'.addition', images(r,t)*images(r,u)
                    == images(r,t+u))
    for r, s in product(model.order, repeat=2):
        for t, u in product(vals, repeat=2):
            comm = model.comm(model.X(r,t), model.X(s,u))
            checked(name+'.commutator',
                    model.comm(images(r,t), images(s,u))
                    == model.apply(comm, images))


def altered(model, table):
    return lambda r,t: table[r](t) if r in table else model.X(r,t)


def eq3(m, d, reflected=False):
    n = m.n
    if not reflected:
        q,r,qr = m.root(2,1),m.root(3,2),m.root(3,1)
        table = {
            q: lambda t: m.X(q,t)*m.x(n,3,d*t),
            r: lambda t: m.X(r,t)*m.x(n,2,d*(t*t-t)),
            qr: lambda t: m.X(qr,t)*m.x(n,2,d*t)*m.x(n,1,d*t*t),
        }
    else:
        q,r,qr = m.root(n,n-1),m.root(n-1,n-2),m.root(n,n-2)
        table = {
            q: lambda t: m.X(q,t)*m.x(n-2,1,d*t),
            r: lambda t: m.X(r,t)*m.x(n-1,1,d*(t*t-t)),
            qr: lambda t: m.X(qr,t)*m.x(n-1,1,d*t)*m.x(n,1,d*t*t),
        }
    return altered(m, table)


def eq5(m, b):
    q, a, p = m.root(2,1), m.root(2,-1), m.root(2,0)
    rho = m.root(1,0)
    return altered(m, {
        q: lambda t: m.X(q,t)*m.x(3,0,b*t),
        a: lambda t: m.X(a,t)*m.x(3,0,-b*t),
        p: lambda t: m.X(p,t)*m.x(3,1,-b*t)*m.x(3,-1,b*t),
        rho: lambda t: m.X(rho,t)*m.x(3,2,b*t),
    })


def eq6(m, b, printed=False):
    q,r,qr = m.root(3,2),m.root(2,1),m.root(3,1)
    return altered(m, {
        q: lambda t: (m.I if printed else m.X(q,t))
        *m.x(2,-1,b*t)*m.x(3,-1,b*t*t),
        r: lambda t: m.X(r,t)*m.x(3,-2,b*(t**3-t)),
        qr: lambda t: m.X(qr,t)*m.x(2,-2,b*t)*m.x(3,-3,-b*t**3),
    })


def structure_checks():
    R = PolynomialRing(ZZ, ['x','y'])
    x,y = R.gens()
    for kind in 'BCD':
        m = Classical(kind, 3, R)
        lie = lambda a,b: a*b-b*a
        i,j,k = 3,2,1
        e = lambda a,b: m.roots[m.root(a,b)]
        checked('lemma2.chain.'+kind, lie(e(i,j),e(j,k)) == e(i,k))
        for v in [-k,k]:
            checked('lemma2.signed-chain.'+kind,
                    lie(e(i,j),e(j,v)) == e(i,v))
            checked('eq9.signed-chain.'+kind,
                    m.comm(m.x(i,j,x),m.x(j,v,y)) == m.x(i,v,x*y))
        if kind in 'BD':
            checked('lemma2.orthogonal.'+kind,
                    lie(e(j,k),e(i,-k)) == e(i,-j))
            checked('lemma3.a.'+kind,
                    m.comm(m.x(j,k,x),m.x(i,-k,y)) == m.x(i,-j,x*y))
        if kind == 'B':
            checked('lemma2.B.short', lie(e(i,0),e(j,0)) == 2*e(i,-j))
            checked('lemma3.B.short', m.comm(m.x(i,0,x),m.x(j,0,y))
                    == m.x(i,-j,2*x*y))
            checked('lemma3.B.mixed', m.comm(m.x(i,j,x),m.x(j,0,y))
                    == m.x(i,0,x*y)*m.x(i,-j,x*y*y))
        if kind == 'C':
            checked('lemma2.C.double', lie(e(i,j),e(i,-j)) == 2*e(i,-i))
            checked('lemma2.C.mixed', lie(e(j,k),e(i,-k)) == e(i,-j))
            checked('lemma3.C.double', m.comm(m.x(i,j,x),m.x(i,-j,y))
                    == m.x(i,-i,2*x*y))
            checked('lemma3.C.cubic', m.comm(m.x(i,j,x),m.x(j,-j,y))
                    == m.x(i,-j,x*y)*m.x(i,-i,-x*x*y))
            checked('lemma3.C.g1',m.comm(m.x(i,k,x),m.x(j,-k,y))
                    == m.x(i,-j,x*y))
            checked('lemma3.C.g2',m.comm(m.x(j,k,x),m.x(i,-k,y))
                    == m.x(i,-j,x*y))
    # Literal s-q in the A3 list is not a root; s+q is the highest root.
    a = Classical('A',4,ZZ)
    q,s = a.root(2,1),a.root(4,2)
    checked('printed.length.s-minus-q.refuted',
            tuple(u-v for u,v in zip(s,q)) not in a.roots)
    checked('corrected.length.s-plus-q',
            tuple(u+v for u,v in zip(s,q)) == a.root(4,1))
    c = Classical('C',3,ZZ)
    printed = {c.root(i,j) for i in range(1,4) for j in range(1,i)}
    printed |= {c.root(i,-j) for i in range(1,4) for j in range(1,i)}
    checked('printed.C-range.refuted', c.root(1,-1) not in printed)
    checked('corrected.C-range', printed | {c.root(i,-i) for i in range(1,4)}
            == set(c.roots))
    b = Classical('B',3,ZZ)
    printed_b = {b.root(i,j) for i in range(1,4) for j in range(1,i)}
    printed_b |= {b.root(i,-j) for i in range(1,4) for j in range(1,i)}
    printed_b |= {b.root(i,0) for i in range(2,4)}
    checked('printed.B-range.refuted',b.root(1,0) not in printed_b)
    checked('corrected.B-range',printed_b | {b.root(1,0)} == set(b.roots))


def finite_maps():
    # Literal (5): b=0 satisfies its conditions, and the earlier d=1 over
    # F2 even satisfies 2d=d J2 J2=0. Leaving this unrelated d in (5) fails.
    F = GF(2)
    m = Classical('B',3,F)
    b,d = F(0),F(1)
    checked('printed.eq5.hypotheses',3*b==0 and 2*d==0 and
            all(b*(t**3-t)==0 and t*t-t==0 for t in F))
    im = eq5(m,d)
    q,rho = m.root(2,1),m.root(1,0)
    checked('printed.eq5.refuted',m.comm(im(q,F(1)),im(rho,F(1)))
            != m.apply(m.comm(m.X(q,1),m.X(rho,1)),im))
    for R,b in [(GF(3),1),(Zmod(9),3)]:
        b = R(b)
        checked('eq5.hypotheses', 3*b == 0 and all(b*(t**3-t)==0 for t in R))
        m = Classical('B',3,R)
        relations('eq5.'+str(R.cardinality()),m,eq5(m,b),R)
    for R,b in [(GF(3),1),(GF(3),0)]:
        b = R(b)
        checked('eq6.hypotheses', 3*b == 0 and
                all(b*(t**3-t)*(u**3-u)==0 for t,u in product(R,repeat=2)))
        m = Classical('C',3,R)
        relations('eq6.'+str(b),m,eq6(m,b),R)
    m = Classical('C',3,GF(3))
    q = m.root(3,2)
    checked('printed.eq6.noninjective.refuted',
            eq6(m,GF(3)(0),True)(q,GF(3)(1)) == m.I and m.X(q,1) != m.I)
    m = Classical('A',4,GF(2))
    relations('eq3.F2',m,eq3(m,GF(2)(1)),GF(2))
    R = PolynomialRing(GF(2),'e')
    K = R.quotient(R.gen()**2,'e')
    e = K.gen()
    vals = [K(0),K(1),e,1+e]
    checked('eq3.dual.hypotheses', all(2*t==0 for t in vals) and
            all((t*t-t)*(u*u-u)==0 for t,u in product(vals,repeat=2)))
    m = Classical('A',4,K)
    relations('eq3.dual',m,eq3(m,K(1)),vals)
    m = Classical('D',4,GF(2))
    qrr,qr,qrp,r,rp = [m.root(*v) for v in [(3,-2),(3,1),(3,-1),(2,1),(2,-1)]]
    images = altered(m, {
        qrr: lambda t: m.X(qrr,t)*m.x(4,-1,t)*m.x(4,1,t)*m.x(4,-3,t),
        qr: lambda t: m.X(qr,t)*m.x(4,2,t)*m.x(4,1,t),
        qrp: lambda t: m.X(qrp,t)*m.x(4,2,t)*m.x(4,-1,t),
        r: lambda t: m.X(r,t)*m.x(4,3,t),
        rp: lambda t: m.X(rp,t)*m.x(4,3,t),
    })
    checked('eq4.hypotheses', all(t*t-t==0 for t in GF(2)))
    relations('eq4.D4.F2',m,images,GF(2))


def polynomial_maps():
    R = PolynomialRing(QQ,['t','u'])
    t,u = R.gens()
    a = Classical('A',4,R)
    q = a.root(2,1)
    checked('eq1.hypotheses', (t+u)**2 == t*t+u*u+2*t*u)
    checked('eq1.d-definition',R(2)**2-2*R(1)**2 == 2)
    images = altered(a,{q: lambda z:a.X(q,z)*a.x(4,2,2*z)*a.x(4,1,z*z)})
    relations('eq1.QQ',a,images,[t,u])
    c = Classical('C',3,R)
    q = c.root(3,2)
    lam1 = lambda z:(z-z*z)/2
    lam = lambda z:z**3/3-z*z/2
    checked('eq2.lambda1',lam1(t+u)==lam1(t)+lam1(u)-t*u)
    checked('eq2.lambda',lam(t+u)==lam(t)+lam(u)+t*u*(t+u-1))
    checked('eq2.normalization',lam1(R(1))==0 and -lam1(R(2))==1)
    checked('eq2.double-lambda1',2*lam1(t)==t-t*t)
    images = altered(c,{q:lambda z:c.X(q,z)*c.x(2,-2,z)
                       *c.x(3,-2,lam1(z))*c.x(3,-3,lam(z))})
    relations('eq2.QQ',c,images,[t,u])
    raw = altered(c,{q:lambda z:c.X(q,z)*c.x(2,-2,z)
                    *c.x(3,-2,-z*z/2)*c.x(3,-3,z**3/3)})
    relations('eq2.raw.QQ',c,raw,[t,u])
    inner = c.x(2,-2,R(1)/2)
    for z in [t,u]:
        checked('eq2.raw-inner-normalization',
                inner.inverse()*raw(q,z)*inner == images(q,z))


def twist_refutation():
    m = Classical('A',3,GF(9,'a'))
    bar = lambda t:t**3
    printed = lambda r,t:m.X(r,-bar(t))
    x,y = m.x(3,2,1),m.x(2,1,1)
    checked('printed.twist-A.refuted',m.comm(m.apply(x,printed),m.apply(y,printed))
            != m.apply(m.comm(x,y),printed))
    J = matrix(m.R,m.dim,lambda i,j: 1 if i+j==m.dim-1 else 0)
    corrected = lambda g:J*matrix(m.R,m.dim,lambda i,j:bar(g[i,j])).inverse().transpose()*J
    checked('corrected.twist-A.multiplicative',corrected(x*y)==corrected(x)*corrected(y))
    checked('corrected.twist-A.involution',corrected(corrected(x*y))==x*y)


def twisted_d_checks():
    # Involution swaps x,X and y,Y and fixes z; hence x,X,y,Y are
    # independent generic conjugates and the long-root parameter is fixed.
    R = PolynomialRing(ZZ,['x','X','y','Y','z'])
    x,X,y,Y,z = R.gens()
    m = Classical('D',4,R)
    short = lambda i,a,A:m.x(i+1,1,a)*m.x(i+1,-1,-A)
    long = lambda i,j,a:m.x(i+1,(j+1 if j>0 else j-1),a)
    checked('lemma4.short',m.comm(short(3,x,X),short(2,y,Y))
            == long(3,-2,x*Y+X*y))
    checked('lemma4.mixed',m.comm(long(3,2,z),short(2,y,Y))
            == short(3,z*y,z*Y)*long(3,-2,z*y*Y))


def unitary_example():
    """Example 1: fixed-group model and the obstruction to applying (3).

    The printed ell_d is only a map on root elements. Extending it to a
    chosen normal form on all UA4 is not justified. This bounded check
    does not assert automorphy of the product in the example.
    """
    from collections import deque
    F = GF(4,'a')
    m = Classical('A',5,F)
    J = matrix(F,5,lambda i,j:1 if i+j==4 else 0)
    star = lambda g:J*matrix(F,5,lambda i,j:g[i,j]**2).transpose()*J
    key = lambda g:tuple(g.list())
    generators = []
    seen = set()
    for r in m.order:
        if r in seen:
            continue
        e = m.roots[r]
        i,j,_ = m.pivots[r]
        a,b = m.indices[i],m.indices[j]
        rb = m.root(6-b,6-a)
        seen |= {r,rb}
        if r == rb:
            generators.append(m.X(r,F(1)))
        else:
            rr = tuple(x+y for x,y in zip(r,rb))
            for t in F:
                if not t:
                    continue
                base = m.X(r,t)*m.X(rb,t*t)
                candidates = [base*m.X(rr,z) for z in F] if rr in m.roots else [base]
                generators += [g for g in candidates if star(g)*g == m.I]
    generators = list({key(g):g for g in generators}.values())
    group = {key(m.I):m.I}
    queue = deque([m.I])
    while queue:
        g = queue.popleft()
        for h in generators:
            gh = g*h
            if key(gh) not in group:
                group[key(gh)] = gh
                queue.append(gh)
    checked('example1.group-order',len(group)==1024)
    for g in group.values():
        checked('example1.group-fixed',star(g)*g==m.I)
    for d in F:
        if d:
            checked('example1.eq3-hypothesis-fails',
                    any(d*(t*t-t)*(u*u-u) != 0 for t,u in product(F,repeat=2)))


if __name__ == '__main__':
    start = perf_counter()
    structure_checks()
    finite_maps()
    polynomial_maps()
    twist_refutation()
    twisted_d_checks()
    unitary_example()
    for name,count in sorted(COUNTS.items()):
        print(f'{name}: {count} passed')
    print(f'TOTAL: {sum(COUNTS.values())} exact assertions; {perf_counter()-start:.3f}s')
