from sage.all import *
"""Exact finite-field checks for Lemma 13 and the type 3D4 trace calculation.

This is evidence over the explicitly enumerated fields, not a proof of
the classification of large abelian or Thompson subgroups.
"""
import json

results = []
for q in [2, 3, 4, 5, 7, 8]:
    K = GF(q**3, name='z')
    el = list(K)
    sig = lambda t: t**q
    tr = lambda t: t + sig(t) + sig(sig(t))
    fixed = {t for t in el if sig(t) == t}
    plus = {t + sig(t) for t in el}
    minus = {t - sig(t) for t in el}
    trace = {tr(t) for t in el}
    kertrace = {t for t in el if tr(t) == 0}
    assert fixed == trace
    assert minus == kertrace
    assert {a+b for a in plus for b in fixed} == set(el)
    assert fixed.intersection(plus) == {2*t for t in fixed}
    kerplus = {t for t in el if t+sig(t) == 0}
    if K.characteristic() != 2:
        assert kerplus == {K(0)}
    else:
        assert kerplus == fixed
    # The expression is trilinear over the fixed field. Checking a spanning
    # set (here a prime-field basis, which also spans over the fixed field)
    # therefore covers all d,t,v for each K.
    z = K.gen()
    basis = [z**i for i in range(K.degree())]
    triples = 0
    for d in basis:
        transform = lambda t: sig(sig(d))*sig(t) + sig(d)*sig(sig(t))
        for t in basis:
            for v in basis:
                assert tr(t*transform(v)-transform(t)*v) == 0
                triples += 1
    # The cubic norm is onto the fixed field, including zero.
    norm = lambda t: t*sig(t)*sig(sig(t))
    assert {norm(t) for t in el} == fixed
    g = K.multiplicative_generator()
    assert norm(g).multiplicative_order() == q-1
    results.append({'q':int(q), 'order':int(K.order()), 'fixed':len(fixed),
                    'trace_kernel':len(kertrace), 'plus_kernel':len(kerplus),
                    'trace_bilinear_basis_triples':int(triples)})
    L = GF(q**2, name='w')
    fixed2 = {t for t in L if t**q == t}
    assert {t**(q+1) for t in L} == fixed2
    assert L.multiplicative_generator()**(q+1) in fixed2
print(json.dumps({'sage_version':version(), 'fields':results},indent=2))
