#import "defs.typ": *
=== Elementary equivalence <sec:l2009-model-elementary-equivalence>
Consider $R=NT lr((n,K))$ and $R'=NT lr((n,S))$ for $n>=3$. The theory of the
Lie ring $Lambda lr((R))$ and, similarly, of the Jordan ring $J lr((R))$ is
hereditarily unsolvable if and only if so is the theory $Th lr((K))$ of the base
ring. Moreover, the following theorem is valid. #theorem[
  An associative ring $K$ with identity can be interpreted into the rings
  $Lambda lr((R))$ and $J lr((R))$ with parameters.
] <th:l2009-model-coefficient-interpretation>

In constructing an interpretation of the coefficient ring into the unitriangular
group $UT lr((n,K))$ with parameters, Belegradek showed that, for a suitable
associative ring $K$, these parameters are undefinable in the group
$UT lr((n,K))$ for $n>=3$, but the commutative coefficient ring can be
interpreted into the unitriangular group without parameters
[@bib:l2009-model-Belegradek1999, Propositions 1.23.5 and 1.23.6]. The cases of
a commutative and a noncommutative coefficient ring for associated Lie and
Jordan rings differ substantially as well. In particular, _if $K$ is an
associative commutative ring, then the theories $Th lr((K))$ and
$Th lr((J lr((R))))$ (and, similarly, the theories $Th lr((K))$ and
$Th lr((Lambda lr((R)))))$ are recursively isomorphic._

The following theorem reveals a relationship between the elementary equivalence
of the associated rings with the elementary properties of the base rings.
#theorem[
  Suppose that either $n>4$ or $K$ is a commutative ring and $n=3,4$.

  Then, each of the elementary equivalences
  $
    J lr((R)) equiv J lr((R')), quad
    Lambda lr((R)) equiv Lambda lr((R')), quad
    UT lr((n,K)) equiv UT lr((n,S))
  $
  is equivalent to the existence of central idempotents $f$ in $K$ and $g$ in
  $S$ for which $f K equiv g S$ and $(1-f)K equiv lr([(1-g)S])^Sop$.
  #ed-note[
    The argument gives central idempotents in ultrapowers. Their descent to the
    original rings with elementarily equivalent components is not justified. The
    sufficient implication is unaffected. Compare Theorem
    @th:l2008-model-elementary-equivalence and its proof.
  ]
] <th:l2009-model-elementary-equivalence>

The key point is the passage from an elementary equivalence to an isomorphism of
the corresponding systems and, next, the application of the main theorem from
[@bib:l2009-model-KuzucuogluLevchuk2004] and Theorem
@th:l2009-model-standard-jordan-isomorphisms from Section
@sec:l2009-model-isomorphisms. The apparatus of ultraproducts (see
[@bib:l2009-model-ChangKeisler1973] and the 1993 monograph by W.~Hodges) is also
essentially used. According to the isomorphism theorem
[@bib:l2009-model-ChangKeisler1973, Theorem 6.1.15], _algebraic systems
$frak(A)$ and $frak(B)$ are elementarily equivalent if and only if some of their
ultrapowers are isomorphic._

The passage $UT lr((n,K))^I slash D ≃ UT lr((n,K^I slash D))$ from the
ultrapower of the unitriangular group to the ultrapower $K^I slash D$, which was
constructed by Belegradek [@bib:l2009-model-Belegradek1999] in the proof of
Proposition 2.2.8, remains valid for a noncommutative ring $K$. For the Lie and
Jordan rings, the following assertion is also valid. #lemma[
  For any associative ring $K$ with unity and any ultrafilter $(D,I)$, there
  exist isomorphisms
  $
    Lambda lr((NT lr((n,K))))^I slash D
    ≃ Lambda lr((NT lr((n,K^I slash D)))),
  $
  $
    J lr((NT lr((n,K))))^I slash D ≃ J lr((NT lr((n,K^I slash D)))).
  $
] <lem:l2009-model-lie-jordan-ultrapower>

In [@bib:l2009-model-KuzucuogluLevchuk2004] and in Theorem
@th:l2009-model-standard-jordan-isomorphisms, nontrivial idempotent-ring
isomorphisms of unitriangular groups and of the associated Lie and Jordan rings
are related to the direct decompositions of these algebraic systems
corresponding to the direct Pierce decompositions of the coefficient rings. On
the other hand, the elementary equivalence of algebraic systems can be
transferred to their direct products [@bib:l2009-model-ChangKeisler1973, Theorem
6.3.4]. To complete the proof of Theorem @th:l2009-model-elementary-equivalence,
it remains to note that the elementary equivalence of coefficient rings can be
easily transferred to unitriangular groups of the same degree and to the
associated Lie and Jordan rings.
