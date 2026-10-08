#import "defs.typ": *
=== Isomorphisms <sec:l2009-model-isomorphisms>
Isomorphisms of a ring $K$ and a chain $Gamma$ induce isomorphisms of the ring
$R=NT lr((Gamma,K))$. The anti-isomorphisms $tilde: K arrow S$ of rings and
$prime: Gamma arrow Omega$ of chains determine the anti-isomorphism of the ring
$R$ defined by
$
  R arrow NT lr((Omega,S))=R',
  quad alpha=lr(‖a_(i j)‖) arrow tilde(alpha)' := lr(‖tilde(a)_(j' i')‖),
  quad alpha in R.
$
Let $R^Sop$ denote the ring opposite to $R$. As in
[@bib:l2009-model-Levchuk1983, @bib:l2009-model-KuzucuogluLevchuk2004], it can
be shown that any hypercentral Jordan automorphism of height $<=3$ of the ring
$R$ for $|Gamma|>4$ is the product of an inner and a central automorphism and
the automorphism $1+chi$, where $chi=delta_a$, $delta'_c$, $sigma_b$, or
$sigma'_d$ is a Jordan derivation.

Let $f$ be a central idempotent in the ring $K$. An isomorphism
$theta: K^+ arrow S^+$ of additive groups satisfying the condition
$theta lr((1_K))=1_S$ is called an $f$-isomorphism, or an idempotent isomorphism
of the ring $K$, if it induces an isomorphism of the ideal $f K$ and an
anti-isomorphism of the ideal $(1_K-f)K$. Rings connected by an idempotent
isomorphism are said to be idempotent-isomorphic.
#source(3, printed: 187)
When $Gamma=Omega$ and $prime$ is an anti-automorphism of the chain $Gamma$, we
obtain an extension to the Jordan idempotent isomorphism
$
  R arrow R', quad alpha arrow theta lr((f alpha))
  +theta lr([(1-f)alpha']), quad alpha in R.
$ <eq:l2009-model-jordan-idempotent-map>
Products of idempotent ring isomorphisms and chain ones, hypercentral
isomorphisms of height $<=3$, and triangular automorphisms give standard Jordan
isomorphisms.

All chains of order $n$ are isomorphic to the chain ${1,2,dots,n}$ with a unique
automorphism (the identity) and the unique anti-automorphism $k arrow n+1-k$.
Obviously, isomorphisms and elementary equivalences preserve the nilpotency
class of groups and rings; this recovers the matrix degree when the coefficient
rings are nonzero. The following theorem describes Jordan isomorphisms of the
ring $R=NT lr((n,K))$ onto $R'=NT lr((n,S))$ with $n>4$. #theorem[
  The rings $J lr((R))$ and $J lr((R'))$ with $n>4$ are isomorphic if and only
  if the rings $K$ and $S$ are idempotent-isomorphic; any isomorphism between
  them is standard.
] <th:l2009-model-standard-jordan-isomorphisms>

To describe isomorphisms and derivations, we first study the images of the
ideals $N_(i j)=lr(〈K e_(u v) | v<=j, u>=i, v<u〉)$ for $i,j in Gamma$. We
prove their invariance with respect to Jordan isomorphisms up to multiplication
by idempotent and hypercentral isomorphisms. The ideals $N_(i j)$ are
$(Der R)$-invariant, and their invariance with respect to Lie and Jordan
derivations holds up to addition of hypercentral (with height $<=3$)
derivations.

Isomorphisms have also been described for $n=4$ and, in the case of the
commutative coefficient ring $K$, for $n=3$. The exceptionality of the degrees
$<=4$ in Theorem @th:l2009-model-standard-jordan-isomorphisms manifests itself
as in the descriptions of the isomorphisms of the Lie rings $Lambda lr((R))$ and
unitriangular groups given in [@bib:l2009-model-Levchuk1983,
@bib:l2009-model-KuzucuogluLevchuk2004].

#remark[
  Videla’s theorem [@bib:l2009-model-Videla1988] on the elementary equivalence
  $NT lr((m,S)) equiv NT lr((n,K))$ and the theorem from
  [@bib:l2009-model-KuzucuogluLevchuk2004] about isomorphisms
  $NT lr((m,S)) ≃ NT lr((n,K))$ were proved under the assumption that the
  coefficient rings are associative rings with identity. According to
  [@bib:l2009-model-Minakova2008], these theorems remain valid if only one of
  the coefficient rings is associative. The following question of Belegradek
  [@bib:l2009-model-Belegradek1999] remains open: Does there exist an
  isomorphism $UT lr((3,K)) ≃ UT lr((3,S))$ for associative and nonassociative
  coefficient rings?
] <rem:l2009-model-nonassociative-coefficients>
