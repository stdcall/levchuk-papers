#import "defs.typ": *
=== Derivations <sec:l2009-model-derivations>
We denote the additive group of derivations of an arbitrary ring $R$ by $Der R$.
An endomorphism $zeta$ of the additive group $R^+$ of a ring $R$ is called a
derivation if $zeta lr((a b))=zeta lr((a))b+a zeta lr((b))$ for $a,b in R$. The
Lie ring $Lambda lr((R))$ under Lie multiplication
$alpha * beta=alpha beta-beta alpha$ and the Jordan ring $J lr((R))$ under
multiplication $alpha compose beta=alpha beta+beta alpha$ are associated with
the associative ring $R$. For any $gamma in R$, we obtain the inner derivation
$x arrow x * gamma$ of such a ring.

The relationship between ring derivations and endomorphisms is revealed in the
following lemma. #lemma[
  An endomorphism $zeta$ of the additive group $R^+$ satisfying the condition
  $zeta lr((R))^2=0$ is a derivation in the ring $R$ if and only if
  $1+zeta: x arrow x+zeta lr((x))$ is an endomorphism of $R$.
] <lem:l2009-model-square-zero-derivation>

We denote the first and last elements of a chain $Gamma$ (if they exist) by $p$
and $q$, respectively. Let $K$ be an associative ring with identity, and let
$R=NT lr((Gamma,K))$. The mapping $x arrow x * gamma$ for a triangular
$Gamma$-matrix $gamma=lr(‖gamma_(i j)‖)$ ($gamma_(i j)=0$ if $i<j$) over $K$ is
a derivation in the ring $R$ if and only if the images of the $Gamma$-matrix
units $e_(i j)$ are finitary or, equivalently, each row with number $!=q$ and
each column with number $!=p$ in $gamma$ contain finitely many nonzero elements.
If, in addition, there exists a similar $Gamma$-matrix $gamma'$ satisfying the
condition $gamma gamma'=gamma' gamma=e$ modulo the center of the ring $R$, then
the mapping $alpha arrow gamma alpha gamma'$ (where $alpha in R$) is an
automorphism of $R$; if the principal diagonal in $gamma$ is unit, then this
automorphism is locally inner. We say that the automorphisms and derivations
constructed above are triangular, and those constructed for diagonal
$Gamma$-matrices $gamma$ are diagonal.

An isomorphism or a derivation $theta$ of the ring $K$ induces, respectively, an
isomorphism or a derivation of the ring $R$:
$
  overline(theta): lr(‖a_(i j)‖) arrow lr(‖theta lr((a_(i j)))‖)
  quad (lr(‖a_(i j)‖) in NT lr((Gamma,K))).
$
An automorphism (or a derivation) of a ring is called hypercentral of height
$m$, or central (for $m=1$), if
#source(2, printed: 186)
it is the identity (respectively, identically zero) modulo the $m$th hypercenter
and such $m$ is minimal, even up to multiplication by an inner automorphism
(respectively, a derivation).

#theorem[
  The group $Der NT lr((Gamma,K))$ for $|Gamma|>2$ is the sum of
  $overline(Der) K$ and the subgroups of triangular and central derivations.
] <th:l2009-model-associative-derivations>
It follows from this theorem that the _uaz_-derivations introduced in
[@bib:l2009-model-ChunPark2006] in order to describe $Der NT lr((n,K))$ reduce
to central derivations.

The $Gamma$-matrices $x e_(i j)$ (where $x in K$, $i,j in Gamma$, and $i>j$)
under ordinary addition and multiplication additively generate the ring
$NT lr((Gamma,K))$. We set $[i,j]={k in Gamma | i<=k<=j}$. We write
$j triangle.stroked.l i$ if $i$ is the first element of the subset
${k in Gamma | k>j}$. The hypercenters are described by the following lemma.
#lemma[
  The center of the ring $R=NT lr((Gamma,K))$ coincides with the annihilator and
  is nonzero only for $p,q in Gamma$. If $p,q in Gamma$, then in the ring $R$
  and the associated Lie and Jordan rings, the $m$th hypercenters are
  $
    HC_m lr((R))=lr(
      〈K e_(i j) | j<i,
      |[p,j]|+|[i,q]|<=m+1〉
    ).
  $
  If either endpoint is absent, all finite hypercenters are zero.
] <lem:l2009-model-hypercenters>

Derivations in a ring are trivial Lie and Jordan derivations, and isomorphisms
and anti-isomorphisms between rings are trivial Jordan isomorphisms. According
to classical theorems of Herstein [@bib:l2009-model-Herstein1956,
@bib:l2009-model-Herstein1957], Jordan isomorphisms and derivations of a prime
ring of characteristic $!=2$ are trivial. Martindale~III, Baxter, and Brešar
transferred Herstein’s theorems to semiprime rings and Wong and Zhang
transferred them to the rings $NT lr((n,K))$ and close rings and algebras over
commutative rings (see [@bib:l2009-model-Wang2007] and the references therein).
Lie derivations in the algebra $NT lr((n,K))$ were considered in
[@bib:l2009-model-OuWangYao2007]. For $R'=NT lr((Omega,S))$, V.~M. Levchuk
together with Kuzucuoglu proved the following theorem. #theorem[
  If $K$ is a ring without zero divisors and $|Gamma|>2$, then any Jordan
  isomorphism of the ring $R$ to $R'$ is trivial modulo $HC_3 lr((R))$. A
  nontrivial Jordan isomorphism exists if and only if
  $HC_1 lr((R)) != HC_2 lr((R))$, $K$ is an integral domain, and $2K=0$.
] <th:l2009-model-jordan-isomorphisms-domain>

Herstein’s derivation theorem [@bib:l2009-model-Herstein1957] has the following
analogue. #theorem[
  Any Lie or Jordan derivation of the ring $R=NT lr((Gamma,K))$ is trivial
  modulo $HC_3 lr((R))$. A nontrivial Lie (or Jordan) derivation exists if and
  only if $HC_1 lr((R)) != HC_2 lr((R))$ and either there exists an
  $i triangle.stroked.l q$ and the right annihilator of $K*K$ (respectively, of
  $K compose K$) in $K$ is nonzero or $p triangle.stroked.l i$ and the left
  annihilator is nonzero.
] <th:l2009-model-lie-jordan-derivations>

To describe $Der Lambda lr((R))$ and $Der J lr((R))$, we find the Lie and Jordan
hypercentral derivations of height $>1$ in the ring $R$. For $p,q in Gamma$ and
$a,c in K$, consider the endomorphisms of the additive group $R^+$ defined by
$
  sigma_a: x e_(i p) arrow a x e_(q i), quad p triangle.stroked.l i<q,
  quad sigma'_c: x e_(q j) arrow x c e_(j p), quad p<j triangle.stroked.l q,
$
$
  delta_a: x e_(i p) arrow a x e_(q m), quad
  x e_(m p) arrow a x e_(q i), quad
  p triangle.stroked.l i triangle.stroked.l m<q,
$
$
  delta'_c: x e_(q j) arrow x c e_(h p), quad
  x e_(q h) arrow x c e_(j p), quad
  p<h triangle.stroked.l j triangle.stroked.l q,
  quad x in K
$
(the images of the remaining generating elements $x e_(u v)$ are set to zero).
We denote the left and right annihilators of a subset $M$ in the ring $K$ by
$Ann_K^((l)) lr((M))$ and $Ann_K^((r)) lr((M))$, respectively. We set
$
  DD_3=lr(〈delta_a | a in Ann_K^((l)) lr((K compose K))〉), quad
  DD'_3=lr(〈delta'_c | c in Ann_K^((r)) lr((K compose K))〉);
$
$
  DD_2=lr(〈sigma_a | a in Ann_K^((l)) lr((K compose K))〉), quad
  DD'_2=lr(〈sigma'_c | c in Ann_K^((r)) lr((K compose K))〉);
$
$
  tilde(DD)_2=lr(〈sigma_b | b in Ann_K^((l)) lr((K*K))〉), quad
  tilde(DD)'_2=lr(〈sigma'_d | d in Ann_K^((r)) lr((K*K))〉).
$
#theorem[
  Suppose that $K$ is an associative ring with identity, $Gamma$ is a chain, and
  $R=NT lr((Gamma,K))$. Then,
  $
    Der J lr((R))=cases(
      DD_2+DD'_2+DD_3+DD'_3+Der R & |Gamma|>3,
      DD_2+DD'_2+Der R & |Gamma|=3,
    ) ";"
  $
  $
    Der Lambda lr((R))=cases(
      tilde(DD)_2+tilde(DD)'_2+DD_3+DD'_3+Der R & |Gamma|>3,
      tilde(DD)_2+tilde(DD)'_2+Der R & |Gamma|=3,
    ) "."
  $
] <th:l2009-model-derivation-decomposition>
Special cases of Theorem @th:l2009-model-derivation-decomposition were proved by
Kuzucuoglu and Radchenko.
