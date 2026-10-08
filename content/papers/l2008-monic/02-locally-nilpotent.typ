#import "../../main-defs.typ": *
#import "defs.typ": *

=== Automorphisms of Locally Nilpotent Rings and Groups
<sec:l2008-monic-locally-nilpotent>

Firstly, we consider standard automorphisms of certain locally nilpotent rings
and groups. Recall that a Lie ring $Lambda(R) := (R,+,ast)$ with the Lie product
$alpha ast beta = alpha beta - beta alpha$ and, also, a Jordan ring
$J(R) := (R,+,compose)$ with the Jordan product
$alpha compose beta = alpha beta + beta alpha$ are associated to every
associative ring $R$. The map $x arrow.r 1+x$ of any radical ring $R$ is an
isomorphism of the adjoint group $G(R)$. For the automorphism groups it isn’t
difficult to verify the following equalities:

$ Aut R = Aut G(R) inter Aut J(R) = Aut G(R) inter Aut Lambda(R). $

Usually all automorphisms of $R$ are considered as standard automorphisms for
the adjoint group and associated rings. Every inner automorphism of the adjoint
group gives an inner automorphism of the ring $R$.

By [@bib:l2008-monic-Levchuk1992], an automorphism of a ring or group is called
_hypercentral of height $m$_ (or _central_ for $m <= 1$), if it acts like the
identity, modulo the m-th hypercenter and even up to multiplication by inner
automorphisms such $m$ is the least.

Let $K$ be an associative ring with identity. Choose a chain (or linearly
ordered set) $Gamma$ by an order relation $<=$. A niltriangular $Gamma$-matrix
$‖a_(i j)‖_(i,j in Gamma)$, $a_(u v) = 0$, $u <= v$, over $K$ is said to be
_finitary_, if it has a finite number of nonzero elements. The ring
$NT(Gamma, K)$ (or $NT(n, K)$ at $Gamma = {1,2,dots,n}$) of all such
$Gamma$-matrices with the usual matrix addition and multiplication is locally
nilpotent and hence radical. The adjoint group of the ring $NT(Gamma, K)$ for a
finite chain $Gamma$ is isomorphic to the unitriangular group $UT(|Gamma|, K)$.

Set $R = NT(Gamma, K)$. Let $e_(i j)$ be the $Gamma$-matrix unit. Evidently, the
elementary $Gamma$-matrices $x e_(i j)$ ($x in K$, $i > j$) generate the
additive and adjoint groups of the ring $R$. When a chain $Gamma$ is dense, we
may always choose $k in Gamma$ such that $j < k < i$ and hence
$e_(i j) = e_(i k) e_(k j)$. Thus $R = R^2$ and therefore the monic condition
places no restriction on automorphisms of the ring $R$ or the associated ring.
Also, see [@bib:l2008-monic-Levchuk1987], [@bib:l2008-monic-Merzlyakov1995].

#source(3, printed: 382) We now consider the center and certain hypercentral
series. Denote by $p$ and $q$, respectively, the first and the last elements of
$Gamma$ (if they exist), by $[i,j]$, the segment ${k in Gamma | i <= k <= j}$ of
$Gamma$.

#lemma[Assume $K != 0$ and $|Gamma| >= 2$. The center (and the annihilator) of
  the ring $R = NT(Gamma, K)$ is nonzero if and only if $p,q in Gamma$. The m-th
  hypercenter $Z_m lr((R))$ of $R$ coincides with
  $〈K e_(i j) | j < i, |[p,j]| + |[i,q]| <= m+1〉$. Also, it coincides with the
  m-th hypercenter of the associated Jordan and Lie rings and of the adjoint
  group.]
<lem:l2008-monic-hypercenters>

#proof[We obtain the statements of the lemma directly, by using the main
  relations between elementary $Gamma$-matrices. For the adjoint group $G(R)$
  and for the rings $R,Lambda(R)$ see also [@bib:l2008-monic-Levchuk1983],
  [@bib:l2008-monic-Levchuk1987].]

Evidently, every isomorphism $theta$ of the coefficient ring $K$ induces a ring
isomorphism $‖a_(i j)‖ arrow.r ‖theta(a_(i j))‖$ of the ring $R$. Analogously,
every isomorphism (or isometry) of the chain $Gamma$ induces a chain isomorphism
of $R$.

Since the ring $R$ is locally nilpotent,
$e+beta+beta^2+dots = (e-beta)^(-1) in e+R$ for any $beta in R$ and the identity
$Gamma$-matrix $e$. It gives an inner automorphism
$alpha arrow.r (e-beta) alpha (e-beta)^(-1)$ ($alpha in R$) of the ring $R$.
Consider a generalization. Choose an arbitrary (lower) triangular $Gamma$-matrix
$gamma = ‖gamma_(i j)‖$ (with $gamma_(i j) = 0$ for $i < j$) over $K$ in which
every row with a number $!= q$ and every column with a number $!= p$ have only
finitely many nonzero elements. If there exists a similar $Gamma$-matrix
$gamma'$ satisfying the equalities $gamma gamma' = gamma' gamma
= e$ modulo the center of $R$, then the map $alpha arrow.r gamma alpha gamma'$
($alpha in R$) is an automorphism, which is called a _triangular_ (or _locally
inner_, if the main diagonal of $gamma$ consists of ones, or _diagonal_ for a
diagonal $Gamma$-matrix $gamma$), automorphism of the ring $R$,
[@bib:l2008-monic-Levchuk1987]. By [@bib:l2008-monic-Levchuk1983,
Theorem~@th:l1983-main-automorphisms] and [@bib:l2008-monic-Levchuk1987,
Theorem~@th:l1987-rings-automorphisms], we have:

_If $Gamma$ is a finite chain of order $>= 3$ or $K$ has no zero-divisors, then
every automorphism of the ring $R = NT(Gamma, K)$ is a product of induced ring
and chain automorphisms, triangular and central automorphisms._

When either $Gamma$ and $K$ satisfy the same restrictions and $|Gamma| > 4$ or
$|Gamma| = 3,4$ and $K$ is a commutative ring, the automorphism groups of the
Lie ring $Lambda(R)$ and of the adjoint group $G(R)$ also have been described in
[@bib:l2008-monic-Levchuk1983], [@bib:l2008-monic-Levchuk1987]. Consider the
Jordan automorphisms of the ring $R$, i.e., automorphisms of the Jordan ring
$J(R)$.

By Herstein’s classical theorem [@bib:l2008-monic-Herstein1956], _every Jordan
isomorphism between prime rings of characteristic not 2 is an isomorphism or an
anti-isomorphism_. The usual goal is to describe all Jordan automorphisms and
isomorphisms. The special case has been investigated by X. Wang
[@bib:l2008-monic-Wang2007] etc.: _every Jordan automorphism of the algebra
$NT(n, K)$ over a 2-torsion free commutative ring $K$ with no idempotents except
0 and 1 is an automorphism or an anti-automorphism_.

In the general case we may construct non-trivial Jordan isomorphisms of the ring
$R = NT(Gamma, K)$ by analogy with idempotent isomorphisms of $Lambda(R)$ and
$G(R)$. Let $S$ be a ring and $f$ be a central idempotent of the ring $K$. An
isomorphism $theta: K^+ arrow.r S^+$ of the additive groups is called an
_idempotent isomorphism_ of the ring $K$, if it induces an isomorphism of the
ideal $f K$ and an anti-isomorphism of the ideal $(1-f)K$ and also
$theta(1_K) = 1_S$, [@bib:l2008-monic-Levchuk1983]. If $prime$ is an
anti-automorphism of the chain $Gamma$, we obtain an induced idempotent Jordan
isomorphism of $R$:

$
  alpha arrow.r theta(f alpha) + theta[(1-f)alpha']
  quad (alpha = ‖alpha_(i j)‖ in R, alpha'_(i j) = alpha_(j' i')).
$

Jordan automorphisms of the ring $R = NT(Gamma, K)$ can be described by analogy
with $Aut Lambda(R)$ and $Aut G(R)$ in [@bib:l2008-monic-Levchuk1983],
[@bib:l2008-monic-Levchuk1987] (see also [@bib:l2008-monic-Levchuk2008Jordan]).
A Jordan automorphism of $R$ is called _standard_, if it is a product of an
automorphism of $R$ and an idempotent automorphism of $J(R)$. The following
theorem holds.

#theorem[#source(4, printed: 383) Let $R = NT(Gamma, K)$, $|Gamma| > 4$. If
  $Gamma$ is a finite chain or $K$ is a ring without zero-divisors, then every
  automorphism of the Jordan ring $J(R)$ (analogously, of $Lambda(R)$ or $G(R)$)
  is a product of some standard and hypercentral of height $<= 3$ automorphisms
  of $J(R)$.]
<th:l2008-monic-jordan-automorphisms>

Note that automorphisms are also described in the exceptional cases
$|Gamma| = 3,4$, in particular, for any commutative ring of coefficients.

#example[We now show that there exist non-standard Jordan hypercentral
  automorphisms of $R$. Let $p,q in Gamma$ and let there exist the direct
  successor $k$ of $p$ (i.e., the first element of the subset
  ${j in Gamma | p < j}$) and the direct successor $m$ of $k$ in $Gamma$. Choose
  an element $c in K$ with $c(K compose K) = 0$; this is equivalent to the
  restrictions $2c = 0$ and $c(K ast K) = 0$. Then the map
  $x e_(k p) arrow.r (e_(k p)+c e_(q k))x$, $x in K$ (other elementary matrices
  $x e_(u v)$ are fixed) and, analogously, the map

  $
    x e_(k p) arrow.r (e_(k p)+c e_(q m))x,
    quad x e_(m p) arrow.r (e_(m p)+c e_(q k))x quad (x in K)
  $

  determine automorphisms of the Jordan ring $R$. Such automorphisms together
  with symmetrical ones generate all Jordan hypercentral automorphisms up to
  multiplication by inner and central automorphisms.]
<exm:l2008-monic-jordan-shears>

Recall that the adjoint group of the ring $NT(n, K)$ is isomorphic to the
unitriangular group $UT(n, K)$ which is also isomorphic to the unipotent
subgroup $U G(K)$ of the Chevalley group of Lie type $G = A_(n-1)$. The
well-known question about automorphisms of all unipotent subgroups over finite
fields [@bib:l2008-monic-Kondratyev1986, Problem (1.5)] has been solved in the
90s. In the general case the following theorem has been proved (see
[@bib:l2008-monic-Levchuk1992]).

#theorem[Every automorphism of the unipotent subgroup $U G(K)$ of Lie rank
  $>= 3$ over an arbitrary field $K$ is a product of some standard and
  hypercentral of height $<= 5$ automorphisms.]
<th:l2008-monic-unipotent-automorphisms>

For the unipotent group of the classical types
$G = B_n,C_n,D_n,twisted(2, A_n),twisted(2, D_n)$ finitary generalizations of
the types

$ B_Gamma, C_Gamma, D_Gamma, twisted(2, A_Gamma), twisted(2, D_Gamma), $
<eq:l2008-monic-finitary-types>

respectively, with an arbitrary chain $Gamma$ have been investigated, see
[@bib:l2008-monic-Levchuk1992], [@bib:l2008-monic-LevchukSuleimanova2008] etc.

#hypothesis[Does Theorem~@th:l2008-monic-unipotent-automorphisms hold for the
  finitary unipotent group $U G(K)$ of types @eq:l2008-monic-finitary-types with
  any infinite chain $Gamma$?]

In [@bib:l2008-monic-Levchuk1987, Theorem~@th:l1987-rings-automorphisms] the
corresponding Lie-ring and group cases are proved for an infinite chain $Gamma$
by using the description of maximal abelian ideals of associated rings. There
exist close structural connections of normal subgroups of $U G(K)$ and ideals of
the associated Lie ring. The normal structure and maximal abelian normal
subgroups of $U G(K)$ are described in a uniform form by V. Levchuk and G.
Suleimanova [@bib:l2008-monic-LevchukSuleimanova2008]. Also, the last
description allows one to find the large (or the highest order) abelian
subgroups of $U G(K)$ over finite fields in explicit form, see A. S.
Kondratyev’s question [@bib:l2008-monic-Kondratyev1986, Problem (1.6)]. We
obtain all large abelian normal subgroups of $U G(K)$ directly from
[@bib:l2008-monic-LevchukSuleimanova2008]. As it was recently shown by G.
Suleimanova, there exist large abelian subgroups of some groups $U G(K)$ which
are not conjugated in the Chevalley group $G(K)$ with a normal subgroup of
$U G(K)$. Therefore it is natural to investigate the question of description of
all such exceptional cases.
<pass:l2008-monic-exceptional-large-question>
