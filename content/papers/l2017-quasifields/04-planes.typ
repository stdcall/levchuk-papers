#import "../../main-defs.typ": source
#import "defs.typ": *
#import "types-diagram.typ": translation-types

=== Projective translation planes and its coordinatizing quasifields
<sec:l2017-quasifields-planes>

The constructions of quasifields and projective translation planes are closely
related. According to [@bib:l2017-quasifields-Hall1976,
@bib:l2017-quasifields-Hughes1973], the _projective plane_ is a set of points
and lines with an incidence relation between them such that:

- any two distinct points are incident with a unique line,
- any two distinct lines are incident with a unique point,
- there exist four points such that no three are incident with one line.

For every projective plane $pi$ a _dual plane_ $pi^d$ is determined. By
definition, its points are lines of $pi$ and its lines are points of $pi$ and,
also, the point and the line are incident in $pi^d$ if and only if they are
incident in $pi$.

The number $n$ is called an _order_ of finite plane, if some (equivalently,
every) its line is incident to $n+1$ points. Such plane consists of $n^2+n+1$
points and so many lines (see [@bib:l2017-quasifields-Hall1976, Theorem
20.1.1]).

By Bruck–Ryser theorem, there is no plane of order $n$, if $n$ cannot be
expressed as a sum of two integer squares and $n equiv 1$ or $2 (mod 4)$.

Bijective map of points and lines of projective plane $pi$, respectively, to
points and lines of projective plane $pi'$ is called an _isomorphism of planes_
(for $pi = pi'$, also _automorphism_ or _collineation_), if it preserves the
incidence relation. Any collineation of projective plane $pi$, that fixes the
line $l in pi$ pointwise and the point $P in pi$ linewise, is
_$(P,l)$-perspectivity_.

#metadata(none) <pass:l2017-quasifields-translation-plane>
If there exists a line $l in pi$ such that for any point $P in l$ the group of
$(P,l)$-perspectivities acts transitively on the affine points of each line
through $P$ distinct from $l$, then $pi$ is called a _translation plane_. If
dual plane $pi^d$ is translation plane too then $pi$ is a _semifield plane_.

Now we consider well-known coordinatization method of translation planes by
quasifields using “spread set”. Recall that the _group partition_ is a set of
its subgroups (components of partition), which have trivial pairwise
intersections and their set-theoretic union gives whole group.

Let $G$ be abelian group with partition $mu$. For corresponding affine plane the
points are the elements of $G$ and the lines are cosets on subgroups of $mu$
and, also, the incidence is set-theoretic. For construction of projective plane
we should define _singular_ (or _infinity_) point and line. We assume that the
cosets on the same subgroup intersect in the same singular point of this plane;
the set of all singular points gives a singular line.

A partition $mu$ of additive group of $2n$-dimensional linear space $V$ over the
field $F$ is called _spread_ in $V$, if $V = M ⊕ N$ for any distinct
$M,N in mu$. Then all components are $n$-dimensional subspaces, according to
[@bib:l2017-quasifields-Andre1954]. We get a projective translation plane
$mu(V)$ as above. Inversely: any translation plane is isomorphic to suitable
plane $mu(V)$.

To construct a translation plane $pi$ of rank $n$ over a field $F$ we can use
the $n$-dimensional linear space $W$ over $F$ (coordinatizing set), the outer
direct sum of two copies of $W$,

$V = W ⊕ W = {(x,y) | x,y in W}$, and the spread $mu$ with axes $V(0) := (W,0)$
and $V(infinity) := (0,W)$. Then the other components of $mu$ are

$ V(sigma) = {(v,v^sigma) | v in W}, quad sigma in GL(W). $

#source(5, printed: 692)

#metadata(none) <pass:l2017-quasifields-spread-map>
Let $theta$ be an injective map from linear space $W$ to ring $M(n,F)$ of all
$n times n$-matrices over $F$. The image $R = theta(W)$ is called a _spread
set_, if:

+ identity and zero matrices $E$ and $O$ are in $R$,
+ $R without {O}$ and the matrices $theta(u)-theta(v)$ are in $GL(n, F)$ for all
  $u,v in W$, $u != v$.

In this case we have a quasifield $(W,+,compose)$ with multiplication law

$ x compose y := x dot theta(y) quad (x = (x_1,x_2,dots,x_n), y in W). $

It is well known that projective translation plane is Desarguesian if and only
if its coordinatizing set is a skewfield (a field in finite case). According to
Theorem 6.1 [@bib:l2017-quasifields-Kallaher1982], an affine plane is
translation plane if and only if it is coordinatized by quasifield. In the case
of semifield it is a semifield plane.

The connection between translation planes and coordinatizing quasifields is
reflected by the following diagram of Lavrauw
[@bib:l2017-quasifields-Lavrauw2013], see Table~@tab:l2017-quasifields-types.

#figure(
  translation-types(),
  kind: table,
  caption: [Types of finite translation planes and their associated algebraic
    structures],
) <tab:l2017-quasifields-types>

#definition[
  The triple of bijective maps $alpha,beta,gamma$ of groupoid $(S;compose)$ on
  $(V;dot)$ is called _isotopism_ if $alpha(x compose y) = beta(x) dot gamma(y)$
  ($x,y in S$).
] <def:l2017-quasifields-isotopism>

The isotopism of quasifields $Q$ and $W$ (_autotopism_, if $Q = W$) is a triple
of isomorphisms $alpha,beta,gamma$ of additive group $(Q,+)$ to $(W,+)$, if its
restrictions to the loop $Q^*$ is an isotopism to $W^*$.

Right, middle and left nuclei $N_r,N_m$ and $N_l$ of semifield $S$ are the
invariants of isotopism:

$
  N_r lr((S)) = {k in S | x compose (y compose k) = (x compose y) compose k
    (x,y in S)},
$
$
  N_m lr((S)) = {k in S | x compose (k compose y) = (x compose k) compose y
    (x,y in S)},
$
$
  N_l lr((S)) = {k in S | k compose (x compose y) = (k compose x) compose y
    (x,y in S)}.
$

Kernel in quasifield $Q$ generalizes the left nucleus of semifield:

$
  K = {k in Q | k compose (x compose y) = (k compose x) compose y,
    k compose (x+y) = k compose x + k compose y quad (x,y in Q)}.
$

The kernel of quasifield is a skewfield, and the quasifield is a vector space
over kernel. It is easy to show that any finite quasifield can be determined as
a vector space over prime subfield.

#lemma[
  Let $chevron.l Q,+,dot chevron.r$ be a quasifield of order $p^n$, $W$ be
  $n$-dimensional linear space over $ZZ_p$. Then there exists such a spread set

  $ R = {theta(w) | w in W} subset GL_n lr((p)) union {0}, $

  that $chevron.l Q,+,dot chevron.r$ is isomorphic to
  $chevron.l W,+,ast chevron.r$, where $x ast y = x theta(y)$, $x,y in W$.
] <lem:l2017-quasifields-spread-representation>
