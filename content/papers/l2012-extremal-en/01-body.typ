#import "../../collection.typ": paper-abstract, paper-keywords
#import "../../main-defs.typ": *
#import "defs.typ": *
#import "diagrams/coxeter.typ": coxeter-rows

#source(1, printed: 98)

#paper-abstract(language: "en")[
  We describe all maximal abelian normal subgroups in the unipotent radical $U$
  of a Borel subgroup in a group of Lie type $G$ over a field $K$. This gives a
  new description of the extremal subgroups in $U$ which were studied by C.
  Parker and P. Rowley. For a finite field $K$, we prove that either each large
  abelian subgroup in $U$ is $G$-conjugate to a normal subgroup in $U$ or $G$ is
  of certain exceptional Lie type.
]

#paper-keywords(language: "en")[
  Group of Lie type; Unipotent subgroup; Maximal abelian normal subgroup;
  Extremal subgroup; Large abelian subgroup.
]

#heading(level: 3, numbering: none)[Introduction]
<sec:l2012-extremal-en-introduction>

Let $G$ be a group of Lie type over a field $K$, and let $U$ be the unipotent
radical of a Borel subgroup in $G$. The present paper is devoted to studying
certain abelian normal subgroups in $U$ and some related problems.

The study of these questions has been under active investigation since 1970s. J.
Gibbs [@bib:l2012-extremal-en-Gibbs1970] described the lower and upper central
series, the characteristic subgroups and the automorphisms of $U$ with
$char K != 2, 3$. A description for an arbitrary field $K$ was completed in
[@bib:l2012-extremal-en-Levchuk1990], and it solves the problem (1.5) from
[@bib:l2012-extremal-en-Kondratyev1986]. The approach of
[@bib:l2012-extremal-en-Levchuk1990] uses a description of maximal abelian
normal subgroups of the unitriangular group and close structural connections of
$U$ and its associated Lie ring, cf. [@bib:l2012-extremal-en-Levchuk1976,
@bib:l2012-extremal-en-Levchuk1992, @bib:l2012-extremal-en-Kuzucuoglu2001,
@bib:l2012-extremal-en-Kuzucuoglu2004, @bib:l2012-extremal-en-Levchuk2009].

The theorems announced in [@bib:l2012-extremal-en-Levchuk2008] and Theorems
@th:l2012-extremal-en-frame-normal and @th:l2012-extremal-en-classical-normal
about the normal structure use the concept of corners of subsets in $U$ (for
notation see Section @sec:l2012-extremal-en-preliminaries). Thus, the _extremal
subgroups_ from [@bib:l2012-extremal-en-Parker1997] #source(2, printed: 99) are
the normal abelian subgroups in $U$ with a simple corner. For the application to
symplectic amalgams [@bib:l2012-extremal-en-Parker2002] and the revision of the
classification of finite simple groups, C. Parker and P. Rowley studied the
groups $U$ with an extremal subgroup and the possible simple corners of such a
subgroup [@bib:l2012-extremal-en-Parker1997–@bib:l2012-extremal-en-Parker2003].

Theorems @th:l2012-extremal-en-rank-two-maximal,
@th:l2012-extremal-en-abelian-normal and @th:l2012-extremal-en-f4-e6-maximal of
the present paper and [@bib:l2012-extremal-en-Levchuk2008, Theorem 5] (for the
classical types) describe all maximal abelian normal subgroups in $U$.
Therefore, we have a new solution to the Parker–Rowley problem. Theorem
@th:l2012-extremal-en-parker-rowley gives a clarification of some assertions
from [@bib:l2012-extremal-en-Parker1997, @bib:l2012-extremal-en-Parker1998] when
$U$ is of type $D_4$ and $twisted(2, D_4)$.

In Section @sec:l2012-extremal-en-large-subgroups we consider an application to
description of the large abelian and normal large abelian subgroups in the
finite groups $U$. For the exceptional types, this problem was pointed out in A.
S. Kondratiev’s survey [@bib:l2012-extremal-en-Kondratyev1986, Problem (1.6)]
(for the classical types, see [@bib:l2012-extremal-en-Barry1979,
@bib:l2012-extremal-en-Barry1982, @bib:l2012-extremal-en-Wong1982Orthogonal,
@bib:l2012-extremal-en-Wong1982Unitary]). Using a computer approach as well as a
generalization of A. I. Mal’tsev’s method [@bib:l2012-extremal-en-Malcev1945],
E. P. Vdovin [@bib:l2012-extremal-en-Vdovin2001, Table 4] determined the orders
of large abelian subgroups of $U$.

Given a group-theoretic property $cal(P)$, we recall that every
$cal(P)$-subgroup of largest order in a finite group is a _large
$cal(P)$-subgroup_. Theorem @th:l2012-extremal-en-large-normal-abelian and
[@bib:l2012-extremal-en-Levchuk2009, Table 2] (for the classical types) give the
list of all large normal abelian subgroups in the finite groups $U$. Using the
approach of [@bib:l2012-extremal-en-Malcev1945] and
[@bib:l2012-extremal-en-Vdovin2001] we show that the identical list gives the
normal large abelian subgroups (Theorem
@th:l2012-extremal-en-normal-large-order). (In general, there exists a large
normal $cal(P)$-subgroup, which is not a large $cal(P)$-subgroup, cf. Section
@sec:l2012-extremal-en-large-subgroups.) It allows us to clarify some orders of
large abelian subgroups in $U$ which were found in
[@bib:l2012-extremal-en-Vdovin2001, Table 4], cf. Remark in Section
@sec:l2012-extremal-en-large-subgroups.

Finally, in Section @sec:l2012-extremal-en-large-subgroups we show that either
each large abelian subgroup in $U$ is $G$-conjugate to a normal subgroup in $U$
or $G$ is of certain exceptional type and there exists a normal large abelian
subgroup in $U$ which is not extremal.

=== Preliminary remarks and notation <sec:l2012-extremal-en-preliminaries>

Along with the usual notation of [@bib:l2012-extremal-en-Serre1966,
@bib:l2012-extremal-en-Carter1972, @bib:l2012-extremal-en-Steinberg1967] we use
notation from [@bib:l2012-extremal-en-Levchuk1990], which simplifies our proofs.

Let $Phi(K)$ denotes a Chevalley group with the root system $Phi$ over a field
$K$. This group is generated by the root elements $x_r lr((t))$ ($t in K$,
$r in Phi$). Let $Pi = Pi(Phi)$ be a basis for simple roots in $Phi$, and let
$Phi^+$ be the set of positive roots of $Phi$ with respect to $Pi$. We set
$p(Phi) = max{frac(lr((r,r)), lr((s,s))) | r, s in Pi(Phi)}$.

A _Coxeter graph_ of $Phi$ is defined in J.-P. Serre
[@bib:l2012-extremal-en-Serre1966, V.12]. (This concept coincides with the
concept of the Dynkin diagram discussed by R. Carter
[@bib:l2012-extremal-en-Carter1972, § 3.4].) The nodes of this graph are all
roots from $Pi$. By [@bib:l2012-extremal-en-Serre1966, V.15], it gives a _Dynkin
diagram_ of $Phi$ if the numbers $p(Phi)$ and 1 put into correspondence with the
long and short roots $r in Pi$, respectively. For example, we get the following
different Dynkin diagrams

#coxeter-rows(("B", "C", "G"))

The _twisted group_ $twisted(m, Phi)(K)$ is the centralizer in $Phi(K)$ of a
_twisting automorphism_ $theta in Aut Phi(K)$ of order $m = 2$ or 3. According
to [@bib:l2012-extremal-en-Steinberg1967, § 11], $theta$ is the composition of a
graph automorphism $tau$ and a non-trivial automorphism
$sigma: t arrow.r overline(t)$ ($t in K$) of $K$ satisfying the condition
$p(Phi) sigma^m = 1$. We also denote by $overline(" ")$ the symmetry of Coxeter
graph. For certain extension of the symmetry $overline(" ")$ of order $m$ on the
Coxeter graph to the root system $Phi$, we have
$theta(X_r) = tau(X_r) = X_(overline(r))$ ($r in Phi$, $X_r = x_r lr((K))$).

As usual, the “root” elements of $twisted(m, Phi)(K)$ are given by the subgroups
$X_S^1 = twisted(m, Phi)(K) inter 〈 X_r | r in S 〉$ for certain equivalence
classes $S$ of $Phi$, cf. [@bib:l2012-extremal-en-Steinberg1967,
@bib:l2012-extremal-en-Carter1972]. We now associate the root elements with the
$overline(" ")$-orbits.

#source(3, printed: 100) A mapping of a root system to another one is called a
_homomorphism_ if it can be extended to a homomorphism of the root lattices of
these root systems. By [@bib:l2012-extremal-en-Levchuk1982, Lemma
@lem:l1982-parabolic-root-folding], for $p(Phi) = 1$ there exists a homomorphism
$zeta$ of $Phi$ onto a root system such that $zeta(r) = zeta(s)$ if and only if
either $r = s$ or $overline(r) = s$ or $overline(s) = r$. Therefore, if either
$(Phi,m) = (D_4,3)$ or $m = 2$ and $Phi$ is of type $E_6$, $D_(n+1)$, $A_(2n-1)$
or $A_(2n)$ then $zeta(Phi)$ is of type $G_2$, $F_4$, $B_n$, $C_n$ or $B C_n$
[@bib:l2012-extremal-en-Serre1966, V.16], respectively, cf.
[@bib:l2012-extremal-en-Carter1972, Remark 13.3.8] and
[@bib:l2012-extremal-en-Levchuk1982, Lemma
@lem:l1982-parabolic-twisted-automorphism].

When $S$ is an $overline(" ")$-orbit in $Phi$, $S$ has type $A_1$,
$A_1 times A_1$ or $A_1 times A_1 times A_1$, by Propositions 13.6.3 and 13.6.4
in [@bib:l2012-extremal-en-Carter1972]. Then $X_S^1 = x_S lr((F)) tilde.eq F^+$,
where $F$ is the subfield ${t in K | overline(t) = t} = ker(1-sigma)$, $K$ or
$K$, respectively for each type, and $F^+$ is the additive group of $F$. If
$S = {r,overline(r),r+overline(r)}$ has type $A_2$ then $Phi$ is of type
$A_(2n)$ and

$
  X_S^1 = {x_S lr((t,u)) | x_S lr((t,u)) = x_r lr((t))
    x_(overline(r)) lr((overline(t))) x_(r+overline(r)) lr((u)),
    u,t in K, u+overline(u) = plus.minus t overline(t)}.
$

For the $overline(" ")$-orbits ${r+overline(r)}$ and ${r,overline(r)}$, we
denote, respectively, $x_(r+overline(r)) lr((ker(1+sigma)))$ by $X_(2R)$, where
$2R = zeta(r+overline(r))$, and $x_R lr((K))$ by $X_R$, where $R = zeta(r)$, and
$X_R$ is the system of representatives
$x_R lr((t)) = x_r lr((t)) x_(overline(r)) lr((overline(t)))
x_(r+overline(r)) lr((tilde(t)))$ (for all $t in K$) of cosets in $X_S^1$ by the
subgroup $X_(2R)$, and $tilde(" ")$ is a transformation of $K$. In the remaining
cases, $S$ has type $B_2$ or $G_2$ (see [@bib:l2012-extremal-en-Carter1972,
Proposition 13.6.4]), and $twisted(m, Phi)(K)$ is of type $twisted(2, G_2)$,
$twisted(2, B_2)$ or $twisted(2, F_4)$. Then $S$ is the union of
$overline(" ")$-orbits having representatives $r$, $r+overline(r)$ (and also
$2r+overline(r)$ for type $G_2$). We now use the root subsets $alpha(K) = X_R$,
$beta(K) = X_(2R)$, and $gamma(K) = X_(3R)$, which were defined in Proposition
13.6.4 (vi) and (vii) in [@bib:l2012-extremal-en-Carter1972].

Thus, the $overline(" ")$-orbit $alpha$ of each root $r in Phi$ uniquely
determines a root subset $X_alpha$ in $twisted(m, Phi)(K)$. The set of all such
$alpha$ will be denoted by $twisted(m, Phi)$. If $alpha$ is of order 1 then
$alpha$ is said to be of the _first type_. Choosing all $alpha$ with
$r in Pi(Phi)$ we get a basis $Pi(twisted(m, Phi))$ for $twisted(m, Phi)$. If
$p(Phi) = 1$ then $twisted(m, Phi) = zeta(Phi)$, and
$Pi(twisted(m, Phi)) = zeta(Pi(Phi))$. Thus, for type $twisted(3, D_4)$, the
root system $zeta(Phi)$ is of type $G_2$ with $r,q in Pi(Phi)$,
$q = overline(q)$, and we have

$
  X_a = x_a lr((K)), quad a = zeta(r) quad
  (x_a lr((t)) := x_r lr((t)) x_(overline(r)) lr((overline(t)))
    x_(overline(overline(r))) lr((overline(overline(t)))), t in K),
$
$
  X_b = x_q lr((ker(1-sigma))), quad b = zeta(q) quad
  (x_b lr((t)) := x_q lr((t)), t = overline(t)).
$

By analogy with [@bib:l2012-extremal-en-Levchuk1990], $G(K)$ denotes a group of
Lie type associated either with the system $G = twisted(m, Phi)$ or $G = Phi$.
We fix a basis $Pi$ for $G$ and the set $G^+$ of all _positive roots_ with
respect to $Pi$. We define a unipotent subgroup $U$ by
$U = U G(K) := 〈 X_s | s in G^+ 〉$, cf. [@bib:l2012-extremal-en-Carter1972,
@bib:l2012-extremal-en-Steinberg1967, @bib:l2012-extremal-en-Levchuk1990].

Let ${r}^+$ be the family of $s in G^+$ with nonnegative coefficients in the
linear expression of $s-r$ by $Pi$. We set

$
  T(r) := 〈 X_s | s in {r}^+ 〉, quad
  Q(r) := 〈 X_s | s in {r}^+ without {r} 〉 quad (r in G).
$

If $H subset.eq T(r_1) T(r_2) dots T(r_m)$ and the inclusion fails under every
substitution of $T(r_i)$ by $Q(r_i)$ then $cal(L)(H) = {r_1,r_2,dots,r_m}$ is
said to be the _set of corners_ of $H$.

As in [@bib:l2012-extremal-en-Carter1972, § 4.4], take the $K$-algebra
$cal(L)_K$ with Chevalley basis ${e_r (r in Phi),dots}$. Denote by $N Phi(K)$
the subalgebra in $cal(L)_K$ with the basis ${e_r | r in Phi^+}$. The Lie
products $e_r ast e_s = c_(r s) e_(r+s)$ ($c_(r s) = 0$ for $r+s in.not Phi$)
define the structure constants of Chevalley basis in $N Phi(K)$. Chevalley’s
commutator formula gives $[X_r,X_s] = x_(r+s) lr((c_(r s) K)) mod Q(r+s)$. Using
also relations from [@bib:l2012-extremal-en-Levchuk1990, § 4 (I)] and
[@bib:l2012-extremal-en-Levchuk2009, Theorem 2] for the twisted groups, we
easily get

#lemma[Let $U = U G(K)$ and $r,s,r+s in G^+$. Then either
  $[X_r,X_s] = X_(r+s) mod Q(r+s)$ or $G = Phi$, $c_(r s) K = 0 = p(Phi)! K$,
  and $[X_r,X_s] subset.eq Q(r+s)$.]
<lem:l2012-extremal-en-root-commutator>

It is well known that every element $gamma in U$ is uniquely represented as the
product of root elements $x_r lr((gamma_r))$, $r in G^+$, arranged according to
a fixed order in $G$, cf. [@bib:l2012-extremal-en-Steinberg1967, Lemma 18] (we
call such representation as the #source(4, printed: 101) _canonical
decomposition_ of $gamma$). The coefficient $gamma_r$ is said to be an
_r-projection_ of $gamma$. Putting

$
  pi(gamma) := sum_(r in Phi^+) gamma_r e_r quad (gamma in U Phi(K)),
  quad alpha compose beta := pi(pi^(-1)(alpha) pi^(-1)(beta))
  quad (alpha,beta in N Phi(K)),
$

we define an adjoint group $(N Phi(K),compose)$, which is isomorphic to the
group $U Phi(K)$. Similar representation of $U twisted(m, Phi)(K)$ for
$p(Phi) = 1$ as an adjoint group of certain $K_sigma$-module
$N twisted(m, Phi)(K)$ is used in [@bib:l2012-extremal-en-Levchuk1990] and
[@bib:l2012-extremal-en-Levchuk2009].

The set of r-projections of all elements in a subset $H subset.eq U G(K)$ is
called an _r-projection_ of $H$. If an s-projection of $gamma in H$ is the
product of its r-projection and a fixed non-zero scalar, not depending on a
choice of $gamma$, then $r,s$ are said to be _connected_ in $H$. If also there
exist $p,r+p,s+p in G^+$ then $r$ and $s$ are said to be _p-connected_ in $H$.
It is easy to prove the following

#lemma[Let $H lt.closed.eq U Phi(K)$, $p(Phi)! K = K$, $r$ be a corner in $H$,
  $s in {r}^+$, and $s != r$. Then $H$ possesses a subgroup with a corner $s$
  and with the s-projection $K$.] <lem:l2012-extremal-en-corner-full-projection>

The _highest root_ in $G^+$ is denoted by $rho$. If $r in G$ then
$r = sum_(alpha in Pi) c_alpha alpha$ with $c_alpha in ZZ$. The _height_ of $r$
is defined by $ht(r) = sum_(alpha in Pi) c_alpha$. For every system $G$, the
_Coxeter number_ $h$ is defined by $ht(rho)+1 = h(G) = h$. The highest roots of
root systems and $h$ are described in [@bib:l2012-extremal-en-Bourbaki1968,
Tables I–IX]. When $G$ is of type $twisted(2, F_4)$, $twisted(2, B_2)$,
$twisted(2, G_2)$ or $twisted(2, A_(2n))$, we have $h = 9$, 3, 4 or $2n$,
respectively.

The subgroups $U_i = 〈 X_r | r in G^+, ht(r) >= i 〉$ form the _standard
central series_ $U = U_1 supset U_2 supset dots supset U_h = 1$ in $U$, by
[@bib:l2012-extremal-en-Carter1972, Theorem 5.3.3] and
[@bib:l2012-extremal-en-Levchuk1990]. We shall use some property of the
hypercenters (Lemma @lem:l2012-extremal-en-hypercenters-incident). Some
subgroups $A$ and $B$ in a group are said to be _incident_ if $A subset.eq B$ or
$B subset.eq A$. Under the conditions of the following lemma the upper central
(or hypercentral) series $1 = Z_0 subset Z_1 subset Z_2 subset dots$ is
standard, by [@bib:l2012-extremal-en-Levchuk1990]. Set $t(U) = 6$, 3 or 1 for
$G = E_8$, $E_6$, $A_n$, respectively,

$
  t(U) = 4 quad "for" G = G_2,F_4,twisted(2, F_4),twisted(2, E_6),E_7,
  "or" 2K = K "and" G = twisted(3, D_4),
$

and $t(U) = 2$ in the other cases. By [@bib:l2012-extremal-en-Levchuk2002, Lemma
3], we have

#lemma[Let $U = U G(K)$, and let $p(Phi)! K = K$ for $G = Phi$. Then each normal
  subgroup of $U$ is incident with every hypercenter $Z_i$,
  $0 <= i <= t(U)$.] <lem:l2012-extremal-en-hypercenters-incident>

The centralizer $C(T(r))$ of $T(r)$ in $U$ was determined in
[@bib:l2012-extremal-en-Levchuk1990]. For $G = Phi$, we distinguish also some
subgroups of the following form:

$
  alpha(K) (C(T(r)) inter C(T(r'))), quad
  alpha(t) := x_r lr((t)) x_(r') lr((t)) quad (t in K), quad r+r' = rho;
$ <eq:l2012-extremal-en-paired-corners>

$
  beta(K) (C(T(r)) inter C(T(r')))
  {x_r lr((t)) x_(r') lr((t)) x_(r+p) lr((c t)) | t in K} quad (c in K),
  quad beta(t) := x_(r+p) lr((t)) x_(r'+p) lr((t)), quad r+r'+p = rho.
$ <eq:l2012-extremal-en-linked-three-corners>

The group $U$ of type $A_n$ (denoted by $U A_n lr((K))$) is isomorphic to the
unitriangular group $UT(n+1, K)$. By [@bib:l2012-extremal-en-Levchuk1976,
Theorem @th:l1976-maximal-abelian] (for a finite field $K$ of odd order, see
also [@bib:l2012-extremal-en-Weir1955, Theorem 7]), we get

#lemma[Up to conjugation by a diagonal automorphism, every maximal abelian
  normal subgroup of $U A_n lr((K))$ is either $T(p)$, or
  @eq:l2012-extremal-en-paired-corners, or
  @eq:l2012-extremal-en-linked-three-corners for $2K = 0$, $n >= 3$ and some
  $r,r' in Phi^+$, $p in Pi$.] <lem:l2012-extremal-en-an-maximal-abelian>
