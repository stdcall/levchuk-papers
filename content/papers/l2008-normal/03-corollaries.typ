#import "../../main-defs.typ": twisted
#import "defs.typ": *

=== Corollaries <sec:l2008-normal-corollaries>
For a finite base field, when posing the problem about large (of highest order)
Abelian subgroups in $U$ [@bib:l2008-normal-Kondratyev1986, Problem 1.6],
Kondrat’ev mentioned the question of describing the subset $A_N lr((U))$ of
normal subgroups. Using the known orders (see, e.g.,
[@bib:l2008-normal-Kondratyev1986, @bib:l2008-normal-Vdovin2001]), we obtain
$A_N lr((U)) != emptyset$. In particular, for the groups $U E_m lr((K))$,
according to a description of $maximal$ given elsewhere, the four subgroups
mentioned in Theorem~@th:l2008-normal-exceptional, (c) exhaust $A_N lr((U))$.
Thus, for $U = U G(K) approx N G(K)$, the set $A_N lr((U))$ is described by the
following corollary.

#corollary[
  The set $A_N lr((U))$ consists of the following subgroups (below, $d in K^*$
  and $c in K$):

  (a) $T_(n+1,n)$ for the type $A_(2n-1)$; for the type $A_(2n)$ with $n > 1$,
  the subgroup $T_(n+2,n+1)$ is added;

  (b) $T_(1,-1)$ for $G = C_n$ with $n > 2$ or $twisted(2, A_(2n-1))$; for the
  type $twisted(2, A_(2n))$, the subgroups $T_(1,-1) + d K_sigma e_(n 0)$;

  (c) $T_(2,-1) + T_(n 0)$ and $T_(n n-1)$ for $G = B_n$ or
  $twisted(2, D_(n+1))$ and $2K = K$ in the cases $n > 4$ and $n < 4$,
  respectively (for $n = 4$, both subgroups);

  (d) the subgroups mentioned in Theorem~@th:l2008-normal-classical-maximal, (b)
  for $G = D_n$ or $twisted(2, D_(n+1))$ and $2K = 0$; for $G = D_n$, the
  subgroups $T_(2,-1)$ and $T_(2,-1)^tau$ are added; for $n = 4$, $T_43$ is also
  added;

  (e) $T(q_43) + U_6$ for the types $twisted(2, E_6)$ and, if $2K = K$, $F_4$;
  for $2K = 0$, the subgroups $T(p_42) + K(p_43 + c q_43)$,
  $T(q_43) + T(p_41) + K(p_(3,-2) + c p_42)$, $T(p_42) + K q_43$, and
  $T(p_(4,-1)) + K p_43 + K p_42 + K p_41 + K(q_(3,-2) + c q_42)$;

  (f) $angle.l R_43 lr((d)) angle.r R_42 lr((K)) U_5$ for $G = twisted(2, F_4)$,
  $U_2 angle.l alpha angle.r$, where $alpha notin U_2$, for the groups
  $U twisted(2, B_2) lr((K))$ and $U C_2 lr((2))$;
  $U_2 angle.l K alpha angle.r$, where $alpha notin U_2$, for the type $A_2$;
  and the subgroups $T_(1,-1)$ and $T_21$ if $G = C_2$, $2K = 0$, and $|K| > 2$;

  (g) $U_3$ for the types $twisted(3, D_4)$ and, if $6K = K$, $G_2$; $U_2$ if
  $3K = 0$ for the types $twisted(2, G_2)$ and $G_2$; the subgroups
  ${x_(a+b) lr((t)) x_(2a+b) lr((t c)) | t in K} U_4$ and $U_3$ for the type
  $G_2$ provided that $2K = 0$ and $|K| > 2$; and, finally, the subgroup
  $angle.l x_a lr((1)) x_(2a+b) lr((1)),
  x_(a+b) lr((1)) x_(2a+b) lr((1)) angle.r U_4$ in $U G_2 lr((2))$.
] <cor:l2008-normal-largest>

For the purposes of CFSG revision, Parker and Rowley
[@bib:l2008-normal-Parker1997, @bib:l2008-normal-Parker1998] described groups
$U G(K)$ with an extremal subgroup, that is, a normal Abelian subgroup not
contained in $U_2$. Theorems~@th:l2008-normal-exceptional and
@th:l2008-normal-classical-maximal describe all groups $U G(K)$ with an extremal
subgroup (or, equivalently, for which $maximal$ contains a subgroup with a
simple corner, including (see [@bib:l2008-normal-Parker2003]) subgroups with a
unique simple corner). Note that the extremal subgroups having three simple
angles in $U D_4 lr((K))$ with $2K = 0$ that are described in
[@bib:l2008-normal-Parker1997, Theorem 1.3] are Abelian only for $|K| = 2$; the
corresponding subgroup in $U twisted(2, D_4) lr((K))$ from
[@bib:l2008-normal-Parker1998, Theorem 1.2] is Abelian for $|K| = 4$.

According to [@bib:l2008-normal-Levchuk1992], classes of normal subgroups and
Lie ideals coincide in $N Phi(K)$ with $p(Phi)! K = K$, except for the types
$D_n$ and $E_n$ in the case of $2K = 0$. By Theorem~@th:l2008-normal-orthogonal,
the normal subgroups containing no frames $frame([H, X_p])$, and only such
groups, are not ideals in the Lie ring $N D_n lr((K))$ (such $p = p_32$ is
unique).

Let $Gamma$ be a chain with an anti-isometry $prime$. We define a chain
$tilde(Gamma) = Gamma' union Gamma$ by setting $i'' = i$ and $i' <= j$ for all
$i, j in Gamma$; we denote the common element of $Gamma$ and $Gamma'$ (which is
unique if exists) by $0$. We define modules $N G(K)$ of types $G = C_Gamma$,
$D_Gamma$ (for $Gamma' inter Gamma = emptyset$), $B_Gamma$,
$twisted(2, D_Gamma)$, and $twisted(2, A_(tilde(Gamma)))$ and their adjoint
groups by the generators $x e_(i v)$, where $i in Gamma$ and $v in tilde(Gamma)$
(in particular, $N twisted(2, A_(tilde(Gamma))) lr((K)) = angle.l K e_(i v),
ker(1 + sigma) e_(i i') | i, v in tilde(Gamma), i' < v < i angle.r$) and
defining relations locally preserving the structure of the same type. The
theorems of Sections~@sec:l2008-normal-structure and @sec:l2008-normal-abelian
are transferred as for the type $A_Gamma$ in the description of automorphisms of
finitary unitriangular groups in [@bib:l2008-normal-Levchuk1987].
