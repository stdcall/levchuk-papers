#import "../../main-defs.typ": ed-note, source, twisted
#import "defs.typ": *

=== Maximal Abelian normal subgroups <sec:l2008-normal-abelian>
In the group $U = U G(K) approx N G(K)$, the set $maximal$ of all maximal (or
self-centralizing) normal Abelian subgroups is known for the type $A_n$
[@bib:l2008-normal-Levchuk1987]. We use the standard central series
$U_1 supset U_2 supset dots$ from [@bib:l2008-normal-Carter1972], the notations
$p_(i v)$ and $q_(i v)$ for roots from systems of types $F_4$ and
$twisted(2, E_6)$, the representation
$U twisted(2, F_4) lr((K)) = angle.l R_(i v) lr((y)) | 1 <= |v| < i <= 4,
y in K angle.r$ from [@bib:l2008-normal-Levchuk1990], Lemma 3 from
[@bib:l2008-normal-Levchuk2002] on a hypercenter incident to all normal
subgroups, and the notation $K e_r = K_r$ for root subgroups.

#theorem[
  Let $U$ be of exceptional type. Then,

  (a) if $G = G_2$ and $2K = 0$ and $|K| > 2$, then $maximal$ consists of the
  subgroups $U_4 {x_(a+b) lr((t u)) x_(2a+b) lr((t v)) | t in K}$, where
  $u, v in K$ and $(u, v) != (0, 0)$; for $|K| = 2$, it consists of the
  subgroups $U_4 angle.l x_a lr((1)) x_(2a+b) lr((1)),
  x_(a+b) lr((1)) x_(2a+b) lr((1)) angle.r$, $U_3$, and $X_(a+b) U_4$, where $a$
  and $b$ are simple roots and $|a| < |b|$;

  (b) if $G = twisted(2, B_2)$, then
  $maximal = {U_2 angle.l alpha angle.r | alpha in U without U_2}$; if $3K = 0$
  and $G = G_2$ or $twisted(2, G_2)$, then $maximal = {U_2}$; and if either
  $6K = K$ and $G = G_2$ or $G = twisted(3, D_4)$, then $maximal = {U_3}$;

  (c) for type $E_m$, $maximal$ contains $T(alpha_1)$ and $T(alpha_6)$ for
  $m = 6$, $T(alpha_7)$ for $m = 7$, and
  $T(alpha_1 + 2alpha_2 + 2alpha_3 + 3alpha_4 + 2alpha_5 + alpha_6)$
  for $m = 8$, where the $alpha_i$ are simple roots from
  [@bib:l2008-normal-Bourbaki1975, Tables V–VII], and the remaining subgroups
  from $maximal$ belong to $U_4$, $U_5$, and $U_13$, respectively;

  (d) for type $twisted(2, F_4)$,
  $maximal = {U_5 {R_(3,-2) lr((t)) R_42 lr((t u)) | t in K}
    quad (u in K), U_5 R_42 lr((K)) angle.l R_43 lr((v)) angle.r
    quad (v in K^*)}$.#ed-note[
    For $G = twisted(3, D_4)$ in characteristic $2$, the list in (b) is
    incomplete. The additional families, including the case $|K_sigma| = 2$, are
    given in [@bib:ed-Levchuk2012ExtremalAbelianEn, Theorem
    @th:l2012-extremal-en-rank-two-maximal, (d)].
  ]
] <th:l2008-normal-exceptional>

Finally, for the groups $N twisted(2, E_6) lr((K))$ with $F = K_sigma$ and
$N F_4 lr((K))$ with $F = K = 2K$,
$maximal = {T(q_43) + U_6, T(p_(4,-1)) + F(q_(3,-2) + c q_42),
  c in F}$, and for $2K = 0$ and $G = F_4$, $maximal$ consists of
$T(p_42) + K q_43$, $T(q_43) + T(p_41) + K(p_(3,-2) + c p_42)$,
$T(p_(4,-1)) + K p_43 + K p_42 + K p_41 + K(q_(3,-2) + c q_42)$,
$T(p_42) + K(p_43 + c q_43)$, and
$T(p_(4,-1)) + K p_41 + K(q_(3,-2) + c q_42) + K(p_(3,-2) + d p_42)$, where
$c, d in K$.#ed-note[
  In characteristic $2$, the mixed $K$-line $T(p_42) + K(p_43 + c q_43)$ with
  $c != 0$ is invalid for $|K| > 2$: both corner projections must have order
  $2$, as proved in [@bib:ed-Levchuk2012ExtremalAbelianEn, proof of Theorem
  @th:l2012-extremal-en-f4-e6-maximal, p. 112]. The complete characteristic $2$
  lists for $F_4$ and $twisted(2, E_6)$, including the corresponding largest
  normal Abelian subgroups in Corollary @cor:l2008-normal-largest, are given in
  Theorems @th:l2012-extremal-en-f4-e6-maximal and
  @th:l2012-extremal-en-large-normal-abelian of that paper.
]

Using the standard notation $epsilon_i - m epsilon_j = p_(i,m j)$ for
$1 <= j <= i <= n$ and $m in {0, -1, +1}$, the positive roots of systems of type
$A_(n-1)$, $B_n$, $C_n$, and $D_n$ [@bib:l2008-normal-Bourbaki1975], and the
$zeta$-correspondence defined in Section~@sec:l2008-normal-structure, for
$r = p_(i v)$, we write $e_r = e_(i v)$ and $T_(i v) = T(p_(i v))$ in the
modules $N G(K)$ of all classical types except for the subgroups
$T_(i 1) = T(p_(i,-1)) + T(p_(i 1))$ in the module $N D_n lr((K))$. In the cases
of $G = twisted(2, A_m)$ and of $2K = K$ and $G = C_n$, the use of the
$Phi^+$-matrix representation and the formula from
[@bib:l2008-normal-Levchuk1990, Lemma
@lem:l1990-chevalley-classical-root-centralizers (II)] for the centralizer
$C(T_(i j)) = T_(1,-j-1)$
(i.e., $T_(j+1,-j-1)$ or $T_(j+2,-j-1)$) is effective; in the other cases, for
$i = n$, $T_(n n-1)$ is added. We consider only one group among all groups $U$
of type $C_n$ and $B_n$, which are isomorphic for $2K = 0$. We set $F = K_sigma$
for the twisted types and $F = K$ otherwise.

#theorem[
  The set $maximal$ in a group $U$ of type $twisted(2, A_(2n))$ is formed by the
  subgroups $T_(1,-1) + a K_sigma e_(n 0)$ and in a group of type
  $twisted(2, A_(2n-1))$, by the subgroup $T_(1,-1)$; for $2K = 0$, the subgroup
  $T_(2,-2) + b K_sigma e_(n,-1)
  + b K_sigma(e_(n 1) + a e_(n,-1))$ $(a, b in K^*)$ is added; and for $2K = K$
  and $G = C_n$, $maximal = {T_(1,-1)}$. For the other groups $U$ of classical
  type, $maximal$ consists of $T_(2,-1)$ and $T_(2,-1)^tau$ for $G = D_n$ and of
  the subgroups $T_(n j) + T_(1,-j-1)$ $(0 <= j < n)$, where $j != n-2$ or
  $G = C_n$, and $T_(n,i-1) + T_(1,-i-1) + F(e_(n i) + a e_(n-1,-i))$, where
  $1 <= i <= n-2$; for $2K = 0$, it also #source(3, printed: 286) includes the
  following subgroups (below, $a, b, d in K^*$ and $c in K$):

  (a) $angle.l a e_(n,n-1) + d e_(n-1,-n+1) angle.r + T_(n,n-2)$,
  $angle.l a e_(n,n-1) + b e_(n-2,-n+3) + d e_(n-1,-n+1) angle.r
  + K(a e_(n,n-2) + b e_(n-1,-n+3))
  + K(a e_(n,n-3) + b e_(n-1,-n+2)) + T_(n,n-4)$,
  $T_(n,n-4) + K(e_(n,n-1) + b e_(n-2,-n+3))
  + K(e_(n,n-2) + b e_(n-1,-n+3))
  + K(e_(n,n-3) + b e_(n-1,-n+2))$, and
  $T_(n,j-2) + T_(1,-j-1) + K(e_(n j) + a e_(n-1,-j+1)
    + c e_(n-1,-j)) + K(e_(n,j-1) + a e_(n-1,-j))$
  $(2 <= j <= n-2)$ and for $|K| = 2$, the subgroups
  $T_(n,n-3) + K(e_(n n-2) + e_(n-1,-n+2) + e_(n-1,-n+1))
  + K(e_(n n-1) + e_(n-2,-n+2) + e_(n-1,-n+2)
    + c e_(n-1,-n+1))$ and $K(e_(n,n-1) + e_(n-2,-n+3) + e_(n-2,-n+2)
    + c e_(n-1,-n+1) + e_(n-1,-n+2))
  + K(e_(n,n-2) + e_(n-1,-n+3) + e_(n-1,-n+2) + e_(n-1,-n+1))
  + K(e_(n,n-3) + e_(n-1,-n+2)) + T_(n,n-4)$ for the type $C_n$;

  (b) $T_(2,-1) + a sum_(u=1)^n K_sigma e_(u 0)$ for the type
  $twisted(2, D_(n+1))$,
  $K_sigma(e_32 + a e_10 + e_(2,-1))
  + K_sigma(e_31 + a e_20 + e_(2,-1))
  + {a x e_30 + a bar(a) lr((x + bar(x))) e_(2,-1) | x in K} + T_(3,-1)$
  in $N twisted(2, D_4) lr((4))$, the subgroups
  $T_(3,-2) + sum_(u=2)^n K(e_(u 1) + a e_(u,-1))$ together with their images
  for $n = 4$ under the graph automorphism of order $3$ for $G = D_n$, and
  $K(e_43 + e_21 + e_(2,-1) + e_(3,-2))
  + K(e_42 + e_31 + e_(3,-1) + e_(3,-2))
  + K(e_41 + e_(3,-2)) + K(e_(4,-1) + e_(3,-2)) + T_(4,-2)$ in $N D_4 lr((2))$;

  (c) $T_(n,n-4) + F(e_(n n-1) + f e_(n-2,-n+3))
  + F(e_(n n-2) + f e_(n-1,-n+3))
  + F(e_(n n-3) + f e_(n-1,-n+2))$ and $F(e_(n,j-1) + f e_(n-1,-j))
  + F(e_(n j) + f e_(n-1,-j+1) + g e_(n-1,-j))
  + T_(n,j-2) + T_(j+2,-j-1)$, where $f in F^*$, $g in F$, and $2 <= j <= n-2$,
  for $G = D_n$ and $twisted(2, D_(n+1))$;
  $K(e_(n 2) + u e_(n-1,-1) + v e_(n-1 1) + c e_(n-1,-2))
  + K(e_(n 1) + u e_(n-1,-2)) + K(e_(n,-1) + v e_(n-1,-2))
  + T_(n,-2) + T_(4,-3)$, where $u, v in K$ and $(u, v) != (0, 0)$, and
  $K(e_(n 1) + c e_(n,-1))
  + K(e_(n-1,1) + a e_(n 1) + c e_(n-1,-1)) + T_(3,-2)$ for $G = D_n$; and, for
  the type $twisted(2, D_(n+1))$, the subgroups
  $T_(2,-1) + a K_sigma e_(n 0) + a K_sigma(e_(n-1,0) + b e_(n 0))$
  (where $b notin K_sigma$) and $K_sigma(e_(n 1) + a e_(n-1,0) + g e_(n-1,-1))
  + {a x e_(n 0) + a bar(a) lr((x + bar(x))) e_(n-1,-1) | x in K}
  + T_(n,-1) + T_(3,-2)$ where $g = 0$ for $N twisted(2, D_4) lr((4))$.
] <th:l2008-normal-classical-maximal>
