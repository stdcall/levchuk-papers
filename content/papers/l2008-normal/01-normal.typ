#import "../../main-defs.typ": source, twisted
#import "../../collection.typ": article-introduction
#import "defs.typ": *

#article-introduction[Introduction] <sec:l2008-normal-introduction>
#source(1, printed: 284)
The uniform normal structure of the unipotent subgroup
$U G(K) = chevron.l X_r | r in G^+ chevron.r$ of the Chevalley group over a
field $K$ of type $G$ associated with a root system $Phi$ or of twisted type
$G = twisted(m, Phi)$ is described; for special cases, see
[@bib:l2008-normal-Levchuk1992, @bib:l2008-normal-Suleimanova2002] and
references therein. The maximal Abelian normal subgroups are listed. In
Section~@sec:l2008-normal-corollaries, corollaries are given.

=== Normal structure <sec:l2008-normal-structure>
The group $U twisted(m, Phi) lr((K))$ is the centralizer in $U Phi(K)$ of the
“twist” automorphism $upright(sigma)$, being the composition of a graph
automorphism $tau$ and an automorphism $sigma: t arrow overline(t)$ of the field
$K$ satisfying the conditions $p(Phi) sigma^m = 1$ and $sigma != 1$, where
$p(Phi) = max {lr((r, r))/lr((s, s)) | r, s in Phi}$. For $p(Phi) = 1$, we have
$tau(X_r) = X_(overline(r))$ for a substitution $"–"$ of order $m = 2$ or $3$ on
the root system $Phi$ which is extendable to a homomorphism $zeta$ of the root
lattice [@bib:l2008-normal-Carter1972]. If $m = 2$ and $Phi$ is of type
$D_(n+1)$, $A_(2n-1)$, $A_(2n)$, or $E_6$, or if $(m, Phi) = (3, D_4)$, then
$zeta(Phi)$ is a root system of type $B_n$, $C_n$, $B C_n$, $F_4$, or $G_2$,
respectively. We associate sets of roots with $"–"$-orbits in $Phi$. A class
$S = {r, overline(r), r + overline(r)}$ of type $A_2$ corresponds to the
subgroup $x_({r + overline(r)}) lr((ker(1 + sigma)))$ and a fixed system
$X_({r, overline(r)})$ of coset representatives of the $S$th root subgroup
described in [@bib:l2008-normal-Carter1972, 13.6.4].

For $r in G$, let ${r}^+$ denote the set of $s in G^+$ for which the
coefficients in the linear expression of $s-r$ in the base $Pi(G)$ are
nonnegative. We say that $S subset.eq Phi^+$ is 2-normal if $i s + j t in S$
whenever $s in S$, $t, s+t, i s+j t in Phi^+$; and the constant $C_(i j, s t)$
$(i, j > 0)$ in the Chevalley commutator formula is odd. We set
$T(r) = chevron.l X_s | s in {r}^+ chevron.r$ and, for $L subset G^+$,
$Q(L) = chevron.l X_s | s in union_(r in L) {r}^+ without L chevron.r$; changing
${r}^+$ by the 2-normal closure ${r}_2^+$ of the root $r$ in $Phi^+$ in these
expressions, we obtain $T{r}$ and $Q{L}$. We say that
$corners(H) = {r_1, r_2, dots, r_m}$ is the set of corners in
$H subset.eq T(r_1) T(r_2) dots T(r_m)$ (or the set of 2-corners
$corners_2 lr((H))$ for $H subset.eq T{r_1} T{r_2} dots T{r_m}$) if the
inclusion is violated under any replacement of $T(r_i)$ by $Q(r_i)$
(respectively, of $T{r_i}$ by $Q{r_i}$). A frame for $H$ is defined as a set
$frame(H) subset.eq product_(s in corners(H)) X_s$ such that
$frame(H) = H mod product_(s in corners(H)) Q(s)$; replacing $Q(s)$ by $Q{s}$
and $corners(H)$ by $corners_2 lr((H))$, we obtain the definition of a 2-frame
$frame_2 lr((H))$.

When the $s$-projection of any element of $H$ equals the product of its
$r$-projection and a fixed nonzero scalar, then we say that $r$ and $s$ are
connected in $H$; if, moreover, $p, r+p, s+p in G^+$, then $r$ and $s$ are also
$p$-connected.

#theorem[
  A subgroup $H$ in $U G(K)$, where $G = A_n$, $G = twisted(2, A_m)$, or
  $2K = K$ and $G = B_n$ or $C_n$, is normal if and only if, for any corner $r$
  and any $p in Pi(G)$ such that $r+p in G$, either

  (A) $frame([H, X_p]) Q(r+p) subset.eq H$ or $G = B_n$ and

  (B) any two corners in $[H, X_p]$ are $q$-connected for some $q in Pi(G)$, two
  corners in $[H, X_q]$ are connected, and
  $frame([H, X_p]) frame([H, X_q]) Q(r+p, r+p+q) subset H$.
] <th:l2008-normal-classical>

#theorem[
  A subgroup $H$ of a group $U Phi(K)$ of type $C_n$ over a field $K$ of order
  $>2$ and characteristic $2$ is normal if and only if, for any its 2-corners
  $r$ and any $p in Pi(Phi)$ with a short root $r+p in Phi$, either

  (A₂) $frame_2 lr(([H, X_p])) Q{r+p} subset.eq H$ and, for a short root $s$ of
  $r$ and $p$ with $|r| != |p|$, $Q{r+p+s} subset.eq H$ or

  (B₂) in $[H, X_p]$, the two 2-corners are $q$-connected for a simple root $q$;
  in $[H, X_q]$, the two 2-corners are connected; and
  $frame_2 lr(([H, X_p])) frame_2 lr(([H, X_q])) Q{r+p, r+p+q} subset H$.
] <th:l2008-normal-symplectic>

The normal structure of the groups $U C_n lr((2))$ is more cumbersome.

Take a subalgebra $N Phi(K)$ with basis $e_r$ $(r in Phi^+)$ in the $K$-algebra
with Chevalley basis $e_r$ $(r in Phi)$, $dots$. We #source(
  2,
  printed: 285,
) construct an isomorphism $pi$ onto its adjoint group with multiplication
defined by $alpha compose beta = pi(pi^(-1) lr((alpha)) pi^(-1) lr((beta)))$ by
setting $pi(alpha) = sum_(r in Phi^+) t_r e_r$, provided that the element
$alpha in U Phi(K)$ canonically decomposes into the product of root elements
$x_r lr((t_r))$ [@bib:l2008-normal-Carter1972, 5.3.3]. In
[@bib:l2008-normal-Levchuk1990], the twisted group $U G(K)$ in the module
$N G(K)$ for $G = twisted(m, Phi)$, where $p(Phi) = 1$, was considered. We write
$+$ instead of $compose$ if the factors do not depend on the choice of $pi$. For
$N G(K)$, we use the same terminology as for $U G(K)$.

#theorem[
  A subgroup $H$ of the group $N G(K)$ of type $D_n$ (or $twisted(2, D_n)$) is
  normal if and only if, for $p in Pi(G)$ and any corner $r$ with $r+p in G$,
  one of conditions (A), (B), or (C) (respectively, (C′)) holds; the last
  conditions are

  (C) $r$ and $overline(r)$ are $p$-connected corners in $H$ and there exist
  simple roots $p_j = overline(p)_j$ and roots $r_j = r+p_1+p_2+dots+p_j$, where
  $p_1 = p$, $1 <= j <= t$, and $t > 1$, for which the
  $(r, overline(r))$-projection and the $(r_j, overline(r)_j)$-projections with
  $j < t-1$ in $H$ generate a submodule $K(a, b)$ in the $K$-module $(K, K)$;
  the $(r_(t-1), overline(r)_(t-1))$-projection equals $K(a, b)$ or $H$ contains
  a corner $!= overline(r)_(t-1)$, $p_t$-connected with $r_(t-1)$; and
  $
    Q(r_t, overline(r)_t, r+overline(r)+p) + frame([[H, X_p], X_r])
    + frame([[H, X_p], X_(overline(r))]) + frame([H, X_(p_t)])
    + sum_(j=2)^t K(a e_(r_j) + b e_(overline(r)_j)) subset.eq H
  $
  and either $frame([H, X_p]) + T(r+overline(r)+p) subset.eq H$ or $|H_r| = 2$,
  the corner $r$ is simple and $p$-connected to the corner $s = overline(s)$,
  and
  $
    H supset.eq K{a e_(r+p) + b e_(overline(r)+p) - a b e_(r+overline(r)+p)
      - c e_(s+p) | a in H_r^*, b in H_(overline(r))^*, c in H_s^*};
  $

  (C′) there exist classes $r_j = r+p_1+p_2+dots+p_j$ of type $A_1 times A_1$,
  where the $p_j in Pi(G)$ are of type $A_1$ for $1 <= j <= t$ and $t > 1$ and
  $p_1 = p$, for which
  $
    Q(r_t, 2r+p) + frame([H, X_(p_t)])
    + sum_(j=2)^t (K_sigma H_r) e_(r_j) subset.eq H;
  $
  the $r_j$-projections with $j < t-1$ in $H$ equal $K_sigma H_r$ and are
  1-dimensional $K_sigma$-modules; the $r_(t-1)$-projection equals $K_sigma H_r$
  or $H$ contains a corner $p_t$-connected with $r_(t-1)$; and either
  $frame([H, X_p]) + T(2r+p) subset.eq H$ or $|H_r| = 2$ and the corner $r$ is
  simple and $p$-connected with a corner $s$ such that
  $
    {(c overline(x) + x overline(c)) e_(2r+p) - x e_(r+s+p) | x in K}
    + K_sigma lr((c e_(r+p) + c overline(c) f e_(2r+p) - e_(s+p))) subset.eq H
  $
  for $c in H_r^*$ and $f in H_s^*$.
] <th:l2008-normal-orthogonal>
