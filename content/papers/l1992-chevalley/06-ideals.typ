#import "../../main-defs.typ": *
#import "defs.typ": *
=== Ideals and normal subgroups <sec:l1992-chevalley-ideals>
R. Dubisch and S. Perlis [@bib:l1992-chevalley-Dubisch1951] were found an
evident description of ideals of $NT_n lr((K))$ algebra over a field $K$. Ideals
of associated Lie ring conform a more spread class, however they permit a
similar description [@bib:l1992-chevalley-LevchukConnections], I; by Theorem
@th:l1992-chevalley-unitriangular-normal-lie this is equivalent to description
of normal subgroups of adjoint group. By analogic methods we can investigate a
normal structure of unipotent subgroup $U Phi(K)$ in Chevalley group of type
$Phi$.

Each element $alpha in U Phi(K)$ is uniquely expressible in the form of a
product of root elements $x_r lr((t_r))$ $(r in Phi^+)$ disposed according to
fixed root ordering [@bib:l1992-chevalley-Steinberg1967, Lemma 17]. Let us
distinguish a subalgebra $N Phi(K)$ with a basis ${e_r | r in Phi^+}$, in Lie
$K$-algebra with Chevalley basis ${e_r (r in Phi), dots}$
([@bib:l1992-chevalley-Carter1972, Sect. 4.4], and
[@bib:l1992-chevalley-Hurley1971]). Also, suppose
$pi(alpha) = sum_(r in Phi^+) t_r e_r$. It is clearly, $pi$ is an isomorphism of
group $U Phi(K)$ onto $N Phi(K)$ one in respect to operation
$alpha compose beta = pi(pi^(-1) lr((alpha)) pi^(-1) lr((beta)))$. It turns to
be, that class of ideals of Lie ring $N Phi(K)$ over the field
$K = 2K = p(Phi) ! K$ coincides with a class of normal subgroups of group
$angle.l N Phi(K), compose angle.r$.

Let us give a description of ideals of Lie ring $N Phi(K)$ for some types of
$Phi$. For a root $r in Phi$ we denote as $Q(r)$ the subalgebra with basis
${e_s | s in {r}^+, s != r}$, where ${r}^+$ is a totality of positive roots $s$,
for which $s-r$ is a linear
#source(12, printed: 238)
combination of fundamental roots with non-negative coefficients. Let
$H subset N Phi(K)$ and $H_r$ is a totality of $r$-coordinates of all elements
from $H$. A positive root $q$ is called as corner of set $H$, if $H_q != 0$, and
for all roots $s != q$, $q in {s}^+$, we have $H_s = 0$. We denote by $*$
multiplication within Lie ring $N Phi(K)$.

#theorem[
  Let $Phi$ is of type $A_n$, $B_n$ or $C_n$, $K$ is a field with invertible
  element $p(Phi)$. Subset $H$ of Lie ring $N Phi(K)$ is its ideal if and only
  if $H$ is additive subgroup and for each its corner $r$ at $Q(r) subset.not H$
  there exist corner $s$, fundamental root $p$ and non-zero element $d in K$
  such that $r+p,s+p in Phi^+$, $K e_p * H subset H$, being $s$-coordinate of
  each element from $H$ is equal to product of its $r$-coordinate by $d$, and
  besides that either a) $Q(r+p) + Q(s+p) subset H$, or b) $Phi = B_n$ and a
  fundamental root $q$ exist for which $p+q,r+p+q,s+p+q$ are roots and
  $ Q(r+p+q) + Q(s+p+q) + K e_q * (K e_p * H) subset H. $
] <th:l1992-chevalley-classical-ideals>

Note that ideals of Lie ring $N Phi(K)$ have more bulky description, when $Phi$
is of type $D_n$ (also at $Phi = E_6,E_7,E_8$).

Let us construct generalization of Lie ring $N Phi(K)$ analogous to the ring
$NT_Gamma lr((K))$. Let $Gamma$ be arbitrary chain with fixed antiisometries $'$
on any chain. We form new chain $tilde(Gamma) = Gamma' union Gamma$ where
$i' < j$ at $i,j in Gamma$. Further, we extend $'$ to the antiisometry of chain
$tilde(Gamma)$, if suppose $i'' = i$ $(i in Gamma)$. Define $K$-modulus
$NB_Gamma lr((K))$ with basis
${e_(i m) | i in Gamma, m in tilde(Gamma), i' < m < i}$, when intersection
$Gamma inter Gamma'$ is not empty and hence it contains the sole element which
is denoted by $0$ $(= 0')$. If intersection $Gamma inter Gamma'$ is empty, that
$K$-modulus with the same basis we denote by $ND_Gamma lr((K))$, while that with
basis ${e_(i m) | i in Gamma, m in tilde(Gamma), i' <= m < i}$ — by
$NC_Gamma lr((K))$. The constructed $K$-moduli $NG(K)$ are transformed into Lie
$K$-algebras, if products of their basic elements
#source(13, printed: 239)
are defined by the rule:
$
  e_(i j) * e_(j m) = e_(i m), quad e_(i m) * e_(j k) = 0
  quad (m != j, i != k, k != m');
$
$
  e_(j m) * e_(i m') = e_(i j') quad (j' < m < j < i), quad
  e_(i m) * e_(i m') = 0 quad (G = B_Gamma,D_Gamma);
$
$
  e_(i 0) * e_(j 0) = 2e_(i j') quad (G = B_Gamma), quad
  e_(i j) * e_(i j') = 2e_(i i') quad (G = C_Gamma), i > j in Gamma;
$
$
  e_(j k) * e_(i k') = e_(i k) * e_(j k') = e_(i j')
  quad (G = C_Gamma), i > j > k in Gamma.
$
It is necessary to note only, that for finite chain $Gamma$, with the accuracy
to isomorphisms, we ought to have either $Gamma = {0,1,2,dots,n}$,
$NB_Gamma lr((K)) approx NB_n lr((K))$, or $Gamma = {1,2,dots,n}$,
$ND_Gamma lr((K)) approx ND_n lr((K))$, $NC_Gamma lr((K)) approx NC_n lr((K))$;
in all cases $m' = -m$.

Further. Every finite subset of algebra $NG(K)$, for example, of type
$G = B_Gamma$ lies in subalgebra $NB_(Gamma_1) lr((K))$, where $Gamma_1$ is
finite subchain of $Gamma$. Therefore a group operation $compose$ on $N Phi(K)$
naturally transferred onto $NG(K)$, $G = B_Gamma,C_Gamma,D_Gamma$ too, in the
case of arbitrary chain $Gamma$. Main relations in the group
$angle.l NG(K), compose angle.r$ are composed of those
$x e_(i m) compose y e_(i m) = (x+y)e_(i m)$ $(x,y in K)$, and also the
following commutator relations obtained by transferring the commutator Chevalley
formula:
$ [x e_(i j),y e_(j m)] = x y e_(i m), quad m != 0, m != j'; $
$ [x e_(i m),y e_(j k)] = 0, quad i != k, k != m', m != j; $
$
  [x e_(j m),y e_(i m')] = cases(
    x y e_(i j') comma m != 0 comma i > j,
    0 comma i = j,
  ) quad (G = B_Gamma,D_Gamma);
$
$
  [x e_(i 0),y e_(j 0)] = 2x y e_(i j'), quad
  [x e_(i j),y e_(j 0)] = x y e_(i 0) + x y^2 e_(i j'),
  quad i > j quad (G = B_Gamma);
$
$
  [x e_(i j),y e_(i j')] = 2x y e_(i i'), quad
  [x e_(i j),y e_(j j')] = x y e_(i j') - x^2 y e_(i i'),
$ <pass:l1992-chevalley-symplectic-commutators>
#source(14, printed: 240)
$
  [x e_(i k),y e_(j k')] = [x e_(j k),y e_(i k')] = x y e_(i j'),
  quad i > j > k in Gamma quad (G = C_Gamma).
$

#theorem[
  Let $K$ is field of characteristic $!= 2$, $Gamma$ is an arbitrary chain. Then
  the class of all ideals of Lie ring $NG(K)$, $G = B_Gamma,C_Gamma,D_Gamma$,
  coincides with class of all normal subgroups of group
  $angle.l NG(K), compose angle.r$.
] <th:l1992-chevalley-infinite-classical-normal-lie>

It can be shown that statement of Theorem
@th:l1992-chevalley-infinite-classical-normal-lie is not implemented, if
characteristic of field $K$ is equal to 2.
