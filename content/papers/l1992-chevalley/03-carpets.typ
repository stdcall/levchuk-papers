#import "../../main-defs.typ": *
#import "defs.typ": *
=== Elementary carpets <sec:l1992-chevalley-carpets>
The main theorems by Yu. I. Merzlyakov [@bib:l1992-chevalley-Merzlyakov1964],
Yu. V. Sosnovsky [@bib:l1992-chevalley-Sosnovsky1978] and H. Roloff
[@bib:l1992-chevalley-Roloff1982] use a carpet of ideals of degree $n$ over $K$
(i.e. a collection ${A_(i j) | 1 <= i,j <= n}$ with condition
$A_(i j) A_(j k) subset A_(i k)$) in which diagonal ideals are quasiregular. It
may be shown, that a subgroup defined by this carpet always has a decomposition
analogic to that (see, for example, proposition 2.3
[@bib:l1992-chevalley-AbeSuzuki1976]) of congruence subgroup by the modulus of
quasiregular ideal.

The subgroups of Theorem @th:l1992-chevalley-normal-commutators have an analogic
decomposition too, and also every subgroup
$E(carpet) = chevron.l x_r lr((A_r)) | r in Phi chevron.r$ of Chevalley group
$Phi(K)$, for which $carpet = {A_r | r in Phi}$ is an elementary carpet of
ideals of type $Phi$ over $K$ (see definition in
#source(6, printed: 232)
[@bib:l1992-chevalley-Kourovka1980, question 7.28]) and $A_r A_(-r)$
$(r in Phi)$ are quasiregular ideals.

Elementary carpet $carpet$ of type $Phi$ of additive subgroups of ring $K$ is
called as permissible, if
$ E(carpet) inter x_r lr((K)) = x_r lr((A_r)), quad r in Phi. $
The following theorem (see [@bib:l1992-chevalley-Levchuk1983Roots]) solves
partially the question: which conditions onto elementary carpet (in terms of its
elements) are necessary and sufficient for its permissibility? (See question
7.28 [@bib:l1992-chevalley-Kourovka1980]; see also
[@bib:l1992-chevalley-Suzuki1976], [@bib:l1992-chevalley-Levchuk1982] and the
references therein.) Note that for arbitrary carpet $carpet$ of type $Phi$ over
a field the set $Sigma(carpet) = {r in Phi | A_r A_(-r) != 0}$ is either empty
or a joining of pairly orthogonal indecomposable quasilocked root subsystems
$Sigma_1, Sigma_2, dots, Sigma_m$.

#theorem[
  For permissibility of elementary carpet $carpet$ of type $Phi$ of additive
  subgroups of locally finite field $K$ it is necessary and sufficient, that at
  non-empty $Sigma(carpet)$ the condition should be implemented: for each $i$,
  $1 <= i <= m$, and $r in Sigma_i$ we can find the subfield $P_i$ and element
  $t_r in K$ such as that $A_r = t_r P_i$, and if $Sigma_i = {r,-r}$, then
  either $t_r t_(-r) in P_i$ or $|P_i| = 3$, $(t_r t_(-r))^2 = -1$, or
  $|P_i| = 2$.
] <th:l1992-chevalley-permissible-carpets>
