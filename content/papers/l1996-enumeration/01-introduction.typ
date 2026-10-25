#import "../../collection.typ": article-introduction, paper-abstract
#import "defs.typ": *

#source(1, printed: 49)
#paper-abstract(language: "en")[
  The number of different characteristic subgroups of the classic-type group
  $U G(K)$ over a field $K$ and that of normal $D$-invariant ($D$ is the set of
  diagonal automorphisms) subgroups of the same group are given.
]

#article-introduction(
  number: 1,
)[Introduction] <sec:l1996-enumeration-introduction>

Throughout the paper, $K$ stands for a field of order $> 2$. As in
[@bib:l1996-enumeration-Levchuk1990], $U G(K)$ denotes the maximal unipotent
subgroup of a Lie-type group $G$ over $K$. The main result of the paper cited is
formulated as follows:

#theorem[
  The number $c(G,K)$ of characteristic subgroups of the classic-type group
  $U G(K)$ over a field $K$ of order $> 2$ is equal to:
  $ binom(n, floor(n/2)) quad "for" G = A_(n-1) "or" ""^2 A_(n-1), n > 1; $
  $
    binom(2n, n) quad "for" G = B_n (n > 3, 2K = K), "or"
    C_n (n >= 2, 3K = 0, abs(K) > 3), "or"
    D_(n+1) (n > 3), "or" ""^2 D_(n+1) (n >= 3, abs(K) > 4);
  $
  $ 4^(n-1) + binom(2n-1, n) quad "for" 2K = 0, G = B_n "or" C_n, n >= 2; $
  $ binom(2n, n) - 1 quad "for" G = C_n, 6K = K; $
  $ binom(2n, n) - 2 quad "for" G = C_n, n > 2 (abs(K) = 3). $
] <th:l1996-enumeration-characteristic-count>

#source(2, printed: 50)The problem of estimating the number of different
subgroups of a group has already been studied. For example, an estimate for the
number of fixed-order subgroups of a finite $p$-group is well known
(G.~Frobenius, Ph.~Hall, et al.)

Note that, for $U G(K)$, the enumeration of characteristic subgroups is closely
connected with that of normal subgroups invariant with respect to the subgroup
$D$ of all diagonal automorphisms. For $G = A_(n-1)$ ($abs(K) > 2$), the number
$d(G,K)$ of such subgroups was determined out by G.~P.~Egorychev
[@bib:l1996-enumeration-Egorychev1989, Theorem 2.1.2] and B.~A.~Tolasov
[@bib:l1996-enumeration-Tolasov1977]. The results are based on the description
[@bib:l1996-enumeration-Levchuk1974, Section~@sec:l1974-normal-subgroups] of
$D$-invariant normal subgroups of the unitriangular group $upright(U T)(n,K)$.
The latter is isomorphic to the adjoint group of the ring $NT(n, K)$ of
niltriangular matrices. The class of all $D$-invariant normal subgroups of the
adjoint group coincides with the class of all $D$-invariant ideals in the ring
$NT(n, K)$ and the associated Lie ring (see [@bib:l1996-enumeration-Levchuk1992,
Theorem~@th:l1992-chevalley-unitriangular-normal-lie]).

By analogy with the case of $G = A_(n-1)$ in Chevalley $K$-algebra of arbitrary
type $Phi$ (see, for example, [@bib:l1996-enumeration-Carter1972, Section 4.4;
@bib:l1996-enumeration-Hurley1969]), we select a subalgebra $N Phi lr((K))$,
whose basis is formed by elements $e_r$ of Chevalley basis relative to positive
roots $r in Phi^+$. In [@bib:l1996-enumeration-Levchuk1990,
@bib:l1996-enumeration-Levchuk1992] the group $U Phi lr((K))$ is treated as the
adjoint group of the Lie ring $N Phi lr((K))$.

The number $d(G,K)$ is determined in Theorem~@th:l1996-enumeration-normal-count.
The number $d(Phi,K)$ is also found in the paper, including the most difficult
case $p(Phi)!K = 0$; here $p(Phi)$ is defined as maximal ratio
$lr((r,r)) / lr((s,s))$, $(r,s in Phi)$.

This investigation is also interesting as an example of direct enumeration,
where modern methods of calculation of combinatorial sums had to be involved for
obtaining the answer in closed form.

Some results of this paper were announced in
[@bib:l1996-enumeration-Egorychev1993], where the list of the subgroups of
groups $U G(K)$ of small Lie ranks was presented.
