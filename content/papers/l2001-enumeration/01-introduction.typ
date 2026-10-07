#import "../../collection.typ": paper-abstract, paper-keywords
#import "defs.typ": *

#source(1, printed: 20)

#paper-abstract(language: "en")[
  We consider the maximal nilpotent subalgebra $N Phi lr((K))$ of the Chevalley
  algebra of the type $Phi$ over an arbitrary field $K$. Our purpose is
  enumeration of ideals of $N Phi lr((K))$ that are invariant under the subgroup
  $D$ of all diagonal automorphisms. Connections between ideals of
  $N Phi lr((K))$ and normal subgroups of the unipotent subgroup of the
  Chevalley group of the type $Phi$ over $K$ are used. Finally, we use methods
  of integral representation of sums and of listing lattice paths. We also
  discuss some other problems of the enumeration of ideals.
]

=== Introduction <sec:l2001-enumeration-introduction>

Let $Phi$ be an indecomposable root system. Consider the Chevalley algebra of
the type $Phi$ over an arbitrary field $K$, cf. R.~Carter
[@bib:l2001-enumeration-Carter1972, §~4.4] and J.~Hurley
[@bib:l2001-enumeration-Hurley1969]. Its maximal nilpotent subalgebra
$N Phi lr((K))$ has a basis which is formed by elements $e_r$ ($r in Phi^+$) of
the Chevalley basis. Our purpose is the enumeration of ideals of algebra
$N Phi lr((K))$ that are invariant under the subgroups $D$ of all diagonal
automorphisms.

The unipotent subgroup $U Phi lr((K))$ of the Chevalley group of the type $Phi$
over $K$ is treated in [@bib:l2001-enumeration-Levchuk1990] as the adjoint group
of the algebra $N Phi lr((K))$. Denote by $c(Phi; K)$, the number of all
characteristic subgroups of the group $U Phi lr((K))$, and by $d(Phi; K)$, the
number of all $D$-invariant normal subgroups of $U Phi lr((K))$. Continuing
[@bib:l2001-enumeration-Egorychev1993], [@bib:l2001-enumeration-Egorychev1996],
we investigate the number $Lambda(Phi; K)$ of all $D$-invariant ideals of the
algebra $N Phi lr((K))$ together with the numbers $c(Phi; K)$ and $d(Phi; K)$.

The highest-dimension commutative subalgebras of the complex algebra
$N Phi lr((CC))$ (having used another terminology) and hence of the semi-simple
complex Lie algebras and also the highest-dimension commutative subgroups of the
semi-simple complex Lie groups, were enumerated by A.~I.~Mal’cev
[@bib:l2001-enumeration-Malcev1945]. Problems of estimating the number of
different subgroups in groups have been considered for a long time. The
estimates for the number of Sylow subgroups, the number of fixed-order subgroups
in a finite $p$-group (G.~Frobenius, Ph.~Hall, et. al.) are well known. The
numbers $c(Phi; K)$, $d(Phi; K)$ and ones for twisted types were found in
[@bib:l2001-enumeration-Egorychev1993] and
[@bib:l2001-enumeration-Egorychev1996] (cf. theorems
@th:l2001-enumeration-characteristic-count and
@th:l2001-enumeration-normal-count in §~@sec:l2001-enumeration-construction
below); the case $Phi = A_(n-1)$ see also [@bib:l2001-enumeration-Egorychev1989,
theorem 2.1.2] and [@bib:l2001-enumeration-Tolasov1977].

#source(2, printed: 21)For calculating the number $Lambda(Phi; K)$ at
$char K != 2$ it is useful to see its connection with number $d(Phi; K)$, due to
the known correspondence of normal subgroups and ideals, cf.
[@bib:l2001-enumeration-Levchuk1976] and [@bib:l2001-enumeration-Levchuk1992].
Exceptional cases are investigated in detail in the paper. Our main result is
the following theorem.

#theorem[
  The number $Lambda(Phi; K)$ of all $D$-invariant ideals of the algebra
  $N Phi lr((K))$ of classical type over a field $K$ of an order greater then 2
  is equal to
  $
    1/n binom(2n, n - 1) quad "at" Phi = A_(n-1), n > 1;
  $
  $
    binom(2n - 1, n) + binom(2n - 2, n) quad "at" Phi = D_n, n > 2;
  $
  $
    binom(2n, n) quad "at" K = 2K, Phi = B_n "or" C_n, n > 1;
  $
  and $Lambda(C_1; K) = 2$. If $2K = 0$, then
  $
    Lambda(C_n; K) = 9 Lambda(C_(n-1); K)
    - 1/n binom(2n - 2, n - 1) 2^(n+1)
    = sum_(i=1)^n 2^(n-i+1) i/n binom(2n, n - i), quad n >= 2;
  $
  $
    Lambda(B_n; K) = 3 dot 4^(n-1)
    - 2 frac((2n - 2)!, (n - 1)! (n + 1)!) (n^2 - n + 1), quad n >= 1.
  $
] <th:l2001-enumeration-ideal-count>

The proof of this theorem is reduced in §~@sec:l2001-enumeration-construction to
a pure combinatorial task. Its solution is obtained in
§~@sec:l2001-enumeration-lattice-paths and
§~@sec:l2001-enumeration-integral-sums, using methods of integral representation
of sums [@bib:l2001-enumeration-Egorychev1989] and of listing lattice paths.
Some other enumeration problems are discussed in
§~@sec:l2001-enumeration-problems.
