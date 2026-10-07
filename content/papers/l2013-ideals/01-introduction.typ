#import "../../collection.typ": paper-abstract, paper-keywords
#import "../../main-defs.typ": *
#import "../../statements.typ": *
#import "../../collection.typ": article-introduction
#import "defs.typ": *

#source(1, printed: "1250140-1")

#paper-abstract(language: "en")[
  Using the method of integral representation of combinatorial sums we enumerate
  ideals of certain nilpotent matrix rings.
]

#paper-keywords(language: "en")[
  Nilpotent matrix rings; enumeration of ideals; computation of combinatorial
  sums.
]

#article-introduction[Introduction] <sec:l2013-ideals-introduction>

Enumerative combinatorial problems in algebra and geometry have been considered
for a long time: the well-known estimates for the number of fixed-order
subgroups in a finite $p$-group (G. Frobenius, Ph. Hall etc.), the ranks of the
lower central series of free groups (see [@bib:l2013-ideals-Gorchakov1972;
@bib:l2013-ideals-Kourovka2007, Question~2.18]). When $K$ is a field or skew
field of an order $>2$, all normal subgroups of the unitriangular group over $K$
that are invariant under the subgroup $D$ of all diagonal automorphisms are
enumerated in [@bib:l2013-ideals-Egorychev1989, Theorem~2.1.2;
@bib:l2013-ideals-Levchuk1974] (see also [@bib:l2013-ideals-Tolasov1977]).
According to [@bib:l2013-ideals-Levchuk2002], this also enumerates all
$D$-invariant ideals and Lie ideals of the $K$-algebra $NT(n, K)$ of all
niltriangular $n times n$ matrices, cf. [@bib:l2013-ideals-Dubisch1951].

#source(2, printed: "1250140-2")In [@bib:l2013-ideals-Egorychev1996,
@bib:l2013-ideals-Egorychev2001, @bib:l2013-ideals-Levchuk1990] the enumeration
of characteristic subgroups of the unipotent subgroup of the classical linear
groups and $D$-invariant ideals of the nil-radical in the Chevalley algebra over
a field (see [@bib:l2013-ideals-Carter1972, §~4.4;
@bib:l2013-ideals-Hurley1969]) are developed by enumeration in
[@bib:l2013-ideals-Egorychev1989, @bib:l2013-ideals-Levchuk1974]. On the other
hand, the number of symmetric forms and quadrics of the projective space over a
local ring with nilpotent principal maximal ideal had been found in
[@bib:l2013-ideals-Egorychev2008, @bib:l2013-ideals-Levchuk2006]. The simple
formulas from [@bib:l2013-ideals-Egorychev1996, @bib:l2013-ideals-Egorychev2001,
@bib:l2013-ideals-Egorychev2008, @bib:l2013-ideals-Gorchakov1972] are achieved
using the integral representation method of combinatorial summation which is
developed in [@bib:l2013-ideals-Egorychev1989].

The present paper gives a new applications of the method
[@bib:l2013-ideals-Egorychev1989]. Let $R_n lr((K,J))$ be the ring of all
$n times n$ matrices over a ring $K$ with elements from an ideal $J$ of $K$ on
and above the main diagonal. (Thus, $R_n lr((K,0))=NT(n, K)$.) Ideals and
automorphisms of these rings are studied in [@bib:l2013-ideals-Kuzucuoglu2000,
@bib:l2013-ideals-Kuzucuoglu2001, @bib:l2013-ideals-Levchuk2005,
@bib:l2013-ideals-Levchuk2002, @bib:l2013-ideals-Suleimanova2005]. Our purpose
is to prove the following theorem.

#main-theorem[
  Let $K$ be a local ring with a principal maximal ideal $J$ of a nilpotent
  degree $s$ and $|K slash J|>2$. Then the number of all coordinate ideals of
  the ring $R_n lr((K,J))$ ($n>=2$) is a function $Omega(n, s)$ such that
  $
    Omega(n, 1)=frac(1, n) binom(2n, n-1),
  $
  $
    Omega(n, s)=(s-1)(2n-1)binom(2n-2, n-1)+binom(2n, n)-2^(2n-2), quad s>=2.
  $ <eq:l2013-ideals-main-count>
] <th:l2013-ideals-main-count>

The description of coordinate ideals and a combinatorial expression of the
number $Omega(n, s)$ is obtained in §~@sec:l2013-ideals-ring-ideals. We find the
number $Omega(n, s)$ in the closed form by using the properties of $res$
operator with operations of Laurent formal power series and applying general
approach [@bib:l2013-ideals-Egorychev1989] to computation of combinatorial sums.

See also Remark~@rem:l2013-ideals-noncommutative-coefficients and Questions
@pr:l2013-ideals-binary-field-question[A] and
@pr:l2013-ideals-classical-lie-question[B] in §~@sec:l2013-ideals-main-proof.

