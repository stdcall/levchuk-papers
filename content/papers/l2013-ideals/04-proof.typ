#import "../../main-defs.typ": *
#import "../../statements.typ": *
#import "defs.typ": *

=== Proof of Main Theorem <sec:l2013-ideals-main-proof>

#source(8, printed: "1250140-8")We now complete the proof of
@th:l2013-ideals-main-count[Main Theorem].

By definition, the number $Omega^0(n)$ is the number of all staircases $Lc$ in
@eq:l2013-ideals-primary-corners. Each staircase is determined in one-to-one
correspondence by a pair of increasing sequences $i_1,i_2,dots,i_r$ and
$j_1,j_2,dots,j_r$, $r>=1$. The number of such pairs is obviously
$binom(n, r)binom(n, r)$. It follows
$
  Omega^0(n)=sum_(r=1)^n binom(n, r)^2
  =-1+sum_(r=0)^n binom(n, r)^2=binom(2n, n)-1.
$

#lemma[
  The number of ideals @eq:l2013-ideals-coordinate-ideal with $J T=0$ and $T!=0$
  (i.e. $I(J^(s-1),Lc,Lc')$) is equal to
  $ Omega^0(n)=binom(2n, n)-1. $
] <lem:l2013-ideals-last-layer-count>

#theorem[
  The number of all sets of corners $(Lc,Lc')$ of degree $n$ is equal to
  $ Omega(n)=(2n-1)binom(2n-2, n-1). $
] <th:l2013-ideals-all-corners-count>

#proof[
  We use @eq:l2013-ideals-corner-sum and Lemmas
  @lem:l2013-ideals-primary-staircase-count and
  @lem:l2013-ideals-secondary-staircase-count. We get
  $ Omega(n)=sum_(i,j=1)^n binom(n-i+j-1, n-i)binom(i-1+n-j, n-j) $
  $
    =sum_(i,j=1)^n res_x lr(((1-x)^(-j)x^(-n+i-1)))
    res_y lr(((1-y)^(-i)y^(-n+j-1)))=sum_(i,j=1)^infinity dots
  $
  (if $i>n$ or $j>n$, added terms of the sum are zero by definition of the $res$
  operator)
  $
    =res_(x y) {(1-x)^(-1)(1-y)^(-1)(x y)^(-n-1)
      lr([sum_(i,j=1)^infinity {lr((x/(1-y)))^i} {lr((y/(1-x)))^j}])}
  $
  (twice using the formula for the sum of an infinite geometric progression)
  $
    =res_(x y) {(1-x)^(-1)(1-y)^(-1)(x y)^(-n)
      lr([(1-(x/(1-y)))^(-1)(1-(y/(1-x)))^(-1)])}
  $
  $ =res_(x y) {(1-x-y)^(-2)(x y)^(-n)} $
  $ =res_(x y) {lr([1+sum_(k=1)^infinity binom(k+1, k)(x+y)^k])(x y)^(-n)} $
  $
    =sum_(k=1)^infinity (k+1)res_(x y) {(x+y)^k (x y)^(-n)}
    =(k+1)res_(x y) {(x+y)^k (x y)^(-n)} |_(k=2(n-1))
  $
  (#source(9, printed: "1250140-9")if $k!=2(n-1)$, each term is zero by
  definition of the $res$ operator)
  $ =(2n-1)res_(x y) {(x+y)^(2n-2)(x y)^(-n)}=(2n-1)binom(2n-2, n-1). $
]

For the number studied by Davletshin [@bib:l2013-ideals-Davletshin2011, Main
Theorem], the restriction to positions below the diagonal gives the following
reflection count.

#theorem[
  The following equality is satisfied:
  $ Omega^+(n)=(2n-1)binom(2n-2, n-1)-2^(2n-2). $
] <th:l2013-ideals-strict-lower-corners-count>

#proof[
  A primary staircase with $i_1=i$ and $j_r=j$ is represented by a path from
  $(i,1)$ to $(n,j)$ whose steps increase either row or column by 1. Its corners
  are the points where a column run ends and a row run begins, including the
  boundary corners. There are $binom(n-i+j-1, n-i)$ such paths. All corners are
  below the diagonal exactly when the path stays below it. Reflecting the
  initial segment up to the first diagonal point transforms a path meeting the
  diagonal into a path from $(1,i)$ to $(n,j)$. Hence the number of admissible
  primary staircases is
  $ binom(n-i+j-1, n-i)-binom(n-i+j-1, j-i), $
  with the second term zero for $j<i$. Multiplying by the secondary count in
  Lemma @lem:l2013-ideals-secondary-staircase-count and summing gives
  $
    Omega(n)-Omega^+(n)
    =sum_(d=0)^(n-1) binom(n+d-1, d) sum_(i=1)^(n-d) binom(n-d-1, n-d-i)
    =sum_(d=0)^(n-1) binom(n+d-1, d)2^(n-d-1).
  $
  The last sum counts binary words of length $2n-1$ with at least $n$ ones,
  grouped by the position $n+d$ of the $n$th one. Exactly half of all words have
  this property, so the sum is $2^(2n-2)$. The result now follows from Theorem
  @th:l2013-ideals-all-corners-count.
]


Applying Theorems @th:l2013-ideals-count-decomposition,
@th:l2013-ideals-all-corners-count, @th:l2013-ideals-strict-lower-corners-count
and Lemma @lem:l2013-ideals-last-layer-count for $s>1$, we obtain
$ Omega(n, s)=(s-2)Omega(n)+Omega^+(n)+Omega^0(n)+1 $
$
  =(s-2)(2n-1)binom(2n-2, n-1)
  +lr([(2n-1)binom(2n-2, n-1)-2^(2n-2)])
  +lr([binom(2n, n)-1])+1.
$
It follows
$ Omega(n, s)=(s-1)(2n-1)binom(2n-2, n-1)+binom(2n, n)-2^(2n-2), quad s>=2. $
This completes the proof.

#remark[
  The generalized concept of Suleimanova [@bib:l2013-ideals-Suleimanova2005] of
  strongly maximal ideal allows one to generalize
  @th:l2013-ideals-main-count[Main Theorem] to certain noncommutative
  coefficient rings.
] <rem:l2013-ideals-noncommutative-coefficients>

Note that a subset of the ring $NT(n, K)$ is a Lie ideal if and only if it is a
normal subgroup of the adjoint group which is isomorphic to the unitriangular
group $UT(n, K)$ (see [@bib:l2013-ideals-Levchuk2002]). (In general, for the
radical ring $R_n lr((K,J))$ this correspondence is not satisfied.) When $K$ is
a field or skew field of order $>2$, all $D$-invariant Lie ideals of $NT(n, K)$
are ideals and, therefore, they are also enumerated by
[@bib:l2013-ideals-Egorychev1989, Theorem~2.1.2].

#question("A")([
  Find the number of all ideals of the algebra $NT(n, K)$ for the exceptional
  case $|K|=2$. (See also more general questions
  [@bib:l2013-ideals-Egorychev2001, Problems~1 and~2].)
]) <pr:l2013-ideals-binary-field-question>

Consider the Chevalley $K$-algebra $Lc(Phi, K)$ (similarly to
[@bib:l2013-ideals-Carter1972, §~4.4; @bib:l2013-ideals-Hurley1969]) associated
with a root system $Phi$. $D$-invariant ideals of its nil-radical
$N_Phi lr((K))$ had been #source(10, printed: "1250140-10")enumerated in
[@bib:l2013-ideals-Egorychev1996, @bib:l2013-ideals-Egorychev2001,
@bib:l2013-ideals-Levchuk1990], when $K$ is a field of order $>2$. The product
$N_Phi lr((K)) dot Lc(Phi, K, J)$ of the nil-radical and the
congruence-subalgebra of level $J$ in $Lc(Phi, K)$ generalizes the Lie algebra
$R_n lr((K,J))$ of Lie type $A_(n-1)$.

#question("B")([
  Under the restrictions of @th:l2013-ideals-main-count[Main Theorem] find the
  number of all $D$-invariant ideals of the algebra
  $N_Phi lr((K)) Lc(Phi, K, J)$ of the classical Lie type.
]) <pr:l2013-ideals-classical-lie-question>
