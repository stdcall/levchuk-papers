#import "../../main-defs.typ": *
#import "../../statements.typ": *
#import "defs.typ": *

#source(5, printed: "1250140-5")In particular, for $s=2$ every nonzero ideal
@eq:l2013-ideals-coordinate-ideal of the ring $R_n lr((K,J))$ is either an ideal
$I(K,Lc,Lc')$ or $I(J^(s-1),Lc,Lc')$ and, consequently,
$ Omega(n, 2)=Omega^+(n)+Omega^0(n)+1. $
For ideals @eq:l2013-ideals-coordinate-ideal in remaining cases at $s>=3$ we may
choose the ideal $T$ exactly by $s-2$ possibilities $T=J^m$ with
$m=1,2,dots,s-2$. For the enumeration we use the number $Omega(n)$ of all sets
of corners $(Lc,Lc')$ of degree $n$.

We now obtain the following theorem.

#theorem[
  Let $K$ be a local ring with a principal maximal ideal $J$ which is nilpotent
  of degree $s$ and let $|K slash J|>2$. Then the number of all coordinate
  ideals of the ring $R_n lr((K,J))$ ($n>=2$) is a function $Omega(n, s)$ from
  the numbers $n,s$ such that
  $
    Omega(n, 1)=frac(1, n) binom(2n, n-1),
    quad Omega(n, s)=(s-2)Omega(n)+Omega^+(n)+Omega^0(n)+1, quad s>1.
  $
] <th:l2013-ideals-count-decomposition>

In the next sections we find the numbers $Omega^0(n)$, $Omega^+(n)$ and
$Omega(n)$. Note that the number $Omega(n, 1)$ (i.e. when $s=1$, $J=0$ and $K$
is a field) is found [@bib:l2013-ideals-Egorychev1989, Theorem~2.1.2].

#example[
  Consider the case $n=2$. Since four cases (according to each matrix position)
  of $Lc$ with a unique corner and, in addition, the case $Lc={(1,1),(2,2)}$
  exhaust all opportunities of choice of staircases
  @eq:l2013-ideals-primary-corners, $Omega^0(2)=5$. Also, we have
  $
    Omega^+(2)=|{({(2,1)},{(1,1),(2,2)}),({(2,1)},{(1,1),(1,2),(2,2)})}|=2,
  $
  $
    Omega(2)=|{({(1,1),(2,2)},Lc'),({(1,1)},Lc'),({(2,2)},Lc'),({(1,2)},Lc')}|
    +Omega^+(2)=6,
  $
  where $Lc'$ is uniquely determined by choosing $Lc$ for each pair $(Lc,Lc')$.
  Therefore $Omega(2, s)=6s-4$ for all $s>=1$ and $Omega(2, s)=2$ for the case
  $s=1$, i.e. $J=0$.
] <exm:l2013-ideals-two-by-two>

=== #[Enumeration of the Diagonal Paths on a Rectangular Lattice]
<sec:l2013-ideals-diagonal-paths>

We shall use the combinatorial scheme [@bib:l2013-ideals-Feller1971] of
enumeration for diagonal paths on a rectangular lattice and the general approach
to computation of combinatorial sums [@bib:l2013-ideals-Egorychev1989] which is
based on the definition and properties of the $res$ operator with operations of
Laurent formal power series.

Note that each sequence ${(i_1,j_1),(i_2,j_2),dots,(i_r,j_r)}$ of $Lc$ type of
length $r>=1$ (analogously of $Lc'$ type) is in one-to-one correspondence with
the increasing path $(i_1,j_1),(i_2,j_2),dots,(i_r,j_r)$ with the $r-1$ diagonal
steps on a rectangular lattice from $(i_1,j_1)$ to $(i_r,j_r)$, see
Fig.~@fig:l2013-ideals-staircases.

Let $Lc(i, j)$ ($i,j in {1,dots,n}$) be the set of all sequences of $Lc$ type of
arbitrary length $r>=1$, which have $i_1=i$, $j_r=j$. Let #source(
  6,
  printed: "1250140-6",
)$Lc'(i,j)$, $i,j in {1,dots,n}$, be the set of all secondary staircases between
the boundary points $(1,j)$ and $(i,n)$, including the staircase with no
additional corner. By definition of the number $Omega(n)$, we have
$ Omega(n)=sum_(i=1)^n sum_(j=1)^n |Lc(i, j)| dot |Lc'(i,j)|. $
<eq:l2013-ideals-corner-sum>

Denote by $Lc_r lr((i,j))$ the set of all sequences of $Lc$ type of fixed length
$r>=1$, which have $i_1=i$, $j_r=j$. Let $Lc'_q lr((i,j))$, $i,j in {1,dots,n}$,
be the set of secondary staircases with exactly $q>=0$ additional corners,
excluding the two boundary points. In calculation of the sum
@eq:l2013-ideals-corner-sum we will also find the following sums:
$
  sum_(i=1)^n sum_(j=1)^n |Lc_r lr((i,j))| dot |Lc'(i,j)|,
  quad sum_(i=1)^n sum_(j=1)^n |Lc(i, j)| dot |Lc'_q lr((i,j))|,
  quad sum_(i=1)^n sum_(j=1)^n |Lc_r lr((i,j))| dot |Lc'_q lr((i,j))|.
$
For each increasing path with $r$ steps from the origin $(0,0)$ to a fixed point
$(p,q)$ there exists a one-to-one correspondence with pairs of $r$-partitions of
$p$ and $q$ with nonempty parts. We now obtain the following known Lemmas
@lem:l2013-ideals-origin-paths–@lem:l2013-ideals-total-translated-paths
[@bib:l2013-ideals-Feller1971].

#lemma[
  Let $N_(r,p,q)$ be the number of increasing diagonal $r$-step paths ($r>=0$)
  on a rectangular lattice from $(0,0)$ to $(p,q)$. Then $N_(0,0,0)=1$,
  $N_(r,0,0)=0$ for $r>0$, and
  $ N_(r,p,q)=binom(p-1, r-1)binom(q-1, r-1) quad (p>=1,q>=1,r>=1). $
] <lem:l2013-ideals-origin-paths>

#lemma[
  The number $N_r lr(((s,t),(p,q)))$ of increasing paths on a rectangular
  lattice with a fixed number of steps $r>=0$ from $(s,t)$ to $(p,q)$,
  $p>=s>=0$, $q>=t>=0$, is equal to 1 if $r=0$, $s=p$, $t=q$, and
  $
    N_r lr(((s,t),(p,q)))=binom(p-s-1, r-1)binom(q-t-1, r-1),
    quad p-s>=r, quad q-t>=r, quad r>=1.
  $ <eq:l2013-ideals-fixed-step-paths>
] <lem:l2013-ideals-translated-paths>

#lemma[
  The number of increasing diagonal $r$-step paths on a rectangular lattice from
  $(0,0)$ to a fixed point $(p,q)$ for all $r>=1$ is equal to
  $ sum_(r>=1) N_(r,p,q)=binom(p+q-2, p-1) quad (p>=1,q>=1). $
] <lem:l2013-ideals-total-origin-paths>

#lemma[
  The number $N((s,t),(p,q))$ of increasing diagonal paths on a rectangular
  lattice from $(s,t)$ to $(p,q)$, $p>=s>=0$, $q>=t>=0$, is equal to 1 if $s=p$,
  $t=q$, and also
  $ N((s,t),(p,q))=binom(p+q-s-t-2, p-s-1) quad (p>s,q>t). $
  <eq:l2013-ideals-all-step-paths>
] <lem:l2013-ideals-total-translated-paths>

#source(7, printed: "1250140-7")We now apply the coefficients method of
summation from [@bib:l2013-ideals-Egorychev1996] to the equality
@eq:l2013-ideals-corner-sum.

#lemma[
  Let $i,j,r in {1,dots,n}$. Then
  $
    |Lc(i, j)|=binom(n-i+j-1, n-i), quad
    |Lc_r lr((i,j))|=binom(n-i, r-1)binom(j-1, r-1).
  $
] <lem:l2013-ideals-primary-staircase-count>

#proof[
  It is clear that
  $
    |Lc(i, j)|=1+sum_(s=1)^(j-1) sum_(t=i+1)^n N((i,s),(t,j))
    =1+sum_(s,t) binom(j-s+t-i-2, t-i-1),
  $
  where 1 corresponds to the single path with zero steps from $(i,j)$ to the
  same point, and the numbers $N((i,s),(t,j))$ are defined by
  @eq:l2013-ideals-all-step-paths with coordinate increments $t-i$ and $j-s$.
  Using the representation of a binomial coefficient by the $res$ operator, we
  have
  $ |Lc(i, j)|=1+sum_(s,t) res_x {(1-x)^(-j+s)x^(-t+i)} $
  $ =1+res_x {(1-x)^(-j)x^i lr((sum_(s,t)(1-x)^s x^(-t)))} $
  $
    =1+res_x {(1-x)^(-j)x^i lr(((1-x)-(1-x)^j)) (1-(1-x))^(-1)
      lr((x^(-i-1)-x^(-n-1)))(1-x^(-1))^(-1)}
  $
  $
    =1+res_x {-(1-x)^(-j)x^(-1)+(1-x)^(-1)x^(-1)
      +(1-x)^(-j)x^(-n+i-1)-(1-x)^(-1)x^(-n+i-1)}
  $
  $ =1-1+1+binom(n-i+j-1, n-i)-1=binom(n-i+j-1, n-i). $
  The second equality of the lemma can be proved analogously taking into account
  @eq:l2013-ideals-fixed-step-paths.
]

#lemma[
  Let $i,j in {1,dots,n}$, $q>=0$. Then
  $
    |Lc'(i,j)|=binom(i-1+n-j, n-j), quad
    |Lc'_q lr((i,j))|=binom(n-j, q)binom(i-1, q).
  $
] <lem:l2013-ideals-secondary-staircase-count>

#proof[
  The additional corners of a secondary staircase are obtained by choosing $q$
  row indices in ${1,dots,i-1}$ and $q$ column indices in ${j+1,dots,n}$, both
  in increasing order. Hence their number is $binom(i-1, q)binom(n-j, q)$.
  Summing over $q>=0$ and applying the binomial convolution gives
  $binom(i-1+n-j, n-j)$. The term $q=0$ corresponds to no additional corner. If
  $i=1$ or $j=n$, it is the only term, and $|Lc'(i,j)|=1$.
]
