#import "defs.typ": *

=== Several problems of ideal enumeration <sec:l2001-enumeration-problems>

As in §~@sec:l2001-enumeration-construction, let’s choose a subalgebra
$T(r_1,dots,r_m)$ in algebra $N Phi lr((K))$ of classical type $Phi$. It is
characterized by $m$-staged steplines $L$ in the corresponding $Phi^+$-matrix
(see Fig.~@fig:l2001-enumeration-stepline); by definition, $abs(L)=m$. A
subalgebra is denoted $T'(r_1,dots,r_m)$ if its basis formed by elements $e_r$
of the Chevalley basis under the condition $r_i < r$ even if for one
$1 <= i <= m$. Then
$
  H(L,S) = T'(r_1,dots,r_m)
  + {a_1 e_(r_1)+dots+a_m e_(r_m) | (a_1,a_2,dots,a_m) in S}
$
is ideal of Lie algebra (analogously Lie ring) $N Phi lr((K))$ for each
$K$-linear subspace $S$ (respectively additive subgroup) of the space $K^m$ of
$m$-length lines over the field $K$.

#problem[
  Find the number $alpha(Phi, q)$ (analogously $alpha_(R)(Phi,q)$) of all ideals
  of the form $H(L,S)$ of Lie algebra (respectively ring) $N Phi lr((K))$ of
  classical type $Phi$ over the finite field $K=GF(q)$.
] <pr:l2001-enumeration-boundary-ideals>

Note that description of all ideals of Lie ring $N Phi lr((K))$ over the field
$K$ has been obtained in [@bib:l2001-enumeration-Levchuk1976] for $Phi$ being of
type $A_n$ and in [@bib:l2001-enumeration-Levchuk1992] when $K=2K$, $Phi$ is of
type $B_n$, $C_n$ or $D_n$. Also there the bijective correspondence has been
established between a class of all ideals of Lie ring $N Phi lr((K))$ for
above-pointed cases and a class of all normal subgroups of group
$U Phi lr((K))$. Naturally arises

#problem[
  Find the number of all ideals of a Lie algebra (ring) $N Phi lr((K))$ of
  classical type $Phi$ over the finite field $K$.
] <pr:l2001-enumeration-all-ideals>

Let’s consider Problem~@pr:l2001-enumeration-boundary-ideals more explicitly. An
additive subgroup $S subset K^m$ is called $m$-proper if, for each number $i$,
$1 <= i <= m$, an element of $S$ exists with non-zero $i$-th coordinate.
Evidently the different ideals correspond to different pairs $(L,S)$ with
$abs(L)$-proper additive subgroup (subspace) $S$, and this correspondence is
bijective. Let $B(m,Phi)$ be the number of all $m$-staged steplines $L$ in
$Phi^+$-matrix, and $Q(m,q)$ and $Q_(R)(m,q)$ the numbers of all $m$-proper
subspaces and respectively of additive subgroups in $GF(q^m)$. For $Phi$ of
types $A_n$, $B_n$ or $C_n$ the relations are obtained
$
  alpha(Phi, q) = 1+sum_(m=1)^n B(m,Phi) dot Q(m,q),
$ <eq:l2001-enumeration-linear-ideal-count>
$
  alpha_(R)(Phi,q) = 1+sum_(m=1)^n B(m,Phi) dot Q_(R)(m,q).
$ <eq:l2001-enumeration-additive-ideal-count>

Using $q$-binomial coefficients
$
  lr([mat(m; k; delim: #none)])_q
  = ((q^m-1)(q^m-q)dots(q^m-q^(k-1)))/
  ((q^k-1)(q^k-q)dots(q^k-q^(k-1)))
$

#source(14, printed: 33)one can pre-assign the numbers $Q(m,q)$ recurrently:
$
  sum_(j=1)^m binom(m, j)Q(j,q)
  = sum_(k=1)^m lr([mat(m; k; delim: #none)])_q.
$ <eq:l2001-enumeration-proper-subspace-recurrence>

Numbers $Q_(R)(m,q)$ can be described analogously.

When $Phi$ is of type $A_(n-1)$, the Lie ring $N Phi lr((K))$ is isomorphic to
that associated with ring $NT_(n)(K)$ of (lower) nil-triangular
$n times n$-matrices over $K$. According to Theorem~9
[@bib:l2001-enumeration-Dubisch1951], ideals of form $H(L,S)$, including the
zero ideal, and only these, are the ideals of the associative algebra
$NT_(n)(K)$ over field $K$. Exactly the same ideals of form $H(L,S)$ owing to
[@bib:l2001-enumeration-Levchuk1976], §~2, exhaust all ideals of ring
$NT_(n)(K)$ and therefore the number of these when $K=GF(q)$ coincides with
$alpha_(R)(A_(n-1),q)$. The formula (2.36)
[@bib:l2001-enumeration-Egorychev1989] gives a clear expression for numbers
$B(m,n)=B(m,A_(n-1))$. Therefore we obtained the combinatorial description of
numbers $alpha(A_(n-1), q)$ and $alpha_(R)(A_(n-1),q)$.

#theorem[
  Let $K=GF(q)$ and let numbers $Q(m,q)$ are pre-assigned by recurrence relation
  @eq:l2001-enumeration-proper-subspace-recurrence. Then the number of ideals of
  the algebra $NT_(n)(K)$ is equal to
  $
    1+1/n sum_(m=1)^(n-1) binom(n, m)binom(n, m+1)Q(m,q).
  $
] <th:l2001-enumeration-niltriangular-ideals>

The number of ideals of a Lie ring (as well as Lie algebra) $N Phi lr((K))$ of
classical type $Phi$ over $K=GF(q)$ can be represented analogously; a
description of ideals for these cases is given by Theorem~2
[@bib:l2001-enumeration-Levchuk1976] and Theorem~9
[@bib:l2001-enumeration-Levchuk1992].

Finally, let $K$ be an associative ring with identity, and let $R_(n)(K,J)$ be
the ring of all $n times n$ matrices over $K$ with elements from an ideal $J$ on
and above the main diagonal. All ideals of the ring $R_(n)(K,J)$ are described
for $K=ZZ_(p^m)$, $m >= 1$, and $J=(p)$ ($p$ is a prime) and in some another
cases. Evidently, $R_(n)(K,0)=NT_(n)(K)$. It seems that methods given in this
paper can be extended to enumeration, in particularly, of all ideals of the ring
$R_(n)(ZZ_(p^m),(p))$.
