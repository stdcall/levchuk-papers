#import "defs.typ": *

=== Computation of combinatorial sums <sec:l2001-enumeration-integral-sums>

Later on we will use the method of coefficients.

==== #[
  #source(8, printed: 27)Formula for $Lambda_(n)(C_n;K)$
] <ss:l2001-enumeration-c-integrals>

#lemma[
  Let a sequence of members ${Lambda_n}_1^infinity$ be given by formula
  @eq:l2001-enumeration-c-binomial-sum. Then the recurrence formula holds
  $
    Lambda_n = 9 Lambda_(n-1) - 1/n binom(2n-2, n-1) 2^(n+1),
    quad n >= 2; quad Lambda_1 = 2.
  $ <eq:l2001-enumeration-c-recurrence>
] <lem:l2001-enumeration-c-recurrence>

#proof[
  We first write the integral representation for numbers $i/n binom(2n, n-i)$:
  $
    i/n binom(2n, n-i) = binom(2n, n-i) - 2 binom(2n-1, n-i-1)
    = 1/(2 pi upright(i)) integral_(abs(x)=rho)
    (1+x)^(2n) x^(-n+i-1) dif x
    - 2/(2 pi upright(i)) integral_(abs(x)=rho)
    (1+x)^(2n-1) x^(-n+i) dif x
    = 1/(2 pi upright(i)) integral_(abs(x)=rho)
    (1+x)^(2n-1) (1-x) x^(-n+i-1) dif x, quad rho > 0.
  $ <eq:l2001-enumeration-c-coefficient-integral>

  If we substitute this integral representation for numbers $i/n binom(2n, n-i)$
  under the summation sign in formula @eq:l2001-enumeration-c-binomial-sum for
  $Lambda_n$, then we’ll have
  $
    Lambda_n = sum_(i=1)^n 2^(n-i+1) 1/(2 pi upright(i))
    integral_(abs(x)=rho) (1+x)^(2n-1) (1-x) x^(-n+i-1) dif x
    = sum_(i=0)^infinity dots
  $
  (as added numbers of sum obviously are equal to 0)
  $
    = 2^(n+1)/(2 pi upright(i)) integral_(abs(x)=rho)
    (1+x)^(2n-1) (1-x)
    lr((sum_(i=0)^infinity (x/2)^i)) x^(-n-1) dif x
    = 2^(n+1)/(2 pi upright(i)) integral_(abs(x)=rho)
    (1+x)^(2n-1) (1-x) (1-x/2)^(-1) x^(-n-1) dif x
  $
  (the substitution $z=x/(2(1+x)^2):0 arrow.r 0$)
  $
    = 1/(2 pi upright(i)) integral_(abs(z)=0.1)
    [(1-12z)+(1-8z)^(1/2)] (1-9z)^(-1) z^(-n-1) dif z.
  $
  From the last formula follows @eq:l2001-enumeration-c-recurrence. Really,
  $
    Lambda_n = 1/(2 pi upright(i)) integral_(abs(z)=0.1)
    ((1-12z)+(1-8z)^(1/2))/((1-9z)z^(n+1)) (1-9z+9z) dif z
    = 1/(2 pi upright(i)) integral_(abs(z)=0.1)
    [(1-12z)+(1-8z)^(1/2)] z^(-n-1) dif z
    + 9 Lambda_(n-1)
    = 9 Lambda_(n-1) - 1/n binom(2n-2, n-1) 2^(n+1),
    quad n >= 2; quad Lambda_1 = 2.
  $
]

==== Formula for $Lambda(B_n; K)$ <ss:l2001-enumeration-b-integrals>

Here we will find integral representation for sums in formula
@eq:l2001-enumeration-b-binomial-sum.

#lemma[
  #source(9, printed: 28)For $n >= 1$
  $
    S_1(n) = sum_(i=2)^n sum_(t=1)^n binom(t-1, t-i)
    (t(t+1))/(2n-t) binom(2n-t, n-t)
    = 1/(2 pi upright(i)) integral_(abs(x)=rho)
    P_(n)(x)(1-x)^(-n-3)(1-2x)^(-1) x^(-n+1) dif x,
    quad 0 < rho < 1/2,
  $ <eq:l2001-enumeration-first-sum-integral>
  where
  $
    P_(n)(x) = (n+1)-2(2n+1)x+2(2n+1)x^2.
  $ <eq:l2001-enumeration-polynomial-p>
] <lem:l2001-enumeration-first-sum-integral>

#proof[
  We first find an integral representation for multipliers of a general member
  of sum @eq:l2001-enumeration-first-sum-integral. We have
  $
    binom(t-1, t-i) = 1/(2 pi upright(i))
    integral_(abs(y)=rho_1) (1-y)^(-i) y^(-t+i-1) dif y,
    quad 0 < rho_1 < 1.
  $ <eq:l2001-enumeration-binomial-integral>

  To obtain the integral representation for the second multiplier
  $(t(t+1))/(2n-t) binom(2n-t, n-t)$ we represent it primary as a sum of
  binomial coefficients. Successively we obtain
  $
    t/(2n-t) binom(2n-t, n-t)
    = ((t-2n)+2n)/(2n-t) binom(2n-t, n-t)
    = -binom(2n-t, n-t)+2binom(2n-t-1, n-t);
  $
  $
    -(t+1)binom(2n-t, n-t)
    = (n+1)binom(2n-t+1, n-t)-2(n+1)binom(2n-t, n-t);
  $
  $
    2(t+1)binom(2n-t-1, n-t)
    = -2n binom(2n-t, n-t)+2(2n+1)binom(2n-t-1, n-t).
  $

  As a result we have
  $
    (t(t+1))/(2n-t) binom(2n-t, n-t)
    = (n+1)binom(2n-t+1, n-t)-2(2n+1)binom(2n-t, n-t)
    +2(2n+1)binom(2n-t-1, n-t)
    = (n+1)1/(2 pi upright(i)) integral_(abs(x)=rho_2)
    (1-x)^(-n-2)x^(-n+t-1) dif x
    -2(2n+1)1/(2 pi upright(i)) integral_(abs(x)=rho_2)
    (1-x)^(-n-1)x^(-n+t-1) dif x
    +2(2n+1)1/(2 pi upright(i)) integral_(abs(x)=rho_2)
    (1-x)^(-n)x^(-n+t-1) dif x
    = 1/(2 pi upright(i)) integral_(abs(x)=rho_2)
    P_(n)(x)(1-x)^(-n-2)x^(-n+t-1) dif x,
    quad 0 < rho_2 < 1,
  $ <eq:l2001-enumeration-second-binomial-integral>
  where polynomial $P_(n)(x)$ in defined in @eq:l2001-enumeration-polynomial-p.

  From @eq:l2001-enumeration-binomial-integral and
  @eq:l2001-enumeration-second-binomial-integral follows
  $
    binom(t-1, t-i) (t(t+1))/(2n-t) binom(2n-t, n-t)
    = 1/(2 pi upright(i))^2 integral_Gamma
    P_(n)(x)(1-x)^(-n-2)(1-y)^(-i)y^(-t+i-1)x^(-n+t-1)
    dif x ∧ dif y,
  $
  where skeleton $Gamma = {(y,x) in CC^2: abs(y)=rho_1, abs(x)=rho_2,
    0 < rho_1 < 1, 0 < rho_2 < 1}$. From there

  #source(10, printed: 29)$
    S_1 = sum_(i=2)^n sum_(t=i)^n binom(t-1, t-i)
    (t(t+1))/(2n-t) binom(2n-t, n-t)
    = sum_(i=2)^n sum_(t=i)^n 1/(2 pi upright(i))^2 integral_Gamma
    P_(n)(x)(1-x)^(-n-2)(1-y)^(-i)y^(-t+i-1)x^(-n+t-1)
    dif x ∧ dif y
    = sum_(i=2)^n sum_(t=i)^infinity dots
  $
  (because by $t > n$ integrals on $x$ obviously are equal 0)
  $
    = sum_(i=2)^n lr(
      {
        1/(2 pi upright(i))^2 integral_Gamma
        P_(n)(x)(1-y)^(-i)(1-x)^(-n-2)x^(-n-1)y^(i-1)
        lr({sum_(t=i)^infinity (x/y)^t}) dif x ∧ dif y
      }
    ).
  $

  There the values $rho_1$ and $rho_2$ are chosen in such a way that
  $1 > rho_1 > rho_2 > 0$ and on skeleton $Gamma$ the inequality
  $
    abs(x/y) < 1
  $ <eq:l2001-enumeration-geometric-bound>
  holds, and a series of geometric progression
  $
    sum_(t=i)^infinity (x/y)^t = (1-x/y)^(-1)(x/y)^i
  $ <eq:l2001-enumeration-geometric-series>
  on this skeleton converges uniformly. Thus, taking into account
  @eq:l2001-enumeration-geometric-bound–@eq:l2001-enumeration-geometric-series
  we get
  $
    S_1 = sum_(i=2)^n 1/(2 pi upright(i))^2 integral_Gamma
    P_(n)(x)(1-y)^(-i)(1-x)^(-n-2)(y-x)^(-1)x^(-n+i-1)
    dif x ∧ dif y
    = sum_(i=2)^infinity dots
  $
  (since integrals on $x$ are equal 0 by $i > n$)
  $
    = 1/(2 pi upright(i))^2 integral_Gamma
    P_(n)(x)(1-x)^(-n-2)(y-x)^(-1)x^(-n-1)
    lr({sum_(i=2)^infinity (x/(1-y))^i}) dif x ∧ dif y.
  $

  Here we choose $rho_2$ small enough, such that inequality
  $abs(x(1-y)^(-1)) < 1$ holds on skeleton $Gamma$. Thus, summing w.r.t. $i$ we
  get
  $
    S_1 = 1/(2 pi upright(i))^2 integral_Gamma
    (P_(n)(x)(1-x)^(-n-2))/((y-x)(1-x-y)(1-y)x^(n-1))
    dif x ∧ dif y.
  $ <eq:l2001-enumeration-first-double-integral>

  According to the theorem of residues we compute
  @eq:l2001-enumeration-first-double-integral as an iterated integral using the
  fact that the integrand has only a pole of first degree at the point $y=x$.
  Thus integrating @eq:l2001-enumeration-first-double-integral w.r.t. $y$ we
  have
  @eq:l2001-enumeration-first-sum-integral
  $
    S_1 = 1/(2 pi upright(i)) integral_(abs(x)=rho)
    (P_(n)(x)(1-x)^(-n-3))/((1-2x)x^(n-1)) dif x,
    quad 0 < rho < 1/2.
  $
]

#lemma[
  $
    sum_(m=t+1)^n m/(2n-m) binom(2n-m, n-m)
    = (t+2)/(2n-t) binom(2n-t, n-t-1).
  $ <eq:l2001-enumeration-ballot-tail>
] <lem:l2001-enumeration-ballot-tail>

#proof[
  Setting
  $
    m/(2n-m) binom(2n-m, n-m)
    = -binom(2n-m, n-m)+2binom(2n-m-1, n-m)
    = -1/(2 pi upright(i)) integral_(abs(x)=rho)
    (1-x)^(-n-1)x^(-n+m-1) dif x
    +2/(2 pi upright(i)) integral_(abs(x)=rho)
    (1-x)^(-n)x^(-n+m-1) dif x
    = 1/(2 pi upright(i)) integral_(abs(x)=rho)
    (1-x)^(-n-1)(1-2x)x^(-n+m-1) dif x,
    quad 0 < rho < 1,
  $ <eq:l2001-enumeration-ballot-integral>

  #source(11, printed: 30)we have
  $
    S = sum_(m=t+1)^n m/(2n-m) binom(2n-m, n-m)
    = sum_(m=t+1)^n 1/(2 pi upright(i)) integral_(abs(x)=rho)
    (1-x)^(-n-1)(1-2x)x^(-n+m-1) dif x
    = sum_(m=t+1)^infinity dots
  $
  (supplemented integrals obviously are equal to 0 by $m > n$)
  $
    = 1/(2 pi upright(i)) integral_(abs(x)=rho)
    (1-x)^(-n-1)(1-2x)
    lr({sum_(m=t+1)^infinity x^m}) x^(-n-1) dif x
  $
  (since the series $sum_(m=t+1)^infinity x^m$ uniformly converges by
  $abs(x)=rho < 1$)
  $
    = 1/(2 pi upright(i)) integral_(abs(x)=rho)
    (1-x)^(-n-2)(1-2x)x^(-n+t) dif x
    = 1/(2 pi upright(i)) integral_(abs(x)=rho)
    (1-x)^(-n-2)x^(-n+t) dif x
    -2/(2 pi upright(i)) integral_(abs(x)=rho)
    (1-x)^(-n-2)x^(-n+t+1) dif x
    = (t+2)/(2n-t) binom(2n-t, n-t-1).
  $
]

#lemma[
  For $n >= 1$
  $
    S_2(n) = sum_(i=2)^(n-1) sum_(t=i)^(n-1) sum_(m=1+t)^n
    (t+1)binom(t-2, t-i) m/(2n-m)binom(2n-m, n-m)
    = 1/(2 pi upright(i)) integral_(abs(x)=rho)
    Q_(n)(x)(1-x)^(-n-3)(1-2x)^(-1)x^(-n+2) dif x,
    quad 0 < rho < 1/2.
  $ <eq:l2001-enumeration-second-sum-integral>
] <lem:l2001-enumeration-second-sum-integral>

#proof[
  Summing over $m$, by virtue of @eq:l2001-enumeration-ballot-tail we have
  $
    S_2(n) = sum_(i=2)^(n-1) sum_(t=i)^(n-1) binom(t-2, t-i)
    ((t+1)(t+2))/(2n-t) binom(2n-t, n-t-1).
  $ <eq:l2001-enumeration-second-sum-reduced>

  Further computations of the sum $S_2(n)$ were carried out in the same way as
  for sum $S_1(n)$ in Lemma~@lem:l2001-enumeration-first-sum-integral, using
  relations
  $
    binom(t-2, t-i) = 1/(2 pi upright(i)) integral_(abs(y)=rho_1)
    (1-y)^(-i+1)y^(-t+i-1) dif y, quad 0 < rho_1 < 1,
  $
  $
    ((t+1)(t+2))/(2n-t) binom(2n-t, n-t-1)
    = -(n+2)binom(2n-t+1, n-t-1)+2(n+1)binom(2n-t, n-t-1)
    +2(n+2)binom(2n-t, n-t-2)-2(2n+1)binom(2n-t-1, n-t-2)
    = 1/(2 pi upright(i)) integral_(abs(x)=rho_2)
    Q_(n)(x)(1-x)^(-n-3)x^(-n+t) dif x,
    quad 0 < rho_2 < 1,
  $
  where
  $
    Q_(n)(x) = n-4n x+2(2n+1)x^2.
  $ <eq:l2001-enumeration-polynomial-q>
]

#lemma[
  For $n >= 1$
  $
    S_3(n) = sum_(i=2)^n sum_(t=i)^n binom(t-1, t-i)
    (t(t+1))/(2n-t) binom(2n-t, n-t)
    +sum_(i=2)^(n-1) sum_(t=i)^(n-1) sum_(m=t+1)^n
    binom(t-2, t-i) ((t+1)m)/(2n-m) binom(2n-m, n-m)
    = 3 dot 4^(n-1)-(2n+1)binom(2n-2, n-4)
    -(n+3/2)binom(2n-1, n-3)+(n+1/4)binom(2n, n-2)
    -3/8 binom(2n+4, n+2)+3/4 binom(2n+2, n+1).
  $ <eq:l2001-enumeration-combined-sum>
] <lem:l2001-enumeration-combined-sum>

#proof[
  #source(12, printed: 31)If we substitute the integral representations
  @eq:l2001-enumeration-first-sum-integral and
  @eq:l2001-enumeration-second-sum-integral for sums in left part of formula
  @eq:l2001-enumeration-combined-sum, where polynomials $P_(n)(x)$ and
  $Q_(n)(x)$ are defined in @eq:l2001-enumeration-polynomial-p and
  @eq:l2001-enumeration-polynomial-q, then we obtain
  $
    S_3(n) = 1/(2 pi upright(i)) integral_(abs(x)=rho)
    (P_(n)(x)+x Q_(n)(x))(1-x)^(-n-3)(1-2x)^(-1)x^(-n+1) dif x
    = 1/(2 pi upright(i)) integral_(abs(x)=rho)
    (R_(n)(x))/(1-2x) (1-x)^(-n-3)x^(-n+1) dif x,
    quad 0 < rho < 1/2;
  $ <eq:l2001-enumeration-combined-integral>

  where
  $
    R_(n)(x) = (n+1)-(3n+2)x+2x^2+2(2n+1)x^3.
  $ <eq:l2001-enumeration-polynomial-r>
  Since
  $
    (R_(n)(x))/(1-2x) = (n+1/4)-(n+3/2)x-(2n+1)x^2
    +3/4 (1-2x)^(-1),
  $
  then integral @eq:l2001-enumeration-combined-integral decomposes on the next
  sum of integrals:
  $
    S_3(n) = (n+1/4)1/(2 pi upright(i)) integral_(abs(x)=rho)
    (1-x)^(-n-3)x^(-n+1) dif x
    -(n+3/2)1/(2 pi upright(i)) integral_(abs(x)=rho)
    (1-x)^(-n-3)x^(-n+2) dif x
    -(2n+1)1/(2 pi upright(i)) integral_(abs(x)=rho)
    (1-x)^(-n-3)x^(-n+3) dif x + J(n)
  $ <eq:l2001-enumeration-combined-split>
  $
    = (n+1/4)binom(2n, n-2)-(n+3/2)binom(2n-1, n-3)
    -(2n+1)binom(2n-2, n-4)+J(n),
  $ <eq:l2001-enumeration-combined-coefficients>
  where integral
  $
    J(n) = 3/4 1/(2 pi upright(i)) integral_(abs(x)=rho)
    (1-2x)^(-1)(1-x)^(-n-3)x^(-n+1) dif x,
    quad 0 < rho < 1/2.
  $ <eq:l2001-enumeration-j-integral>

  In computing the last integral we use substitution $z=f(x)=x(1-x)$, $f(0)=0$,
  $dif z=(1-2x)dif x$, where branch $x=f^(-1)(z)=1/2(1-(1-4z)^(1/2))$ is chosen
  so that $f^(-1)(0)=0$. If we use the relations
  $
    (1-2x)^2=1-4z,
  $
  $
    x^4 = 1/16(1-(1-4z)^(1/2))^4
    = 1/4((1-2z)-(1-4z)^(1/2))^2
    = 1/2(1-4z+2z^2-(1-2z)(1-4z)^(1/2)),
  $
  then pointed substitution gives
  $
    J(n) = 3/4 1/(2 pi upright(i)) integral_(abs(x)=rho)
    x^4/(1-2x)^2 (x(1-x))^(-n-3)(1-2x)dif x
    = 3/8 1/(2 pi upright(i)) integral_(abs(z)=1/5)
    (1-4z+2z^2-(1-2z)(1-4z)^(1/2))/((1-4z)z^(n+3)) dif z
    = 3/8 1/(2 pi upright(i)) integral_(abs(z)=1/5)
    z^(-n-3) dif z
    +3/4 1/(2 pi upright(i)) integral_(abs(z)=1/5)
    (1-4z)^(-1)z^(-n-1) dif z
    -3/8 1/(2 pi upright(i)) integral_(abs(z)=1/5)
    (1-4z)^(-1/2)z^(-n-3) dif z
    +3/4 1/(2 pi upright(i)) integral_(abs(z)=1/5)
    (1-4z)^(-1/2)z^(-n-2) dif z
    = 3 dot 4^(n-1)-3/8 binom(2n+4, n+2)+3/4 binom(2n+2, n+1),
  $ <eq:l2001-enumeration-j-coefficients>

  where in computing of integrals we use the formula of geometric progression
  and known decomposition
  $
    (1-4z)^(-1/2) = 1+sum_(k=1)^infinity binom(2k, k)z^k.
  $

  #source(13, printed: 32)If we substitute the value of integral $J_n$ obtained
  in @eq:l2001-enumeration-j-coefficients into
  @eq:l2001-enumeration-combined-coefficients we get the formula
  @eq:l2001-enumeration-combined-sum.
]

If we substitute the expression for $S_3(n)$ from
@eq:l2001-enumeration-combined-sum into @eq:l2001-enumeration-b-binomial-sum
then after a straightforward computation we get the assertion in
Theorem~@th:l2001-enumeration-ideal-count.

The integral representations @eq:l2001-enumeration-first-sum-integral and
@eq:l2001-enumeration-second-sum-integral for sums $S_1(n)$, $S_2(n)$ allows
also to compute these sums, if we use the calculating scheme from the proof of
Lemma~@lem:l2001-enumeration-combined-sum.

Below a table for initial values for $Lambda(B_n; K)$ is given

#table(
  columns: 6,
  align: center,
  table.header([$n$], [1], [2], [3], [4], [5]),
  [$Lambda(B_n; K)$], [2], [10], [41], [166], [670],
)
