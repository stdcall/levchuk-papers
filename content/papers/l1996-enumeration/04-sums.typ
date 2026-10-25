#import "defs.typ": *

=== Computation of combinatorial sums <sec:l1996-enumeration-sums>

#source(9, printed: 57)Further we apply the method of integral representation
and calculation of combinatorial sums (the method of coefficients) which were
developed in [@bib:l1996-enumeration-Egorychev1989].

#lemma[
  Let a sum $S_n$ be given by
  $
    S_n = sum_(i=2)^(n-1) sum_(t=i)^(n-1) sum_(m=t+1)^n
    binom(t-2, t-i) m/(2n-m) binom(2n-m, n-m), quad n >= 3.
  $
  #statement-intro[
    Then
    $
      S_n = binom(2n-2, n-3).
    $ <eq:l1996-enumeration-d-sum-evaluated>
  ]
] <lem:l1996-enumeration-d-sum>

#proof[
  First, by the algorithm of the method of coefficients
  [@bib:l1996-enumeration-Egorychev1989, Chapter~1], we find the following
  integral representations for the numbers $binom(t-2, t-i)$ and
  $m/(2n-m)binom(2n-m, n-m)$:
  $
    binom(t-2, t-i) = 1/(2 pi upright(i)) integral_(abs(y)=rho_2)
    (1+y)^(t-2)y^(-t+i-1) dif y, quad rho_2 > 0;
  $
  $
    m/(2n-m)binom(2n-m, n-m)
    = 2binom(2n-m-1, n-m)-binom(2n-m, n-m)
    = -1/(2 pi upright(i)) integral_(abs(x)=rho_1)
    (1-x)^(-n-1)x^(-n+m-1) dif x
    + 2/(2 pi upright(i)) integral_(abs(x)=rho_1)
    (1-x)^(-n)x^(-n+m-1) dif x
    = 1/(2 pi upright(i)) integral_(abs(x)=rho_1)
    (1-x)^(-n-1)(1-2x)x^(-n+m-1) dif x, quad 0 < rho_1 < 1.
  $

  Substituting the integral representations into
  @eq:l1996-enumeration-d-sum-evaluated we obtain
  $
    S_n = sum_(i=2)^(n-1) sum_(t=i)^(n-1) sum_(m=t+1)^n
    1/(2 pi upright(i))^2 integral_(abs(x)=rho_1) integral_(abs(y)=rho_2)
    (1+y)^(t-2)y^(-t+i-1)
    times (1-x)^(-n-1)(1-2x)x^(-n+m-1) dif x ∧ dif y
  $
  #source(10, printed: 58)$
    = sum_(i=2)^(n-1) sum_(t=i)^(n-1) sum_(m=t+1)^infinity dots
  $
  [since the added summands equal $0$]
  $
    = sum_(i=2)^(n-1) sum_(t=i)^(n-1) 1/(2 pi upright(i))^2
    integral_(abs(x)=rho_1) integral_(abs(y)=rho_2)
    (1+y)^(t-2)y^(-t+i-1)
    times (1-x)^(-n-1)(1-2x)x^(-n-1)
    lr((sum_(m=t+1)^infinity x^m)) dif x ∧ dif y
    = sum_(i=2)^(n-1) sum_(t=i)^(n-1) 1/(2 pi upright(i))^2
    integral_(abs(x)=rho_1) integral_(abs(y)=rho_2)
    (1+y)^(t-2)y^(-t+i-1)
    times (1-x)^(-n-1)(1-2x)x^(-n-1) x^(t+1)/(1-x) dif x ∧ dif y
    = sum_(i=2)^(n-1) sum_(t=i)^infinity dots
    = sum_(i=2)^(n-1) 1/(2 pi upright(i))^2
    integral_(abs(x)=rho_1) integral_(abs(y)=rho_2)
    ((1+y)^(i-2)(1-x)^(-n-2)(1-2x)x^i)/
    (x^n y(1-x(1+y)y^(-1))) dif x ∧ dif y
    = sum_(i=2)^infinity dots
    = 1/(2 pi upright(i))^2
    integral_(abs(x)=rho_1) integral_(abs(y)=rho_2)
    ((1-x)^(-n-2)(1-2x)x^2)/
    (x^n lr((y-(1+y)x))(1-x(1+y))) dif x ∧ dif y
    = 1/(2 pi upright(i))^2
    integral_(abs(x)=rho_1) integral_(abs(y)=rho_2)
    ((1-x)^(-n-3)(1-2x))/
    (x^(n-2)(y-x(1-x)^(-1))(1-x(1+y))) dif x ∧ dif y
  $
  [$y=x(1-x)^(-1)$ a simple pole]
  $
    = 1/(2 pi upright(i)) integral_(abs(x)=rho_1)
    ((1-x)^(-n-3)(1-2x))/(x^(n-2)(1-x(1+x(1-x)^(-1)))) dif x
  $
  #source(11, printed: 59)$
    = 1/(2 pi upright(i)) integral_(abs(x)=rho_1)
    (1-x)^(-n-2)x^(-n+2) dif x
    = binom(n+2+n-3-1, n-3) = binom(2n-2, n-3).
  $

  Here we may summarize under the integration sign because the geometric
  progression converges uniformly on the sceleton
  $
    gamma = {(x,y) in CC^2: abs(x)=rho_1, abs(y)=rho_2,
      0 < rho_1 << rho_2 < 1/2}
  $
  and, consequently, the inequalities
  $
    abs(x) < 1, quad abs((1+y)x y^(-1)) < 1, quad abs(x(1+y)) < 1
  $
  are valid on $gamma$. Lemma~@lem:l1996-enumeration-d-sum is proved.
]

#lemma[
  Let $n$ be a natural number. Then the following identity holds:
  $
    sum_(i=1)^n sum_(m=i)^n (m-i+2)binom(m-1, m-i)
    m/(2n-m)binom(2n-m, n-m) = 4^(n-1)+binom(2n-1, n).
  $ <eq:l1996-enumeration-c-sum-evaluated>
] <lem:l1996-enumeration-c-sum>

#proof[
  The integral representations for binomial coefficients lead to the formulas
  $
    (m-i+2) = 1/(2 pi upright(i)) integral_(abs(z)=rho_1)
    (1-z)^(-2)z^(-m+i-2) dif z, quad rho_1 < 1,
  $ <eq:l1996-enumeration-linear-integral>
  $
    binom(m-1, m-i) = binom(m-1, i-1)
    = 1/(2 pi upright(i)) integral_(abs(y)=rho_2)
    (1+y)^(m-1)y^(-i) dif y, quad rho_2 > 0,
  $ <eq:l1996-enumeration-binomial-integral>
  $
    m/(2n-m)binom(2n-m, n-m)
    = 1/(2 pi upright(i)) integral_(abs(x)=rho_3)
    (1-x)^(-n-1)(1-2x)x^(-n+m-1) dif x, quad 0 < rho_3 < 1.
  $ <eq:l1996-enumeration-ballot-integral>

  By
  @eq:l1996-enumeration-linear-integral–@eq:l1996-enumeration-ballot-integral,
  the sum $S$ on the left-hand side of @eq:l1996-enumeration-c-sum-evaluated can
  be presented as follows:
  $
    S = sum_(i=1)^n sum_(m=i)^n 1/(2 pi upright(i))^3 integral_gamma
    lr({(1-x)^(-n-1)(1-2x)(1-z)^(-2)})
    times (1+y)^(m-1)y^(-i)z^(-m+i-2)x^(-n+m-1)
    dif x ∧ dif y ∧ dif z,
  $
  #source(12, printed: 60)where
  $
    gamma = {(x,y,z) in CC^3: abs(z)=rho_1, abs(y)=rho_2, abs(x)=rho_3,
      0 < rho_1 < 1, rho_2 > 0, 0 < rho_3 < 1}.
  $

  Continue the sum
  $
    S = sum_(i=1)^infinity sum_(m=i)^infinity dots
  $
  [by
  @eq:l1996-enumeration-linear-integral–@eq:l1996-enumeration-ballot-integral,
  the added summands equal $0$].
  #statement-intro[
    Replacing $m-i$ by $m$, we find
    $
      S = sum_(i=1)^infinity sum_(m=0)^infinity
      1/(2 pi upright(i))^3 integral_gamma
      lr({dots})(1+y)^(m+i-1)y^(-i)z^(-m-2)x^(-n+m+i-1)
      dif x ∧ dif y ∧ dif z
      = 1/(2 pi upright(i))^3 integral_gamma
      lr({dots})z^(-2)x^(-n-1)(1+y)^(-1)
      lr([sum_(i=1)^infinity (x(1+y)/y)^i])
      times lr([sum_(m=0)^infinity (x(1+y)/z)^m]) dif x ∧ dif y ∧ dif z
      = 1/(2 pi upright(i))^3 integral_gamma
      lr({dots})z^(-2)x^(-n-1)(1+y)^(-1) x(1+y)/y
      times (1-x(1+y)/y)^(-1)(1-x(1+y)/z)^(-1)
      dif x ∧ dif y ∧ dif z
      = 1/(2 pi upright(i))^3 integral_gamma
      ((1-x)^(-n-1)(1-2x)(1-z)^(-2))/
      (z x^n lr((z-x(1+y)))(y-x(1+y))) dif x ∧ dif y ∧ dif z.
    $ <eq:l1996-enumeration-triple-integral>
  ]

  Here we may summarize under the integration sign because the geometric
  progression converges uniformly on the sceleton $gamma$. The latter is true if
  we choose $rho_1$, $rho_2$, and $rho_3$ such that
  $
    0 < rho_3 << rho_2 << rho_1 < 1.
  $
  Then the inequalities
  $
    abs(x(1+y)z^(-1)) < 1, quad abs(x(1+y)y^(-1)) < 1
  $
  are valid on $gamma$.

  #source(13, printed: 61)Applying the residue theorem on variable $z$ at the
  simple poles $z_1=0$ and $z_2=x(1+y)$, we obtain
  $
    J_1 = -1/(2 pi upright(i))^2
    integral_(abs(x)=rho_3) integral_(abs(y)=rho_2)
    ((1-x)^(-n-1)(1-2x))/(x^(n+1)(1+y)(y-x(1+y))) dif x ∧ dif y
  $
  [$y=x(1-x)^(-1)$ a simple pole, $y=-1$ an absent pole]
  $
    = -1/(2 pi upright(i)) integral_(abs(x)=rho_3)
    ((1-x)^(-n-2)(1-2x))/(x^(n+1)(1+x/(1-x))) dif x
    = -1/(2 pi upright(i)) integral_(abs(x)=rho_3)
    ((1-x)^(-n-1)(1-2x))/x^(n+1) dif x
    = -binom(2n, n)+2binom(2n-1, n-1)=0
  $
  and
  $
    J_2 = 1/(2 pi upright(i))^2
    integral_(abs(x)=rho_3) integral_(abs(y)=rho_2)
    ((1-x)^(-n-2)(1-2x))/
    ((1-x(1+y))^2(y-x/(1-x))x^(n+1)(1+y)) dif x ∧ dif y
  $
  [$y=x(1-x)^(-1)$ a simple pole]
  $
    = 1/(2 pi upright(i)) integral_(abs(x)=rho_3)
    ((1-x)^(-n-2)(1-2x))/
    ((1+x/(1-x))x^(n+1)(1-x(1+x(1-x)^(-1)))^2) dif x
    = 1/(2 pi upright(i)) integral_(abs(x)=rho_3)
    (1-x)^(-n+1)/((1-2x)x^(n+1)) dif x
  $
  #metadata(none) <pass:l1996-enumeration-inverse-branch>
  [substituting $w=x(1-x)$ we have $0 arrow.r 0$, hence $x=(1-(1-4w)^(1/2))/2$]
  $
    = 1/(2 pi upright(i)) integral_(abs(w)=rho_3)
    (1+2(1-4w)^(1/2))/(4(1-4w)w^(n+1)) dif w
    = 1/4 1/(2 pi upright(i)) integral_(abs(w)=0.2)
    (1-4w)^(-1)w^(-n-1) dif w
    + 1/2 1/(2 pi upright(i)) integral_(abs(w)=0.2)
    (1-4w)^(-1/2)w^(-n-1) dif w
  $
  #source(14, printed: 62)$
    = 4^(n-1)+1/2 binom(2n, n) = 4^(n-1)+binom(2n-1, n).
  $

  Thus, $S=J_1+J_2=4^(n-1)+binom(2n-1, n)$. Lemma~@lem:l1996-enumeration-c-sum
  is proved.
]
