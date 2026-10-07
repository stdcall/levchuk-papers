#import "defs.typ": *

=== #[
  Combinatorics of the number of paths on lattice and formulas for
  $Lambda(C_n; K)$ and $Lambda(B_n; K)$, $2K=0$
] <sec:l2001-enumeration-lattice-paths>

==== #[
  Combinatorics of the number of paths on lattice
] <ss:l2001-enumeration-path-count>

Below we’ll use the well known result for the number of paths with diagonal
steps on lattices with integer (Cartesian) coordinates.

#lemma(
  title: [#[
    [@bib:l2001-enumeration-Feller1967] Vol.~I, ch.~III, §~2, theorem~1, p.~85
  ]],
)[
  The number of paths on lattices with diagonal steps, lying above abscissa
  axes, from the origin to fixed point $(X,Y)$ is equal to
  $
    upright(N)_(X,Y) = Y/X binom(X, (X+Y)/2).
  $ <eq:l2001-enumeration-strict-ballot>
] <lem:l2001-enumeration-strict-ballot>

From Lemma~@lem:l2001-enumeration-strict-ballot follows that the number of paths
of the mentioned type, lying above or touching the abscissa axis, is equal to
$
  upright(N)_(X,Y)^* = (Y+1)/(X+1) binom(X+1, (X+Y+2)/2).
$ <eq:l2001-enumeration-weak-ballot>

==== Computation of $Lambda(C_n; K)$ <ss:l2001-enumeration-c-paths>

From the combinatorial description given in
§~@sec:l2001-enumeration-construction we have that
$
  Lambda(C_n; K) = sum_(i=1)^n 2^(n-i+1) S(i),
$ <eq:l2001-enumeration-c-path-sum>

where $S(i)$ is the number of various paths on the rectangle lattice with
rectangular steps from point $A_i=(-i+1,n-i)$ to point $C=(n,0)$ (see the
coordinate system in fig.~@fig:l2001-enumeration-c-coordinates), which are below
or touch to interest of the straight line $L$ passing through the points
$C=(n,0)$ and $D=(0,n)$.

Choose the new coordinate system $(X,Y)$ with the origin at point $C$, and with
coordinate axes shown in fig.~@fig:l2001-enumeration-c-coordinates by the dotted
line. Then the above mentioned path with rectangular steps from point $A_i$ to
point

#import "diagrams/coordinates.typ": b-coordinates, c-coordinates
#source(6, printed: 25)#drawing(
  c-coordinates,
) <fig:l2001-enumeration-c-coordinates>

$C$ may be considered as the path from point $A_i$ on the same lattice, but with
diagonal steps. Moreover the coordinates of point $A=(X_i,Y_i)$ in the new
coordinate system $(X,Y)$ obviously are equal to $X_i=2n-1$, $Y_i=2i-1$.
<pass:l2001-enumeration-c-affine-coordinate-transform> Thus, using
@eq:l2001-enumeration-weak-ballot we obtain that
$
  S(i) = i/n binom(2n, n-i)
$
and
$
  Lambda(C_n; K) = sum_(i=1)^n 2^(n-i+1) i/n binom(2n, n-i).
$ <eq:l2001-enumeration-c-binomial-sum>

==== Computation of $Lambda(B_n; K)$ <ss:l2001-enumeration-b-paths>

By virtue of the formula @eq:l2001-enumeration-b-steplines we have
$
  Lambda(B_n; K) = d(A_n;K) + 2d(A_(n-1);K) - 2d(A_(n-2);K)
  + sum_(i=2)^n sum_(t=i)^n (t+1)
  upright(N)[(i,-i),(t,-1)] upright(N)[(t,1),(n,n)]
  + sum_(i=1)^(n-1) sum_(t=i)^(n-1) sum_(m=t+1)^n (t+1)
  upright(N)[(i,-i),(t,-2)] upright(N)[(m,1),(n,n)], quad n >= 2.
$ <eq:l2001-enumeration-b-stepline-sum>

The numbers $d(A_n;K)$ are defined by
Theorem~@th:l2001-enumeration-normal-count,
$
  d(A_n;K) = 1/(n+1) binom(2n+2, n).
$ <eq:l2001-enumeration-a-count>

The combinatorial description of the numbers $upright(N)[(i,-i),(t,-1)]$ and
$upright(N)[(m,1),(n,n)]$ is mentioned in §~@sec:l2001-enumeration-construction.

#source(7, printed: 26)#drawing(
  b-coordinates,
) <fig:l2001-enumeration-b-coordinates>

It is easy to see that $upright(N)[(i,-i),(t,-1)]$ coincides with the number of
rectangle paths from point $(t,-1)$ to point $(i,-i)$, and
$upright(N)[(m,1),(n,n)]$ coincides with the number of rectangle paths from
point $(m,1)$ to point $(n,n)$ in rectangle coordinate system $x,y$.

This directly implies that the first number coincides with the number of
$r$-combinations with the volume of the accesses $r$ is equal to path length
$r=(t-i)$, and the number $m$ coincides with the number of various virtual
vertices of this path, $m=i$. Thus,
$
  upright(N)[(i,-i),(t,-1)] = binom(t-1, t-i).
$ <eq:l2001-enumeration-rectangle-paths>

The second number obviously coincides with the number of diagonal paths from the
origin to the point $(X_0,Y_0)$ in coordinate system $X,Y$ (see
fig.~@fig:l2001-enumeration-b-coordinates), where $X_0=2n-m-1$, and $Y_0=m-1$.
Thus by virtue of formula
@eq:l2001-enumeration-weak-ballot
$
  upright(N)[(m,1),(n,n)] = m/(2n-m) binom(2n-m, n)
  = m/(2n-m) binom(2n-m, n-m).
$ <eq:l2001-enumeration-b-ballot>

Formula @eq:l2001-enumeration-b-stepline-sum with regard to formulas
@eq:l2001-enumeration-a-count–@eq:l2001-enumeration-b-ballot has the next form
$
  Lambda(B_n; K) = 1/(n+1) binom(2n+2, n)
  + 2/n binom(2n, n-1) - 2/(n-1) binom(2n-2, n-2)
  + sum_(i=2)^n sum_(t=i)^n (t+1) binom(t-1, t-i)
  t/(2n-t) binom(2n-t, n-t)
  + sum_(i=2)^(n-1) sum_(t=i)^(n-1) sum_(m=t+1)^n (t+1)
  binom(t-2, t-i) m/(2n-m) binom(2n-m, n-m), quad n >= 2.
$ <eq:l2001-enumeration-b-binomial-sum>
