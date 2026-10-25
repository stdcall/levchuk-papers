#import "defs.typ": *
#import "03-paths-diagram.typ": paths-coordinates

=== #[Combinatorial analysis of the number of paths and formulas for $d(D_n,K)$
  and $d(C_n,K)$] <sec:l1996-enumeration-combinatorics>

We use the well-known result on the number of paths with diagonal steps on a
lattice with integer (Cartesian) coordinates.

#lemma(title: [[@bib:l1996-enumeration-Feller1967, Theorem~1]])[
  The number of paths with diagonal steps laying above the real axis and leading
  from the origin to a fixed point $(X,Y)$ is equal to:
  $
    N_(X,Y) = Y/X binom(X, (X+Y)/2).
  $ <eq:l1996-enumeration-strict-ballot>
] <lem:l1996-enumeration-strict-ballot>

By Lemma~@lem:l1996-enumeration-strict-ballot, the number of similar paths but
laying above or on the real axis is equal to:
$
  N_(X,Y)^* = (Y+1)/(X+1) binom(X+1, (X+Y+2)/2).
$ <eq:l1996-enumeration-weak-ballot>

==== The case $d(D_n,K)$ <ss:l1996-enumeration-d-paths>

#source(7, printed: 55)Due to the combinatorial description given in
Section~@sec:l1996-enumeration-construction, we have
$
  d(D_n,K) = d(twisted(2, A)_(2n-2),K)
  + sum_(i=2)^(n-1) sum_(t=i)^(n-1) sum_(m=t+1)^n
  N_1 lr((i,t)) N_2 lr((m,n))
  + d(A_(n-1),K)-d(A_(n-2),K), quad n >= 3,
$ <eq:l1996-enumeration-d-path-sum>
where (in a suitable coordinate system $(x,y)$, see
Fig.~@fig:l1996-enumeration-path-coordinates) $N_1 lr((i,t))$ denotes the number
of various paths with rectangular steps from points $A_i=(-i+1,i)$,
$i in overline(2\,n)$, to points $B_t=(-1,t)$, $t >= i$, and $N_2 lr((m,n))$
stands for the number of various paths from the point $(1,m)$ to the point
$(n,0)$ all of whose points are below or on the line $L$ from $(n,0)$ to
$(0,n)$.

#drawing(paths-coordinates) <fig:l1996-enumeration-path-coordinates>

It is easy to see that the number $N_1 lr((i,t))$ coincides with the number of
various $k=t-i$ scheduling (indistinguishable) rises on $l=i-1$ distinguishable
positions (cells) under the assumption that some of them may be empty. Thus, we
have #source(8, printed: 56)$
  N_1 lr((i,t)) = binom(l+k-1, k) = binom(t-2, t-i).
$ <eq:l1996-enumeration-rectangle-paths>

Choose the new coordinate system $(X,Y)$ with the origin at the point $B$, and
coordinate axes as those indicated on
Fig.~@fig:l1996-enumeration-path-coordinates by dashed line. Then we can
consider the above-mentioned paths $N_2 lr((m,n))$ with rectangular steps from
the point $A_m=(1,m)$ to the point $B$ as the paths from the point $B$ to the
point $A_m$ on the same lattice but with diagonal steps. Moreover, the
coordinates of the point $A_m=(X_m,Y_m)$ in the coordinate system $(X,Y)$ are
$X_m=2n-m-1$, $Y_m=m-1$. Therefore, from @eq:l1996-enumeration-weak-ballot it
follows that
$
  N_2 lr((m,n)) = m/(2n-m) binom(2n-m, n),
$ <eq:l1996-enumeration-ballot-paths>
and from @eq:l1996-enumeration-d-path-sum–@eq:l1996-enumeration-ballot-paths we
obtain
$
  d(D_n,K) = d(twisted(2, A)_(2n-2),K)
  + sum_(i=2)^(n-1) sum_(t=i)^(n-1) sum_(m=t+1)^n
  binom(t-2, t-i) m/(2n-m) binom(2n-m, n)
  + d(A_(n-1),K)-d(A_(n-2),K).
$ <eq:l1996-enumeration-d-binomial-sum>

==== The case $d(C_n,K)$ <ss:l1996-enumeration-c-paths>

Due to the combinatorial description given in
Section~@sec:l1996-enumeration-construction, we have
$
  d(C_n,K) = sum_(i=1)^n sum_(m=i)^n (m-i+2)S(i,m,n),
$
where $S(i,m,n)=N_1 lr((i,m)) times N_2 lr((m,n))$. Here $N_1 lr((i,m))$ (in
suitable coordinate system $(x,y)$; see
Fig.~@fig:l1996-enumeration-path-coordinates) stands for the number of various
paths with rectangular steps from points $A_i=(-i+1,i)$, $i in overline(1\,n)$,
to points $B_m=(0,m)$, $m in overline(i\,n)$, and $N_2 lr((m,n))$ denotes the
number of various paths from the point $(1,m)$ to the point $(n,0)$ which are
placed below or on the line $L$ passing through the points $(n,0)$ and $(0,n)$.

In the same manner as in the case of $d(D_n,K)$ we obtain
$
  d(C_n,K) = sum_(i=1)^n sum_(m=i)^n
  (m-i+2)binom(m-1, m-i) m/(2n-m) binom(2n-m, n).
$ <eq:l1996-enumeration-c-binomial-sum>
