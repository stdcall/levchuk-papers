#import "../../main-defs.typ": source
#import "defs.typ": *

=== Hentzel–Rúa semifield of order 64 <sec:l2017-quasifields-order64>

In 2007 Rúa and Hentzel has indicated [@bib:l2017-quasifields-Hentzel2007] the
second counter-example to Wene’s conjecture. The Hentzel–Rúa semifield is the
unique semifield of order 64 which is neither left nor right primitive. By
[@bib:l2017-quasifields-Hentzel2007], there exist also 35 semifields of order 64
that are not left-primitive but are right-primitive.

Now we consider a structure of Hentzel–Rúa semifield. Let $M(6,2)$ be the ring
of all $6 times 6$-matrices over $ZZ_2$ and let $W$ be a 6-dimensional linear
space over $ZZ_2$, $W = {x = (x_1,dots,x_6) | x_i in ZZ_2, i = 1,dots,6}$. We
define the map $theta: W arrow.r M(6,2)$ by the rule
$theta(x) = x_1 A_1 + dots + x_6 A_6$, $x in W$, where matrices
$A_1,A_2,dots,A_6 in GL_6 lr((2))$ are determined in
[@bib:l2017-quasifields-Hentzel2007]. Then we obtain a bijection $theta$ from
$W$ into $GL_6 lr((2)) union {0}$ and $R = {theta(x) | x in W}$ is a spread set.
It seems we get a semifield $W,+,ast$ of order 64 (the Hentzel–Rúa semifield
$HRu$), defining the multiplication $ast$ on $W$ by the rule

$ x ast y = x dot theta(y) = x sum_(i=1)^6 y_i A_i. $

The vector $e = (1,0,dots,0)$ is an identity in this semifield.

We obtain the following description of its automorphisms and maximal subfields.

#theorem[
  The automorphism group of Hentzel–Rúa semifield $HRu$ is isomorphic to the
  symmetric group $S_3$ and hence has exactly three involution automorphisms.
] <th:l2017-quasifields-hentzel-rua-automorphisms>

#theorem[
  The semifield $HRu$ contains exactly six maximal subfields:

  5 subfields of order 8, three from them are stabilizators of different
  involution automorphisms;

  the unique subfield of order 4, which is a stabilizator of automorphism of
  order 3.
] <th:l2017-quasifields-hentzel-rua-subfields>

We introduce the following subsets for the description of spectra:

$
  K(m,n,k) = {x in HRu | |x|_l = m, |x|_r = n, |x| = k},
  quad m,n,k in NN.
$

It was shown that $K(7,7,7) union {0,e}$ is an union of all subfields of
order 8. Evidently, that $K(3,3,3) union {0,e}$ is a subfield of order 4.
Moreover,

$
  |K(6,6,6)| = 12, quad |K(7,7,6)| = 6, quad
  |K(12,12,7)| = 6, quad |K(15,15,5)| = 6,
$

and also we have

$
  HRu^* = K(1,1,1) union K(3,3,3) union K(7,7,7) union K(6,6,6)
  union K(7,7,6) union K(12,12,7) union K(15,15,5).
$

Using these equalities we show that the loop $HRu^*$ is one-generated.

#lemma[
  For any $n >= 10$ the loop $HRu^*$ is an union of all $n$-th degrees of any
  element $x in K(6,6,6) union K(7,7,6) union K(12,12,7)
  union K(15,15,5)$.
] <lem:l2017-quasifields-hentzel-rua-powers>

Exacting this statement, we find all spectra.

#source(8, printed: 695)

#theorem[
  The spectrum of the loop $HRu^*$ is ${1,3,5,6,7}$. The left and right spectra
  coincide with ${1,3,6,7,12,15}$.
] <th:l2017-quasifields-hentzel-rua-spectra>

Thus, the semifield $HRu$ has no elements with left or right order
$63 = |HRu| - 1$, and hence it is not primitive.
