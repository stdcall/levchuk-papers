#import "../../main-defs.typ": source
#import "defs.typ": *

#source(6, printed: 693)

=== Wene’s conjecture <sec:l2017-quasifields-wene-conjecture>

In 1991 Wene [@bib:l2017-quasifields-Wene1991] wrote the hypotheses: any finite
semifield $D$ is right or left primitive, i.e. every element of the loop $D^*$
is a the set of right- or left-ordered powers of an element in a semifield $D$.
In 2004 Rúa [@bib:l2017-quasifields-Rua2004] has indicated a counter-example to
Wene’s conjecture, using Knuth’s semifield of order 32\. This Knuth–Rúa’s
semifield is neither right nor left primitive. The second counter-example gives
a Hentzel–Rúa’s semifield of order 64 [@bib:l2017-quasifields-Hentzel2007],
which was constructed in 2007. We consider both counter-examples detail in
§§~@sec:l2017-quasifields-order32 and @sec:l2017-quasifields-order64.

Now the primitivity investigations are completed for semifields of orders up to
125 (see [@bib:l2017-quasifields-Hentzel2007] and refers ibid). There exist only
two semifields of order $<= 125$ (as above), which are neither left nor right
primitive.

Note that the counter-examples of odd order are not known still.

Further in this section we consider some general known results in investigations
of primitivity. The following definition gives its weakening.

#definition[
  Any finite semifield $D$, which is $d$-dimensional over its center $Z(D)$, is
  said to be _left-ciclyc_ if for some element $a in D$ the semifield $D$ has
  $Z(D)$-base ${e,a,a^("(" 2),dots,a^("(" d-1)}$.
] <def:l2017-quasifields-left-cyclic>

Any left-primitive semifield is also left-ciclyc
[@bib:l2017-quasifields-Hentzel2007]. Nevertheless, even known non-primitive
semifields are left-ciclyc. The investigations of primitivity are based on the
properties of spread set. It is known that for any finite semifield $D$ with
$Z(D) tilde.eq GF(q)$ and spread set $Sigma$ the characteristic polynomial for
any matrix from $Sigma without {lambda E | lambda in GF(q)}$ has no linear
factors. The following theorem gives the main tool, which was used in
[@bib:l2017-quasifields-Hentzel2007].

#theorem[
  If $D$ is a finite semifield of dimension $d$ over its center $Z(D) = GF(q)$,
  then $w in D$ is a left primitive element of $D$ iff the characteristic
  polynomial of a linear map $L_w: D arrow.r D$, given by $L_w lr((x)) = w x$,
  is an irreducible primitive polynomial of degree $d$ over $Z(D)$.
] <th:l2017-quasifields-primitive-polynomial>

Some conditions from [@bib:l2017-quasifields-Rua2004] and
[@bib:l2017-quasifields-Gow2011] for primitivity of semifields gives

#theorem[
  Let $S$ be a semifield, which is $n$-dimensional over its center $GF(q)$. Then
  $S$ is left and right primitive, if either $n = 3$ or $n$ is prime and $q$ is
  large enough.
] <th:l2017-quasifields-primitivity-sufficient>

Cordero and Jha ([@bib:l2017-quasifields-Cordero2009] and
[@bib:l2017-quasifields-Cordero2010]) consider the problem of existence of
non-primitive quasifields and geometric conditions for primitivity.

#lemma[
  A non-primitive quasifield of square order $q^2$ exists iff $q > 4$.
] <lem:l2017-quasifields-nonprimitive-square-order>

#lemma[
  For all sufficiently large primes $p$, the semifields coordinatizing a
  semifield plane $Pi$ of order $p^5$ are all primitive (right and left) if $Pi$
  does not contain any proper subplane $Pi_0$ of order $> p$.
] <lem:l2017-quasifields-prime-fifth-power>
