#import "../../main-defs.typ": source
#import "../../numbering.typ": family-counter
#import "defs.typ": *

=== Some lemmas and quasifields with associative powers
<sec:l2017-quasifields-associative-powers>

It is easy to show that the orders of elements of any finite loop are also
finite.

#lemma[The order of finite loop is not less than order of any its element.]
<lem:l2017-quasifields-element-order-bound>

#proof(qed: true)[
  The proof of order boundedness of any element $v$ from finite loop
  $L = (L,compose)$ uses right-ordered and left-ordered powers. It is clear that
  such the powers are no more than $|L|$ pairwise distinct elements.

  Choose the sequence $e,v^(1 ")"),v^(2 ")"),dots,v^(m ")")$, that contains two
  equal elements with minimal $m >= 1$. Evidently that $v^(m ")") = v^(j ")")$
  for some $j$, $0 <= j < m$. If $j > 0$ that both elements $v^(m-1 ")")$ and
  $v^(j-1 ")")$ are the solutions of the equation $y compose v = v^(j ")")$ in a
  loop $L$ and so are equal, that contradicts to choice of $m$. Hence, $j = 0$
  and $v^(m ")") = e$. From the proved we have

  $ |v| <= |v|_r <= |L|, quad |v| <= |v|_l <= |L|. $
]

#lemma[
  Let $alpha$ be $m$-th power of an element $v$ from commutative quasigroup. If
  $alpha$ contains $v^2$ as a sub-product no more an once, then
  $alpha = v^("(" m)$.
] <lem:l2017-quasifields-single-square-power>

#proof(qed: true)[
  Let’s suppose that $m >= 3$ (the case $m <= 2$ is trivial). By induction, the
  lemma is proved for $k$-th powers for any $k$. Using commutativity, we can
  suppose also that all multiplications of $v^2$ in $alpha$ are only from the
  right. Then the minimal sub-product in $alpha$ that contains $v^2$ and is not
  $v^2$ is of a form $v^3$; else $v^2$ is in $alpha$ more than once.
  Analogously, the next minimal sub-product in $alpha$ equals to $v^4$. So we
  get the equality $alpha = v^("(" m)$.
]

#lemma[
  Any power $> 1$ of an element $v$ from commutative quasigroup is a product,
  with suitable positioning of brackets, of elements $v^("(" m)$, $m >= 2$, and,
  possible, of products at least two such factors to $v$.
] <lem:l2017-quasifields-power-factorization>

The quasifields with associative powers are the most studied. First of all it is
alternative semifield. In a finite case it is a field, according Artin.

In 1952 Albert [@bib:l2017-quasifields-Albert1952] proved the following theorem.

#theorem[
  Any finite semifield with associative powers of characteristic $p != 2$, the
  center of which contains more than 5 elements, is a finite field.
] <th:l2017-quasifields-power-associative-field>

The associative quasifield is called _nearfield_. In 1936 Zassenhaus
[@bib:l2017-quasifields-Zassenhaus1936] described all finite nearfields. They
are exhausted by Dickson nearfields and 7 exceptional Zassenhaus nearfields of
order $p^2$ for prime $p = 5,7,11,23,29$ and $59$ (see also Hall
[@bib:l2017-quasifields-Hall1976, Theorem 20.7.2]).

The known description of sub-nearfields for finite nearfield is considerably
transferred from the description of subfields for finite field (see Dancs
[@bib:l2017-quasifields-Dancs1971]). It is easy to prove

#lemma[A nearfield $Q$ is a finite field if its loop $Q^*$ is one-generated.]
<lem:l2017-quasifields-one-generated-nearfield>

In connection with the statements of Proposition
@prop:l2017-quasifields-prime-subfield (i) and Corollary
@cor:l2017-quasifields-central-prime-subfield we note that the center even of
finite nearfield is not necessary a field.

#family-counter("rem").update(0)
#remark[
  Let $N$ be the exceptional Zassenhaus nearfield of order 25
  [@bib:l2017-quasifields-Hall1976, page 420]. Then the loop $N^*$ is isomorphic
  to the group $SL(2, 3)$ with the center of order 2. Therefore the center of
  nearfield $N$ equals ${0,e,-e}$ and coincides no prime subfield of $N$.
] <rem:l2017-quasifields-nearfield-center>

The projective plane that is coordinatized by nearfield is called a _nearfield
plane_. We now consider more wide class of translation planes which are
coordinatized by Moufang quasifield, i.e., the quasifield with Moufang loop (cf.
[@bib:l2017-quasifields-Hall1976, Theorem 20.5.3]). The loop $M$ is called
_Moufang loop_ if for all $x,y,z in M$ the following holds:

$
  (x y)(z x) = (x(y z))x, quad ((x y)x)z = x(y(x z)), quad
  x(y(z y)) = ((x y)z)y.
$

The Moufang loops of order less than 32 were described by Chein in 1974,
[@bib:l2017-quasifields-Chein1974]. Some group-theoretic theorems (Lagrange,
Sylow and Hall theorems) are transferred to Moufang loops (Grishkov,
Zavarnitsyn, 2005–2013,
[@bib:l2017-quasifields-Grishkov2005–@bib:l2017-quasifields-Grishkov2013];
Gagola, 2010, [@bib:l2017-quasifields-Gagola2010]). See also Liebeck, 1987
[@bib:l2017-quasifields-Liebeck1987]. It is possible to use these results for
classification of certain Moufang quasifields.
