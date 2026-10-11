#import "../../main-defs.typ": source
#import "defs.typ": *

=== Some remarks and questions <sec:l2017-quasifields-questions>

Recall that the groupoid $L$ with binary operation $dot$ is called a
_quasigroup_, if for all $a,b in L$ any equation $a x = b$ or $x a = b$ is
uniquely solvable in $L$. A quasigroup is a _loop_, if it has an identity $e$
(zero $0$ in the additive terminology). Thus, the group is an associative loop.

#definition[
  The finite set $Q$ with binary operations of addition $+$ and multiplication
  $dot$ is called a _right quasifield_, if

  + $(Q,+)$ is an abelian group,
  + $Q^* := (Q without {0}, dot)$ is a loop,
  + $x 0 = 0$ ($x in Q$),
  + #source(2, printed: 689) it is satisfied the right distributivity
    $(y+z)x = y x + z x$ ($x,y,z in Q$).
] <def:l2017-quasifields-right-quasifield>

Evidently the right distributivity and 1) give the condition $0 x = 0$.

Analogously finite left quasifield is defined with replacement of right
distributivity onto left distributivity. Further we say “quasifield” instead of
“right quasifield”.

#remark[
  By Hughes, Piper [@bib:l2017-quasifields-Hughes1973], a system $(Q,+,dot)$
  with arbitrary $Q$ and conditions 1)–4) is said to be a _weak quasifield_ and,
  also, a _quasifield_, if it is uniquely solvable in $Q$ any equation
  $x a = x b + c$ ($a,b,c in Q$, $a != b$). According to
  [@bib:l2017-quasifields-Hughes1973, 7.3], any finite weak quasifield is a
  quasifield.
] <rem:l2017-quasifields-weak-quasifield>

We now show that a characteristic of any quasifield is always determined,
similarly to fields, and if the characteristic is positive, then the statement
about minimal subfield is also satisfied.

Clearly that any quasifield $Q$ gives a two-sided $ZZ$-module, if for any
integer coefficient $k >= 0$ we set $0 x := 0 = x 0$ and also

$
  k x := underbrace(x+x+dots+x, k "times") = x k,
  quad (-k)x := -(k x) = x(-k) quad (x in Q).
$

#proposition[
  Let $Q$ be a right quasifield with the identity $e$. Then:

  #enum(
    numbering: "i)",
    [$pi: k arrow.r k e$ ($k in ZZ$) is a homomorphism of the integer ring $ZZ$
      into $Q$ and $Q$ is a left $pi(ZZ)$-module;],
    [$pi(ZZ) tilde.eq ZZ$ for $p = 0$, where $p = char Q := char pi(ZZ)$;],
    [if $p > 0$, then $pi(ZZ) tilde.eq ZZ_p$ and $pi(ZZ)$ is unique minimal
      subfield of $Q$.],
  )
] <prop:l2017-quasifields-prime-subfield>

#proof(qed: true)[
  Evidently, $pi$ preserves addition $+$ in $Q$. The associativity of addition
  and right distributivity in $Q$ also give

  $ k e dot m e = k(e dot (m e)) = k(m e) = (k m)e quad (k,m in ZZ). $

  Thus, $pi$ is a homomorphism of ring $ZZ$ into $Q$. Since any quasifield has
  no zero-divisors we obtain that $pi(ZZ)$ is a domain.

  Taking into account the equalities $m e dot x = m(e x) = m x$ we have

  $
    (k e) dot (m e dot x) = k(e dot (m e dot x)) = (k m)x
    = (k e dot m e) dot x,
  $
  $ m e dot (x+y) = m(x+y) = m x + m y = (m e dot x) + (m e dot y). $

  It follows that $Q$ is a left $pi(ZZ)$-module. Clearly, if $pi$ is an
  isomorphism, then $pi(ZZ) tilde.eq ZZ$. Let $Ker(pi) != 0$. Then $pi(ZZ)$ is a
  finite domain and therefore $pi(ZZ) tilde.eq ZZ_p$ for $p := char pi(ZZ) > 0$.
]

Since any semifield are a right and left quasifield, we obtain

#corollary[The center of any semifield contains $pi(ZZ)$.]
<cor:l2017-quasifields-central-prime-subfield>

It seems that this statement is not true, for instance, for near-fields, see
§~@sec:l2017-quasifields-associative-powers. The order of any finite projective
translation plane coincides with the order of its coordinatizing quasifield
(§~@sec:l2017-quasifields-planes). It follows directly

#corollary[
  The order of any finite quasifield and hence the order of any finite
  projective translation plane equals to a prime number degree.
] <cor:l2017-quasifields-prime-power-order>

It is well-known that all quasifield of even orders $2,4$ and $8$ are the
fields. The proper quasifield of order $p^2$ for prime $p > 2$ is constructed by
Dickson (1906, [@bib:l2017-quasifields-Dickson1906]). According to Knuth
[@bib:l2017-quasifields-Knuth1963], it is true

#theorem[
  The proper semifield of order $p^n$ for a prime $p$ exists if and only if
  $n >= 3$ and $p^n >= 16$.
] <th:l2017-quasifields-proper-semifield-orders>

Let $L$ be a multiplicative loop. A product of $m$ its multipliers is said to be
_$m$-th degree_ of fixed element $v$, if every multiplier coincides with $v$.
The smallest integer $m >= 1$ such that there exists $m$-th degree of $v$, which
is equal to the identity, is called the _order_ of $v$ and denoted by $|v|$. The
set of orders of all elements is called a _spectrum_ of loop $L$.

Analogously, using the right-ordered and the left-ordered $m$-th degrees

$
  v^(m ")") = v^(m-1 ")") dot v,
  quad v^("(" m) = v dot v^("(" m-1),
  quad v^(1 ")") = v = v^("(" 1),
$

we define right order $|v|_r$ and left order $|v|_l$ of $v$ and, also, right and
left spectra of $L$, respectively.

The following problems for finite proper quasifields were presented in 2013 by
first author at research seminar of chair of algebra of Moscow State University
and in [@bib:l2017-quasifields-Levchuk2014Conference,
@bib:l2017-quasifields-Levchuk2015].

#source(3, printed: 690)

(A) Enumerate maximal subfields and their possible orders.

(B) Find the finite quasifields $S$ with not-one-generated loop $S^*$.

Hypotheses: the loop of any finite semifield is one-generated.

(C) What loop spectra $S^*$ of finite semifields and quasifields are possible?

(D) Find the automorphism group $Aut S$.

Note that hypotheses (B) is more weak than well-known Wene’s hypotheses (1991):
any finite semifield is right-primitive.

A semifield $S$ and multiplicative loop $S^*$ are called _right-primitive_, if
all elements of loop $S^*$ are the right-ordered degrees of fixed element (in
other words, there exists an element $v in S^*$ such that $|v|_r = |S^*|$).

Wene’s hypotheses was refuted by Rúa [@bib:l2017-quasifields-Rua2004] in 2004.

Clearly that complete classification of quasifields or semifields means
classification up to isomorphisms. On the other hand, classification of their up
to isotopisms (see §~@sec:l2017-quasifields-planes) is important for
classification of projective translation planes. It is shown by the following
theorem of Albert [@bib:l2017-quasifields-Albert1960].

#theorem[
  Projective semifield planes are isomorphic if and only if their coordinatizing
  semifields are isotopic.
] <th:l2017-quasifields-albert-isotopy>
