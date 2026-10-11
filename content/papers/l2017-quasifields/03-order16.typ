#import "../../main-defs.typ": source
#import "defs.typ": *

=== Semifields of order 16 <sec:l2017-quasifields-order16>

The proper finite semifields are completely classified only for smallest
possible orders. In this section we consider the problems (A)–(D) for semifields
of smallest even order 16.

According to Kleinfeld, the number of proper semifields of order 16, up to
isomorphisms, equals to 23. These semifields form two isotopic classes of 18
($V_i$, $1 <= i <= 18$) and 5 ($T_24,T_25,T_35,T_45$ and $T_50$) pairwise
non-isomorphic semifields with the nuclei of order 2 and 4 respectively.

Up to isomorphisms and anti-isomorphisms, we restrict the list to 16 semifields.
For any ring (or quasifield) $R = (R,+,dot)$ the opposite ring
$R^"op" = (R,+,compose)$ is determined by $a compose b = b dot a$ ($a,b in R$).
It is clear that the rings $R^"op"$ and $R$ are anti-isomorphic.

#theorem[
  Any proper semifield of order 16 up to isomorphisms is either one of 7
  semifields $V_1,V_3,V_4,V_8,V_11,V_15,T_25$ or one of opposite semifields to
  them $V_6,V_7,V_5,V_9,V_14,V_16,T_50$, respectively, or one of 9 semifields
  $V_2,V_10,V_12,V_13,V_17,V_18,T_24,T_35,T_45$.
] <th:l2017-quasifields-order16-isomorphism>

Kleinfeld characterizes the Caley table of loop $W^*$ for any semifield
$W = V_i$ or $T_j$ by special generating sequence and forms the table as a latin
square. The multiplication laws for all 16 semifields are obtained in
[@bib:l2017-quasifields-Levchuk2015, Table 3]. All above questions for
semifields of order 16 are completely solved by Kravtsova, Levchuk and Shtukkert
([@bib:l2017-quasifields-Kravtsova2006– @bib:l2017-quasifields-Levchuk2015]).

Let $cal(M)$ be a set of all subfields of order 4 for given semifield. Then the
following Table~@tab:l2017-quasifields-order16 resumes results.

The Kleinfeld method is not suitable for semifields of order more than 16. The
general method to construct quasifields and translation planes will be presented
in the following section.

#source(4, printed: 691)

#figure(
  table(
    columns: 6,
    table.header(
      [Semifield $W$],
      [$|cal(M)|$],
      [Spectrum],
      [Right spectrum],
      [Left spectrum],
      [$|Aut W|$],
    ),
    [$V_1 tilde.eq V_6^"op"$],
    [0],
    [$ {1,4,5} $],
    [$ {1,5,6,15} $],
    [$ {1,6,15} $],
    [1],

    [$V_2$], [1], [$ {1,3,4,5,6} $], [$ {1,3,6,15} $], [$ {1,3,6,15} $], [2],
    [$V_3 tilde.eq V_7^"op"$],
    [0],
    [$ {1,4,5,6} $],
    [$ {1,5,6,15} $],
    [$ {1,5,6,15} $],
    [1],

    [$V_4 tilde.eq V_5^"op"$],
    [1],
    [$ {1,3,4,5,6} $],
    [$ {1,3,6,15} $],
    [$ {1,3,5,6,15} $],
    [1],

    [$V_8 tilde.eq V_9^"op"$],
    [2],
    [$ {1,3,4,5,6} $],
    [$ {1,3,6,15} $],
    [$ {1,3,5,6,15} $],
    [2],

    [$V_10$], [1], [$ {1,3,5,6} $], [$ {1,3,6,15} $], [$ {1,3,6,15} $], [3],
    [$V_11 tilde.eq V_14^"op"$],
    [1],
    [$ {1,3,4,5,6} $],
    [$ {1,3,5,6,15} $],
    [$ {1,3,6,15} $],
    [2],

    [$V_12$], [0], [$ {1,4,5,6} $], [$ {1,5,6,15} $], [$ {1,5,6,15} $], [1],
    [$V_13$], [4], [$ {1,3,5} $], [$ {1,3,15} $], [$ {1,3,15} $], [6],
    [$V_15 tilde.eq V_16^"op"$],
    [2],
    [$ {1,3,4,5} $],
    [$ {1,3,6,15} $],
    [$ {1,3,6,15} $],
    [2],

    [$V_17$],
    [1],
    [$ {1,3,4,5,6} $],
    [$ {1,3,5,6,15} $],
    [$ {1,3,5,6,15} $],
    [1],

    [$V_18$], [2], [$ {1,3,5,6} $], [$ {1,3,5,6,15} $], [$ {1,3,5,6,15} $], [2],
    [$T_24$],
    [2],
    [$ {1,3,4,5,6} $],
    [$ {1,3,5,6,15} $],
    [$ {1,3,5,6,15} $],
    [2],

    [$T_25 tilde.eq T_50^"op"$],
    [2],
    [$ {1,3,4,5,6} $],
    [$ {1,3,5,6,15} $],
    [$ {1,3,6,15} $],
    [2],

    [$T_35$], [1], [$ {1,3,4,5,6} $], [$ {1,3,6,15} $], [$ {1,3,6,15} $], [3],
    [$T_45$], [3], [$ {1,3,5} $], [$ {1,3,5,15} $], [$ {1,3,5,15} $], [4],
  ),
  kind: table,
  caption: [The structure of non-isomorphic semifields of order 16],
) <tab:l2017-quasifields-order16>
