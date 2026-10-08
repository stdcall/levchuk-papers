#import "defs.typ": *
#import "../../collection.typ": article-introduction
#article-introduction[Introduction]
<sec:l2001-automorphisms-introduction>
This paper is devoted to the study of automorphisms of matrix radical rings. The
area has been under active investigation since the 1950s. Automorphisms of the
algebra $NT_n lr((K))$ of all (lower) niltriangular $n times n$ matrices over a
field $K$ were described by Dubisch and Perlis
[@bib:l2001-automorphisms-Dubish1951, Theorem 5-7]. It is easy to verify that
the automorphism group $Aut R$ of any radical ring $R$ coincides with the
intersection of the automorphism group of the adjoint group $G(R)$ and the
automorphism group of the associated Lie ring $Lambda(R)$ of $R$. The adjoint
group of $NT_n lr((K))$ is isomorphic to the unitriangular group $UT_n lr((K))$.
If $K$ is a finite field, then the group $UT_n lr((K))$ is a Sylow subgroup of
$GL_n lr((K))$ and its automorphisms were studied in
[@bib:l2001-automorphisms-Maginnis1993], [@bib:l2001-automorphisms-McBride1983],
[@bib:l2001-automorphisms-Pavlov1952], [@bib:l2001-automorphisms-Weir1955]. For
arbitrary associative ring $K$ with identity automorphism groups of #source(
  2,
  printed: 474,
)$NT_n lr((K))$, $G(NT_n lr((K)))$ and $Lambda(NT_n lr((K)))$ were described in
[@bib:l2001-automorphisms-Levchuk1975; @bib:l2001-automorphisms-Levchuk1983,
Theorem~@th:l1983-main-automorphisms]; see surveys in
[@bib:l2001-automorphisms-Hahn1984], [@bib:l2001-automorphisms-Merzlyakov1978].
This result was extended to all Chevalley groups in
[@bib:l2001-automorphisms-Levchuk1990], [@bib:l2001-automorphisms-Levchuk1992]
and so the problem (1.5) of [@bib:l2001-automorphisms-Kondratyev1986] on
unipotent subgroups of Chevalley groups was solved. On the other hand, the
question of description of automorphisms of Sylow $p$-subgroups of Chevalley
groups over $Z_(p^m)$ for $m>1$ [@bib:l2001-automorphisms-Kourovka1992, Question
12.42] is still open. Let $M_n lr((J))$ be the ring of all $n times n$ matrices
over an ideal $J$ of $K$ and
$ R_n lr((K,J)) := NT_n lr((K))+M_n lr((J)). $
By [@bib:l2001-automorphisms-Kargapolov1979, 11.3.3] Sylow $p$-subgroups of the
group $GL_n lr((Z_(p^m)))$ are isomorphic to the adjoint group of the ring
$R_n lr((Z_(p^m),(p)))$. Note that for any radical ring $R_n lr((K,J))$
investigations of the question about description of automorphism groups
$Aut G(R)$ and $Aut Lambda(R)$ for $R=R_n lr((K,J))$ have some additional
difficulties. In fact, general results in
[@bib:l2001-automorphisms-Levchuk1975], [@bib:l2001-automorphisms-Levchuk1983]
were found by using close structure connections between the associated Lie ring
and the adjoint group of $NT_n lr((K))$. However, for $R_n lr((K,J))$, these
structural connections do not hold; see [@bib:l2001-automorphisms-Kourovka1992,
Question 10.19; @bib:l2001-automorphisms-Kuzucuoglu2000].

The aim of the present paper is to describe the automorphism group
$Aut R_n lr((K,J))$ for arbitrary $K$ and quasi-regular ideal $J$ with certain
specific properties. Theorems @th:l2001-automorphisms-main and
@th:l2001-automorphisms-structure establish the structure of the automorphism
group $Aut R_n lr((K,J))$ when $J$ coincides with a one-sided or two-sided
annihilator of $J^t$ in $K$ for $t>=0$. As a corollary, Proposition
@prop:l2001-automorphisms-module describes automorphisms of $K$-algebra
$R_n lr((K,J))$. The order of $Aut R_n lr((K,J))$ is given in Proposition
@prop:l2001-automorphisms-order for any finite ring $K$ and $J$ as in Theorem
@th:l2001-automorphisms-main. In particular, for an arbitrary divisor $d$ of $m$
$(1<=d<m)$ we obtain
$ abs(Aut R_2 lr((Z_(p^m),(p^d))))=(p^m-p^(m-1)) dot p^(2m) $
and
$
  abs(Aut R_n lr((Z_(p^m),(p^d))))=
  (p^m-p^(m-1))^(n-1) dot p^((2m-d) dot binom(n, 2)+d(n-2)), quad n>2.
$
