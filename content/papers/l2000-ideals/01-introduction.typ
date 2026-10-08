#import "../../collection.typ": article-introduction
#import "defs.typ": *

#article-introduction[Introduction] <sec:l2000-ideals-introduction>

Let $NT_n lr((K))$ be the ring of all (lower niltriangular) $n times n$ matrices
over an associative ring $K$ with zeros on and above the main diagonal. Let
$M_n lr((J))$ be the ring of all $n times n$ matrices over an ideal $J$ of $K$.
In this paper we investigate ideals and structural connections of the ring
$NT_n lr((K))+M_n lr((J))$, which is denoted by $R_n lr((K,J))$.

It was shown in [@bib:l2000-ideals-Levchuk1976] that for $R=NT_n lr((K))$ and
$K=K^2$ the class $OmG(R)$ of all normal subgroups of the adjoint group of the
ring $R$ coincides with the class
#source(3, printed: "3504")
$OmL(R)$ of all ideals of associated Lie ring. The question about
characterization of all associative radical rings $R$ satisfying $OmL(R)=OmG(R)$
(see [@bib:l2000-ideals-Kourovka1992, question~10.19]) is still open. It is
clear that if $J$ is a quasi-regular ideal, then $R_n lr((K,J))$ is a radical
(Jacobson) ring. If the quasi-regular ideal $J$ contains an element $x$
satisfying $x^2!=0$, then Example~@exm:l2000-ideals-determinant-kernel below
shows, for $n>=2$, that there exists a normal subgroup of the adjoint group
which is not an ideal of the groupoid $(R_n lr((K,J)),ast)$ with respect to
associated Lie multiplication $alpha ast beta=alpha beta-beta alpha$. On the
other hand we show in Section~@sec:l2000-ideals-structural that
Example~@exm:l2000-ideals-determinant-kernel gives also a new counterexample to
the question in [@bib:l2000-ideals-Levchuk1976,
Remark~@rem:l1976-normal-groupoid-question] and [@bib:l2000-ideals-Kourovka1980,
question~6.19]. The first counterexample to this question was constructed by
E.~I.~Khukhro (cf. comments to the question~6.19 in
[@bib:l2000-ideals-Kourovka1980]).

Notice that all ideals of any radical ring $R$ are placed in the intersection
$OmG(R) inter OmL(R)$. R.~Dubisch and S.~Perlis [@bib:l2000-ideals-Dubisch1951,
Thm.~9] gave a uniform construction of all ideals of the algebra $NT_n lr((K))$
over a field $K$. Similar construction of ideals of the ring
$NT_n lr((K)) (=R_n lr((K,0)))$ over a division ring $K$ has been found in
V.~M.~Levchuk [@bib:l2000-ideals-Levchuk1976, §~@sec:l1976-lie-ideals]. It is
impossible to give a similar description of the ideals of $NT_n lr((K))$ for the
case $K=ZZ$ (see [@bib:l2000-ideals-Levchuk1976]).

The aim of Section~@sec:l2000-ideals-construction is to get a description of all
ideals of $R_n lr((K,J))$ in an effective way within the line pointed in
[@bib:l2000-ideals-Dubisch1951] and [@bib:l2000-ideals-Levchuk1976]. In this
section we assume that $K$ is a commutative ring with identity. Our main
Theorem~@th:l2000-ideals-boundary-classification describes all ideals of
$R_n lr((K,J))$ when $J$ is a strongly maximal ideal of $K$
(Definition~@def:l2000-ideals-strongly-maximal), in particular, when $K=ZZ$ or
$K=ZZ_m$, $m>1$ and $J$ is a maximal ideal of $K$. This description is similar
to the ones in [@bib:l2000-ideals-Dubisch1951], [@bib:l2000-ideals-Levchuk1976]
and coincides with them, if $K$ is a field and $J=0$. At the end of
Section~@sec:l2000-ideals-construction we give an example of a maximal ideal
which is not strongly maximal.

In Section~@sec:l2000-ideals-abelian we describe all maximal abelian ideals of
the ring $R_n lr((K,J))$ when $K=ZZ_(p^m)$ and $J$ is the strongly maximal ideal
$(p)$. Theorem~@th:l2000-ideals-maximal-abelian shows that if $m$ is even, then
$M_n lr((J^(m/2)))$ is a unique maximal abelian ideal of $R_n lr((K,J))$. But if
$m$ is an odd integer, then the ring $R_n lr((K,J))$ has precisely $(n-2)p+1$ of
maximal abelian ideals. In proof of Theorem~@th:l2000-ideals-maximal-abelian we
also use the known description of maximal abelian ideals of the ring
$NT_n lr((F))$ over a field $F$ (see [@bib:l2000-ideals-Levchuk1976]).

We denote by $e_(i j)$ matrices unit and by $pi_(k m)$ the canonical projection
on $M_n lr((K))$, see [@bib:l2000-ideals-Hungerford1974]. Thus,
$pi_(k m) lr((e_(i j)))=1$ if $(k,m)=(i,j)$ and $pi_(k m) lr((e_(i j)))=0$ if
$(k,m)!=(i,j)$.
