#import "../../main-defs.typ": *
#import "../../statements.typ": repeated-statement
#import "defs.typ": *
#import "../../collection.typ": paper-abstract, paper-keywords

#paper-abstract(language: "en")[
  #source(1, printed: 380) Up to standard multipliers all non-standard
  automorphisms of free associative algebras and polynomial algebras are reduced
  to monic automorphisms of the maximal ideal, which are studied in the present
  paper. For non-standard automorphisms of some locally nilpotent matrix groups
  and rings it has turned out to be more efficient to use hypercentral
  automorphisms.
]

#paper-keywords(language: "en")[free associative algebra, polynomial algebra,
  finitary Chevalley group, unipotent subgroup, associated Lie ring, Jordan
  ring, automorphism.
]

#heading(level: 3, numbering: none)[Introduction]
<sec:l2008-monic-introduction>

Usually the first step on the road to describing the automorphisms of classical
algebras or groups is specifying its standard automorphisms. In this paper we
consider two typical cases when up to a multiplication by a standard
automorphism every non-standard automorphism can be written as a monic or
hypercentral automorphism which were introduced in
[@bib:l2008-monic-Dubisch1951] and [@bib:l2008-monic-Levchuk1992].

An automorphism (similarly, an endomorphism) of a ring or algebra $R$ is said to
be _monic_, if it induces the identity map on each factor $R^m/R^(m+1)$. The
analogous definition of monic endomorphisms of any group uses the factors of its
lower central series. If an automorphism acts like the identity modulo the m-th
hypercenter $Z_m lr((R)) != R$, then it is called _hypercentral_ or _central_
for $m = 1$.

Dubisch and Perlis [@bib:l2008-monic-Dubisch1951] described automorphisms of the
algebra $NT(n, F)$ of all $n times n$ matrices with zeros on and above the main
diagonal over a field $F$. Every monic automorphism of this algebra is the
product of an inner and central automorphisms. The monic automorphisms of the
ring $NT(n, K)$ ($n >= 3$) over an arbitrary associative ring $K$ with identity
have similar description, [@bib:l2008-monic-Levchuk1983]. However, it is
impossible to use monic automorphisms for the description of non-standard
automorphisms of the finitary ring $NT(Gamma, K)$ with any chain $Gamma$ of
matrix indices (§~@sec:l2008-monic-locally-nilpotent). It has #source(
  2,
  printed: 381,
) turned out to be more efficient to use hypercentral automorphisms describing
non-standard automorphisms of associated Lie and Jordan rings and of the
unitriangular group $UT(Gamma, K)$. This approach is also used in
§~@sec:l2008-monic-locally-nilpotent for the unipotent subgroups of some
finitary Chevalley groups.

The hyperannihilator series of a polynomial algebra $B_n = F[x_1,dots,x_n]$ in
commutative variables over an arbitrary field $F$ and of a free associative
algebra $A_n = F〈x_1,x_2,dots,x_n〉$ with the free generators
$x_1,x_2,dots,x_n$ is trivial. The center of $A_n$ consists of scalars for
$n >= 2$, whereas $B_n$ is commutative. In their ideal $R = 〈x_1,dots,x_n〉$,
there is no nonzero proper hypercenter, and the hyperannihilator series is
trivial, in spite of the fact that $inter.big_(k=1)^infinity R^k = 0$. The
problem of describing the automorphisms of $A_n$ and $B_n$
[@bib:l2008-monic-Kourovka2002, Question 3.3] is still open. It is agreed to
call the standard and non-standard automorphisms of these algebras,
respectively, _tame_ and _wild_, A. Czerniakiewicz
[@bib:l2008-monic-Czerniakiewicz1971], P. Cohn [@bib:l2008-monic-Cohn1985], etc.
Obviously, every automorphism of the ideal $R$ can be uniquely continued to one
of the whole algebra. In §~@sec:l2008-monic-free-algebras we prove

#repeated-statement("Corollary", [@cor:l2008-monic-reduction-to-monic])[
  Up to a multiplication by a tame automorphism, any automorphism of the
  algebras $A_n$ and $B_n$ is the continuation of a monic automorphism of $R$.
]

We study some properties of tame and wild automorphisms of the algebra $R$ and
the nilpotent factors $R/R^k$. The problem of automorphism lifting for some free
nilpotent groups and algebras is studied in [@bib:l2008-monic-Gupta1992],
[@bib:l2008-monic-Gupta1995]. In §~@sec:l2008-monic-abelian-factors we study
certain subgroups of $Aut R/R^k$ and bases of associated linear spaces, see
Theorem~@th:l2008-monic-wildness-criterion.
