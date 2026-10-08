#import "../../main-defs.typ": *
#import "defs.typ": *

#heading(level: 3)[
  The Ring $R_n lr((K,J))$ for a Strongly Maximal Ideal $J$
] <sec:l2005-sylow-strongly-maximal>

Let $K$ be an associative ring with the identity and $J$ be an ideal of $K$.
Suleimanova’s example in [@bib:l2005-sylow-Levchuk2002Radical] shows that the
analogue of Lemma @lem:l2005-sylow-normal-lie for $R=R_n lr((K,J))$ (see Section
@sec:l2005-sylow-strongly-maximal) with $J != 0$ does not always hold, see also
[@bib:l2005-sylow-Kourovka1992, Question 10.19]. Therefore investigations of
automorphisms of the adjoint group $G(R)$ and of the associated Lie ring
$Lambda(R)$ have some additional difficulties.

We use an ideal $J$ of $K$ with certain specific properties. If $J$ coincides
with a two-sided or one-sided annihilator of $J^t$ in $K$ for an integer $t>=0$
(with $J^0=K$), then the structure of the automorphism group $Aut R$ coinciding
with $Aut G(R) inter Aut Lambda(R)$, has been described in
[@bib:l2005-sylow-Kuzucuoglu2001].

By [@bib:l2005-sylow-Kuzucuoglu2000], an ideal $J$ of a commutative ring $K$ is
called a _strongly maximal ideal_ if, for any $J$-submodule $T$ of $K$, every
ideal of $K$ which is between $T$ and $J T$ is equal to $T$ or $J T$. Consider
the following generalization for noncommutative cases.

#definition[
  An ideal $J$ of a ring $K$ is called _strongly maximal_ if for every one-sided
  $J$-submodule $T$ of $K$ the equality $J T=T J$ holds and every one-sided
  ideal of $K$ which is between $T$ and $J T$, equals $T$ or $J T$.
] <def:l2005-sylow-strongly-maximal>

We note that ideals of the ring $R=R_n lr((K,J))$
[@bib:l2005-sylow-Kuzucuoglu2000] and of the associated Lie ring $Lambda(R)$ and
also normal subgroups of the adjoint group $G(R)$
[@bib:l2005-sylow-Levchuk2002Radical] have been
#source(4, printed: 228)
described for the case of a strongly maximal ideal $J$ of a commutative ring
$K$. The case of zero ideal $J$ of a division ring $K$ had been studied in
[@bib:l2005-sylow-Levchuk1992]. Also, G. Suleimanova investigates other
noncommutative cases.

By [@bib:l2005-sylow-Kuzucuoglu2000, Proposition 2.5], maximal ideals of the
rings $Z$ and $Z_m$ are strongly maximal. It is clear that every strongly
maximal ideal of a ring $K$ (not coinciding with $K$) is maximal. However, the
inverse is not true. For instance, in the ring $Z[x]$ of polynomials in one
indeterminate $x$ over $Z$, the ideal $p Z+x Z[x]$ for an arbitrary prime $p$ is
maximal but it is not strongly maximal [@bib:l2005-sylow-Kuzucuoglu2000, § 2].

Let $R$ be an arbitrary (associative) ring with the identity. We now consider
certain ideals of the ring $R[x]$ of polynomials and the ring $R[[x]]$ of formal
power series in (commutative) indeterminate $x$ over $R$. It is easy to see that
the ideal $P+(x)$ of these rings for any maximal ideal $P$ of $R$ is maximal.

#lemma[
  Let $P$ be a proper ideal of $R$, $K$ be the ring $R[x]$ of polynomials or the
  ring $R[[x]]$ of power series in indeterminate $x$ over $R$ and $J=P+x K$.
  Then for a positive integer $t$ inclusions
  $J^(t+1) subset J^(t+1)+x^t K subset.eq J^t$ hold. The last inclusion is an
  equality if and only if $P^2=P$.
] <lem:l2005-sylow-polynomial-powers>
#proof[
  It is easy to show by induction that
  $ J^t=P^t+x P^(t-1)+dots+x^(t-1)P+x^t K. $
  <pass:l2005-sylow-polynomial-power>

  In particular, $J^t=P[x]+x^t K$ at $P^2=P$ and $x^t in.not J^(t+1)$ $(t>0)$.
  Similarly, we obtain
  $ J^(t+1)+x^t K=P^(t+1)+x P^t+dots+x^(t-1)P^2+x^t K. $
  <pass:l2005-sylow-polynomial-step>

  It follows that the equality $J^t=J^(t+1)+x^t K$ is satisfied if and only if
  $P^2=P$. The lemma is proved.
]

Consider now the ring of formal power series in one indeterminate $x$, see p.
154 and III.5.4(iv) of [@bib:l2005-sylow-Hungerford1974].

#proposition[
  The principal ideal $(x)$ of the ring $R[[x]]$ of power series over a division
  ring $R$ is strongly maximal.
] <prop:l2005-sylow-power-series>
#proof[
  Let $K=R[[x]]$ and $J=(x)$. Taking into account that $x a=a x$ for all
  $a in R$, we obtain $J^t=x^t K$ for $t>=0$. By
  [@bib:l2005-sylow-Hungerford1974, III.5.10], the units in $K$ are precisely
  those power series with a nonzero constant term. Every nonzero element of $K$
  is of the form $x^t u$ with $u in K$ as a unit. We have
  $
    x^t u K=K x^t u=x^t K=J^t, quad
    x^t u J=x^t u x K=J^(t+1)=J x^t u.
  $
  <pass:l2005-sylow-series-ideals>

  Therefore $K$ is a principal ideal ring whose only ideals are $0$ and $J^t$
  for all $t>=0$, cf. also [@bib:l2005-sylow-Hungerford1974, p. 157, Ex. 10].
  Choose an arbitrary nonzero one-sided $J$-submodule $T$ of $K$. Then there
  exists some nonzero additive subgroup $A$ of $R$ and an integer $t>=0$ such
  that $T=x^t A+J^(t+1)$. Consequently, $J T=T J=J^(t+1)$. It follows
  #source(5, printed: 229)
  that if $T != J^t$, then the ideal $J^(t+1)$ is unique which is between $T$
  and $J T$. This completes the proof.
]

The following theorem gives general examples of strongly maximal ideals.

#theorem[
  If a commutative principal ideal ring $R$ with the identity is a domain or a
  local ring, then every maximal ideal of $R$ is strongly maximal.
] <th:l2005-sylow-principal-ideals>
#proof[
  Let a ring $R$ be chosen as in the theorem, $J$ be a maximal ideal and $T$ be
  an arbitrary nonzero $J$-submodule of $R$. We now consider an arbitrary
  nonzero ideal $S$ of $R$ which is between $T$ and $J T$.

  Choose elements $f,s$ of $R$ such that $S=(s)$ and $J=(f)$. By
  [@bib:l2005-sylow-Hungerford1974, III.3.6 and Ex. 12, p. 141], also there
  exists the greatest common divisor $d$ of all nonzero elements $g in T$. Since
  sets $J g$ for $g in T$ generate the additive subgroup $J T$, so
  $
    J T=(J R)T=J d=(f d), quad
    J T=(f d) subset S=(s) subset T subset (d).
  $
  <pass:l2005-sylow-principal-chain>

  It follows that $s=k d$ and $f d=s m=k m d$ for some $k,m in R$.

  If $R$ is a domain, then we obtain the equality $f=k m$ and inclusions
  $(f) subset (k) subset R$. It shows that either $(f)=(k)$ and $S=J T$ or
  $(k)=R$, $S=(d)$ and hence $S=T$.

  Suppose now that the ring $R$ is local. If $S=(d)$, then $S=T=(d)$, as above.
  Assume that $S != (d)$. Then $k$ is not a unit of $R$. Consequently,
  $k in (f)$, $S=(k d) subset (f d)=J T$ and therefore $S=J T$. The theorem is
  proved.
]

It is not difficult to show that every proper ideal of any local principal ideal
ring with the identity is equal to a degree $J^t$ of a maximal ideal $J$.

The following lemma shows that the property of strong maximality of ideals is
kept under ring homomorphisms.

#lemma[
  Let $J$ be a strongly maximal ideal of a ring $K$. Then the image of $J$ under
  an arbitrary ring homomorphism of $K$ is a strongly maximal ideal.
] <lem:l2005-sylow-homomorphic-image>
#proof[
  Let $macron$ be a homomorphism of the ring $K$ and $I$ be the kernel of this
  homomorphism. Choosing an arbitrary left or right $overline(J)$-submodule
  $T_1$ of $overline(K)$ we set $T=lr({a in K | overline(a) in T_1})$. Then $T$
  is a one-sided $J$-submodule of $K$ which contains $I$, so $J T=T J$ and,
  hence, $overline(J) T_1=T_1 overline(J)$. Let $S_1$ be an ideal of
  $overline(K)$ such that $T_1 supset S_1 supset overline(J) T_1$. Then there is
  an ideal $S$ of $K$ with conditions $overline(S)=S_1$ and
  $T supset S supset T J+I supset T J$. At least two or three of these
  inclusions are equalities because $J$ is a strongly maximal ideal of $K$. It
  follows that equality $S_1=T_1$ or $S_1=T_1 overline(J)$ is satisfied. This
  completes the proof.
]
