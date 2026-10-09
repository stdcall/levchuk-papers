#import "defs.typ": *
=== The structure of the automorphism group
<sec:l2001-automorphisms-structure>
We investigate the structure of the automorphism group of a radical ring $R$ in
Theorem @th:l2001-automorphisms-main as above, $R=R_n lr((K,J))$. Consider the
subgroup series
$ F subset.eq B F subset.eq B F D subset.eq B F D A(K,J). $
<eq:l2001-automorphisms-subgroup-series>
We denote the multiplicative group of all invertible diagonal $n times n$
matrices over $K$ by $D_n lr((K))$ as usual. Denote by $B'_F$ (resp. $B_F$) the
subgroup of inner automorphisms that are induced by adjoint conjugations with
elements from $K e_(n 1)$ (resp.
$lr({K e_(n 1)+(Ann_K J)e_(n 2)+(Ann_K J)e_(n-1,1)}) inter R$). Let
$Lambda(K, J)$ (resp. $Lambda'(K,J)$) be the additive group of all homomorphisms
$lambda:K^+ arrow Ann_K J$ (resp. $lambda:J^+ arrow Ann_K J$) such that
$lambda(J)=0$ (resp. $lambda(J^2)=0$). We also denote by
$Lambda^((l)) lr((K,J))$ the additive group of all $K$-module homomorphisms of
the left $K$-module $J$ into the left annihilator of $J$. Using
@eq:l2001-automorphisms-almost-annihilator-conditions it is easy to verify that
maps
$
  zeta_i:Lambda(K, J) arrow B quad (1<=i<n), quad
  zeta_n:Lambda'(K,J) arrow B,
$
$ zeta^((l)):Lambda^((l)) lr((K,J)) arrow B $
(see Section @sec:l2001-automorphisms-fundamental) are group monomorphisms.

#theorem[
  Let $C(K)$ be the center of a ring $K$, $n>=2$, and
  $C(R)=Ann R+(J inter C(K))e$. Let $Ann_K J subset.eq J$ for $n=2$. Then

  (i) the subgroup series @eq:l2001-automorphisms-subgroup-series is normal in
  the group $B F D A(K,J)$ and equalities $(B F D) inter A(K,J)=D inter A(K,J)$,
  $(B F) inter D=F inter D$, and $F inter B=B_F$ hold;

  (ii) there exist the isomorphisms
  $
    D tilde.eq frac(D_n lr((K)), (K^("#") inter C(K))e), quad
    D inter A(K,J) tilde.eq K^("#")/(K^("#") inter C(K)),
  $
  $
    F tilde.eq (R,compose)/C(R), quad
    F inter D tilde.eq (sum_(i=1)^n J e_(i i),compose)/((J inter C(K))e);
  $

  (iii) the subgroup $B$ is a direct product of subgroups $B'$,
  $zeta_i lr((Lambda(K, J)))$, $1<=i<n$;

  (iv) if $J$ is a principal ideal $(a)$ and $a K=K a$, then
  $
    B'=B'_F times zeta_n lr((Lambda'(K,J)))
    times zeta^((l)) lr((Lambda^((l)) lr((K,J)))).
  $
] <th:l2001-automorphisms-structure>

#source(10, printed: 482)
#proof[
  (i) The subgroup $F$ is normal in $Aut R$ since
  $Aut R subset.eq Aut(R, compose)$ and $F ⊴ Aut(R, compose)$. It is easy to
  show that $D ⊴ D A(K,J)$. Similarly, normalizers in $Aut R$ of subgroups
  $zeta_i lr((Lambda(K, J)))$, $1<=i<n$, and $B'$ contain $D$ and $A(K,J)$. By
  @eq:l2001-automorphisms-annihilator-map subgroups $zeta_i lr((Lambda(K, J)))$
  and $B'$ generate $B$ so $B F$ is a normal subgroup of series
  @eq:l2001-automorphisms-subgroup-series. Consequently, the subgroup series
  @eq:l2001-automorphisms-subgroup-series of the group $B F D A(K,J)$ is normal.
  We get $(B F) inter D=F inter D$ since each intersection $(K e_(i j)) inter R$
  is $D$-invariant. Similarly, $(B F D) inter A(K,J)=D inter A(K,J)$. Clearly,
  $B_F subset.eq B inter F$ for $n>2$. It is also true for $n=2$ if $J$ is a
  quasi-regular ideal such that $Ann_K J subset.eq J$. Suppose the adjoint
  conjugation of $R$ by an element $alpha in R$ is equal to an element
  $chi in B$. By @eq:l2001-automorphisms-adjoint-conjugation we get
  $(K e_(i+1,i))*alpha subset.eq (e+alpha)Ann R=Ann R$ for $1<=i<n$ since
  $beta^chi-beta in Ann R$ for each $beta in NT_n lr((K))$. It follows that
  $chi in B_F$ and $F inter B=B_F$.

  (ii) The subgroup $F$ is isomorphic to the quotient-group of the adjoint group
  of $R$ by its center. The center of the ring $R$ coincides with the center of
  the adjoint group of it and contains $C(R)$. The inverse inclusion is also
  true since any matrix $alpha$ in the center of $R$ satisfies
  $alpha*(K e_(i+1,i))=alpha*(J e_(1 n))=0$, $1<=i<n$. Thus, the center of the
  adjoint group is equal to $C(R)$ and $F tilde.eq (R,compose)/C(R)$.

  The intersection $D inter A(K,J)$ coincides with the set of all conjugations
  of $R$ by matrices from $K^("#") e$. In fact, if $theta in D inter A(K,J)$ and
  $theta$ coincides with the conjugation of $R$ by a diagonal matrix
  $alpha in D_n lr((K))$, then all elements of the main diagonal of $alpha$
  pairwise coincide because $e_(i+1,i)^theta=e_(i+1,i)$, $1<=i<n$. The
  centralizer of $R$ in $D_n lr((K))$ coincides with $(K^("#") inter C(K))e$. It
  gives required isomorphisms of $D$ and $D inter A(K,J)$. Also, we get
  $F inter D tilde.eq (C(R)+(R inter (D_n lr((K))-e)),compose)/C(R)$. Since
  $C(R) inter R inter (D_n lr((K))-e)=C(R) inter (D_n lr((K))-e)
  =(J inter C(K))e$ we obtain the required isomorphism of $F inter D$.

  (iii) Note that the subring $NT_n lr((K))$ of $R$ is $B$-invariant and each
  almost-annihilator automorphism of $R$ induces the identity map on
  $NT_n lr((K))$. By using @eq:l2001-automorphisms-annihilator-map we obtain
  $B=B' times zeta_1 lr((Lambda(K, J))) times dots times
  zeta_(n-1) lr((Lambda(K, J)))$.

  (iv) Suppose that $J=a K=K a$ for some $a in K$. The decomposition of the
  subgroup $B'$ follows easily if we show that subgroups
  $zeta_n lr((Lambda'(K,J)))$, $zeta^((l)) lr((Lambda^((l)) lr((K,J))))$, and
  $B'_F$ generate the subgroup $B'$. Choose an arbitrary almost-annihilator
  automorphism $chi$ of the ring $R$. It is determined in
  @eq:l2001-automorphisms-almost-annihilator-map by means of a homomorphism
  $sigma:J^+ arrow K^+$ and endomorphisms $lambda,mu in End(J^+)$ which satisfy
  @eq:l2001-automorphisms-almost-annihilator-conditions. In particular, $lambda$
  and $mu$ are $K$-module endomorphisms of the left and right $K$-module $J$,
  respectively. By @eq:l2001-automorphisms-adjoint-conjugation we get
  $
    (-x e_(n 1)) compose (a e_(1 n))^chi compose x e_(n 1)
    in a e_(1 n)+(a^lambda+a x)e_(11)+(a^mu-x a)e_(n n)+K e_(n 1)
  $
  for all $x in K$. The equation $a^mu-x a=0$ is solvable in $K$ because
  $J^mu subset.eq K a$. Therefore we can account $a^mu=0$ up to multiplication
  of $chi$ by #source(11, printed: 483)an inner automorphism from $B'_F$. Hence
  $J^mu=(a K)^mu=a^mu K=0$ since $mu$ is a $K$-module endomorphism of the right
  $K$-module $J$. By @eq:l2001-automorphisms-almost-annihilator-conditions we
  obtain $(J^2)^sigma=J^(mu lambda)=0=(J^mu)^2=J^sigma J$ and
  $J^lambda J=J J^mu=0=(J^lambda)^2=J J^sigma$. Consequently,
  $sigma in Lambda'(K,J)$, $lambda in Lambda^((l)) lr((K,J))$, and
  $chi=zeta_n lr((sigma)) dot zeta^((l)) lr((lambda))$. The theorem is proved.
]

We now consider the order $abs(Aut R_n lr((K,J)))$ of the automorphism group for
any finite ring $K$ (which are within Theorem @th:l2001-automorphisms-main).
Taking into account Remark @rem:l2001-automorphisms-general-case we define $Q_n$
to be the order of the subgroup $B F D A(K,J)$ and $Q_2^+$ to be the order of
$B' F D A(K^+,J)$ for $n=2$.

#proposition[
  Let $K$ be a finite ring and $J$ be a quasi-regular ideal of $K$. Suppose
  $Ann_K J subset.eq J$ for $n=2$. Then
  $ Q_2^+=abs(B') dot abs(A(K^+,J)) dot abs(K^("#")) dot abs(J)^4 $
  and
  $
    Q_n=(abs(B')/(abs(K) dot abs(Ann_K J)^2)) dot abs(A(K,J))
    dot (abs(K^("#")) dot abs(Lambda(K, J)))^(n-1)
    dot (abs(K) dot abs(J))^binom(n, 2), quad n>2.
  $
  If $J=(a)$ for $a in C(K)$, then
  $
    abs(B')=abs(Lambda'(K,J)) dot abs(K) dot abs(Ann_J J) dot abs(Ann_K J)^(-1).
  $
] <prop:l2001-automorphisms-order>
#proof[
  By Theorem @th:l2001-automorphisms-structure we get
  $
    abs(D)/abs(D inter A(K,J))=abs(D_n lr((K)))/abs(K^("#"))=abs(K^("#"))^(n-1),
  $
  $
    abs(F)/abs(F inter D)=abs(R)/(abs(Ann R) dot abs(J)^n)
    =(abs(K) dot abs(J))^binom(n, 2)/abs(Ann_K J),
  $
  $ abs(B)=abs(Lambda(K, J))^(n-1) dot abs(B'), $
  $ abs(B inter F)=abs(B_F)=abs(K) dot abs(Ann_K J), $
  for each $n>=2$. Note that the order $abs(H M)$ of the product of two
  arbitrary subgroups $H,M$ in an arbitrary group is equal to the product
  $abs(H) dot abs(M) dot abs(H inter M)^(-1)$; see
  [@bib:l2001-automorphisms-Hungerford1974, Theorem I.4.7]. Therefore, we obtain
  the required decomposition of $Q_n$ by Theorem
  @th:l2001-automorphisms-structure(i). Suppose $n=2$ and $Ann_K J subset.eq J$.
  Then $zeta_1 lr((Lambda(K, J))) subset.eq D A(K^+,J)$ and
  $B F D A(K^+,J)=B' F D A(K^+,J)$ as in the proof of Theorem
  @th:l2001-automorphisms-main. We get $B' inter F=B' inter B_F$ and
  $abs(B' inter B_F)=abs(K)/abs(Ann_K J)$. The formula for $Q_2^+$ follows
  easily since by @th:l2001-automorphisms-structure(i) we obtain
  $ (B' F) inter D=F inter D, $
  $ (B' F D) inter A(K^+,J)=D inter A(K^+,J)=D inter A(K,J). $

  Suppose that $J=a K=K a$ for some element $a in K$. Each $K$-module
  endomorphism of the left $K$-module $J$ is uniquely defined by an image of the
  element $a$ and this image may be an arbitrary element in $Ann_J J$. Therefore
  $abs(Lambda^((l)) lr((K,J)))=abs(Ann_J J)$ for $a in C(K)$. Using Theorem
  @th:l2001-automorphisms-structure(iv) we obtain the required decomposition of
  $abs(B')$. This completes the proof.
]

#source(12, printed: 484)
Using Theorem @th:l2001-automorphisms-main we may describe automorphisms of
$K$-algebras $R_n lr((K,J))$. Let $A_(upright("mod"))$ be the automorphism group
of the algebra $R_n lr((K,J))$.

#proposition[
  Let $K$ be a commutative ring and let $J$ be an ideal of $K$ such that
  $Ann_K lr((J^t))=J$ for a positive integer $t$. Suppose
  @eq:l2001-automorphisms-unit-condition is satisfied for $n=2$. Then
  $A_(upright("mod"))=(A_(upright("mod")) inter B)F D$. If $K$ is a finite ring
  and $J$ is a principal ideal, then
  $abs(A_(upright("mod")))=abs(K^("#")) dot abs(K) dot abs(J) dot abs(Ann_K J)$
  for $n=2$ and
  $
    abs(A_(upright("mod")))=abs(K^("#"))^(n-1) dot abs(Ann_K J)^(n-2)
    dot (abs(K) dot abs(J))^binom(n, 2), quad n>2.
  $
] <prop:l2001-automorphisms-module>
#proof[
  Let $B_(upright("mod"))=A_(upright("mod")) inter B$ and let
  $phi in A_(upright("mod"))$. By Theorem @th:l2001-automorphisms-main there
  exists a $K$-ring or $(K^+,J)$-ring automorphism $theta$ of $R$ and an
  automorphism $chi in B F D$ such that $phi=chi theta$. Without loss of
  generality we may assume that $chi in B$ since
  $F D subset.eq A_(upright("mod"))$. Similarly $chi in B'$ for $n=2$ as in
  Theorem @th:l2001-automorphisms-main so $(x e_(21))^chi=x e_(21)$ for $n>=2$.
  We get
  $
    x^theta e_(21)=(x e_(21))^theta=(x e_(21))^phi
    =x(e_(21)^phi)=x(e_(21)^theta)=x e_(21).
  $
  Consequently, $theta$ is the identity map, $chi in B_(upright("mod"))$, and
  the decomposition of $A_(upright("mod"))$ is proved.

  Using Theorem @th:l2001-automorphisms-structure(iii) we obtain that
  $B_(upright("mod"))$ is equal to a direct product of subgroups
  $B_(upright("mod")) inter B'$,
  $B_(upright("mod")) inter zeta_i lr((Lambda(K, J)))$, $1<=i<n$. Clearly, an
  annihilator automorphism $zeta_i lr((lambda))$ (resp. an almost-annihilator
  automorphism @eq:l2001-automorphisms-almost-annihilator-map) of $R$ is a
  $K$-module if and only if $lambda$ (resp. $sigma$) is a module homomorphism of
  the $K$-module $K$ (resp. $J$). Therefore, we obtain
  $abs(B_(upright("mod")) inter zeta_i lr((Lambda(K, J))))=abs(Ann_K J)$
  $(1<=i<n)$. Assume $K$ to be a finite ring. For $J=a K$ for some $a in K$,
  $B'_(upright("mod"))$ is equal to a direct product of subgroups
  $B_(upright("mod")) inter B'_F$,
  $B_(upright("mod")) inter zeta_n lr((Lambda'(K,J)))$,
  $zeta^((l)) lr((Lambda^((l)) lr((K,J))))$ by Theorem
  @th:l2001-automorphisms-structure(iv). Since
  $Ann_K J subset.eq Ann_K lr((J^t))=J$ we get equalities:
  $
    abs(B_(upright("mod")) inter zeta_n lr((Lambda'(K,J))))
    =abs(Ann_K J)=abs(Ann_J J)=abs(Lambda^((l)) lr((K,J))).
  $
  Using Theorem @th:l2001-automorphisms-structure and Proposition
  @prop:l2001-automorphisms-order we obtain the required formula for
  $A_(upright("mod"))$. This completes the proof.
]

Note that the description of $A_(upright("mod"))$ was found by Dubisch and
Perlis [@bib:l2001-automorphisms-Dubish1951, Theorem 5-7] for arbitrary field
$K$ and $J=0$. See also [@bib:l2001-automorphisms-Levchuk1975,
Corollary~@cor:l1975-automorphisms-domain]. If $K=Z_(p^m)$, then
$A_(upright("mod"))=Aut R_n lr((K,J))$. Therefore, #corollary[
  Let $K=Z_(p^m)$ and $d$ be an arbitrary divisor of $m$ such that $1<=d<m$. If
  $J=(p^d)$, then $abs(Aut R_2 lr((K,J)))=(p^m-p^(m-1)) dot p^(2m)$ and
  $
    abs(Aut R_n lr((K,J)))=(p^m-p^(m-1))^(n-1)
    dot p^((2m-d) dot binom(n, 2)+d(n-2)), quad n>2.
  $
] <cor:l2001-automorphisms-prime-power-order>
#proof[
  It follows from the equality $abs(K)=abs(Ann_K J) dot abs(J)$ and Proposition
  @prop:l2001-automorphisms-module.
]

#source(13, printed: 485)
According to [@bib:l2001-automorphisms-Dubish1951] the automorphism group
$Aut R$ of an arbitrary associative ring $R$ has a normal subgroup $M$ of all
“monic” automorphisms of $R$ which induce the identity map into quotient-ring
$R^k/R^(k+1)$ for all positive integers $k$. Let $R=R_n lr((K,J))$, $n>2$.
Clearly $M supset.eq B F$. If $J=0$, then $M inter D=1$ (see
[@bib:l2001-automorphisms-Dubish1951], [@bib:l2001-automorphisms-Levchuk1975])
and even the group $Aut R$ is equal to the semidirect product of subgroups $M$
and $D A(K,J)$ [@bib:l2001-automorphisms-Levchuk1975]. However, the intersection
$M inter D$ is nontrivial for each nonzero quasi-regular ideal $J$ by Theorem
@th:l2001-automorphisms-structure(ii).
