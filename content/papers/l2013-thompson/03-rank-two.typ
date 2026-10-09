#import "../../main-defs.typ": *
#import "defs.typ": *

=== Large Abelian Subgroups of Groups $U$ of Type $G_2$ and $twisted(3, D_4)$
<sec:l2013-thompson-rank-two>

According to Section @sec:l2013-thompson-preliminaries, the root elements
$x_r lr((t))$ of the groups $U$ of type $G_2$ and $twisted(3, D_4)$ match the
roots of the system $G_2$. Choosing its simple roots $a$ and $b$ such that
$abs(a) < abs(b)$, we use a hypercentral automorphism $varsigma_d$ ($d in K$) of
a group $U$ (see [@bib:l2013-thompson-Levchuk1990]), for which
$varsigma_d lr((x_b lr((t)))) = x_b lr((t)) x_(3a+b) lr((2d t)) mod U_5$
($t in K$). We set
$
  alpha := x_a lr((1)) x_(2a+b) lr((1)), quad beta_c lr((t)) := x_(a+b) lr((t))
  x_(2a+b) lr((t c)).
$ <eq:l2013-thompson-alpha-beta>

We now prove the following theorem.

#theorem[Each large abelian subgroup of the group $U = U G_2(K)$ is
  $G_2(K)$-conjugate to one of the following subgroups:
  #enum(
    numbering: "a)",
    [a normal large abelian subgroup of $U$;],
    [an image under some automorphism $varsigma_d$ ($d in K$) of a subgroup,
      which is $(X_a n_a)$-conjugate to $U_3$ or $X_(a+b) U_4$ for $6K = K$;],
    [
      $
        lr({x_b lr((t)) x_(3a+b) lr((t)) | t in K}) beta_d lr((K)) U_5 quad (d
          in K) quad "for even" abs(K) > 2;
      $ <eq:l2013-thompson-exceptional-even>
    ],
    [$⟨ alpha,beta_1 lr((1)) ⟩ U_4$ for $abs(K) = 4$.],
  )
] <th:l2013-thompson-g2-large>

The proof of the theorem is based on a number of lemmas.

In [@bib:l2013-thompson-Levchuk2008, @bib:l2013-thompson-Levchuk2012Normal,
@bib:l2013-thompson-Levchuk2012Extremal], the normal large abelian subgroups of
$U$ are described as large normal abelian ones. The following lemma follows from
[@bib:l2013-thompson-Levchuk2012Extremal].

#lemma[If the group $U$ is of type $G_2$ then the set $Ac_N lr((U))$ consists of
  $
    U_3 "and" beta_c lr((K)) U_4 quad (c in K) quad "for even" abs(K) > 2, quad
    U_3 "for" 6K = K,
    U_2 "for" 3K = 0, quad ⟨ alpha ⟩ times ⟨ beta_1 lr((1)) ⟩ "for" abs(K) = 2.
  $
  #source(7, printed: 69) Up to diagonal automorphisms, normal large abelian
  subgroups of the group $U twisted(3, D_4)(K)$, are exhausted by the groups:
  $
    U_3 "and" beta_c lr((K_sigma)) dot x_(2a+b) lr((K^(1+sigma))) dot U_4 quad
    (c in K_sigma) quad "for even" abs(K_sigma) > 2,
    U_3 "for" 2K = K, quad ⟨ alpha ⟩ times ⟨ beta_1 lr((1)) ⟩ times x_(2a+b)
    lr((K^(1+sigma))) "for" abs(K_sigma) = 2.
  $
] <lem:l2013-thompson-normal-large>

#corollary[The order $a(U)$ of large abelian subgroups of the group $U = U G(K)$
  of type $G_2$ or $twisted(3, D_4)$ equals $abs(U_3)$, except the cases
  $abs(K) = 2$ or $3K = 0$ for the group $U G_2(K)$ where $a(U) = abs(K)^4$ and
  the group $U twisted(3, D_4)(8)$ where
  $a(U) = 2^6$.] <cor:l2013-thompson-orders>

Due to [@bib:l2013-thompson-Levchuk2009,
Theorem~@th:l2009-finitary-defining-relations], the group $U$ of type $G_2$
satisfies the following isomorphisms: $U slash U_3 approx U A_2(K)$ and
$U slash U_4 approx U B_2(K)$. The following lemma is well known for the group
$U A_2(K) approx UT(3, K)$.

#lemma[Let $A$ be a maximal abelian subgroup and $Z$ be the center of the group
  $U Phi(K)$. Then $A = lr({x_a lr((t)) x_b lr((c t)) | t in K}) Z$ ($c in K$)
  or $T(b)$ for the type $A_2$. For the type $B_2$ we have $A = T(b)$ or $A$ is
  $B$-conjugate either to $X_a Z$ or for the cases $2K = K$ and $2K = 0$ to the
  subgroup, respectively,
  $
    lr({x_a lr((t)) x_b lr((t)) x_(a+b) lr(((t^2-t) slash 2)) | t in K}) Z, quad
    ⟨ x_a lr((1)) x_b lr((1)) ⟩ Z.
  $ <eq:l2013-thompson-b2-maximal>
] <lem:l2013-thompson-a2-b2>

#proof[
  The center $Z$ of the group $U$ of type $B_2$ equals $U_3$ for $2K = K$ or
  $U_2$ for $2K = 0$. If there exists an element $gamma in A$ having two
  corners, then up to $B$-conjugation we may suppose that
  $gamma = x_a lr((1)) x_b lr((1))$. Choosing an arbitrary element
  $beta = x_a lr((t)) x_b lr((t')) x_(a+b) lr((t'')) mod U_3$ of $A$, we find
  $ 1 = [beta,gamma] = x_(a+b) lr((t'-t)) mod U_3, quad t' = t quad (t in K); $
  $
    [beta,gamma] = [x_a lr((t)),x_b lr((1))] [x_b lr((t)),x_a lr((1))] [x_(a+b)
      lr((t'')),x_a lr((1))] = x_(2a+b) lr((2t''+t-t^2)).
  $
  (The signs of the structural constants are chosen according to
  [@bib:l2013-thompson-Levchuk2009,
  Theorem~@th:l2009-finitary-defining-relations].) If $2K = 0$ then $t^2-t = 0$
  and $beta in ⟨ gamma ⟩ Z$. When $2K = K$ we have $t'' = (t^2-t) slash 2$ and
  hence $A$ is the first subgroup in @eq:l2013-thompson-b2-maximal.
]

Setting $pi := 1+sigma+sigma^2$ for the type $twisted(3, D_4)$ we require the
following lemma.

#lemma[If $2K = K$, then $Ker(1+sigma) = 0$. In the general case we have:
  $
    K = K^(1+sigma) + K_sigma, quad K_sigma inter K^(1+sigma) = 2K_sigma, quad
    K^pi = K_sigma, quad Ker(pi) = K^(1-sigma).
  $
] <lem:l2013-thompson-cubic-trace>

#proof[
  If $overline(v) = -v$, then $overline(overline(v)) = -overline(v) = v$,
  $v = overline(v) in K_sigma$ and $2v = 0$. If $2K = K$ then
  $Ker(1+sigma) = 0$. Since for any $K_sigma$-linear transformation of the field
  $K$ the sum of the rank and defect equals $3$, the remaining statements of the
  lemma easily follow from relations
  $
    K supset.eq K^(1+sigma) + K^pi supset.eq K^(sigma^2) = K, quad 0 = 1-sigma^3
    = (1-sigma) pi = pi(1-sigma).
  $
]

The order of a subgroup $A$ of a group $U = U G(K)$ of type $G_2$ or
$twisted(3, D_4)$ may be estimated using the orders of intersections of the
projections $A_i$:
$
  A inter U_i = x_r lr((A_i)) mod U_(i+1), quad 1 < ht(r) = i <= 5;
$ <eq:l2013-thompson-projections>
$
  abs(A) = abs(A colon A inter U_2) dot abs(A_2) dot abs(A_3) dot abs(A_4) dot
  abs(A_5).
$ <eq:l2013-thompson-order-product>

#lemma[Let $A$ be an abelian subgroup of $U$. Then there exist elements
  $d_a,d_b in K$ and an additive subgroup $F subset K$ such that
  $d_b F A_4 = 0$, and
  $
    A = gamma(F) dot (A inter U_2), quad gamma(t) = x_a lr((d_a t)) x_b lr(
      (d_b
        t)
    ) mod U_2 quad (t in F).
  $ <eq:l2013-thompson-simple-projections>

  For the type $twisted(3, D_4)$ and $G_2$ we have $(A_2 A_3)^pi = 0$ and
  $3A_2 A_3 = 0$, respectively. When $d_a F ∋ 1$ we have
  $A_2^(1+sigma) = A_3^pi = 0$ and $2A_2 = 3A_3 = 0$, respectively.
] <lem:l2013-thompson-projection-relations>

#proof[
  #source(8, printed: 70) Recall that $(A U_2) slash U_3$ is an abelian normal
  subgroup of the factor group $U slash U_3$, which is isomorphic to a subgroup
  of the unitriangular group $UT(3, K)$. By Lemma @lem:l2013-thompson-a2-b2 we
  obtain @eq:l2013-thompson-simple-projections, where $gamma(F)$ is the system
  of representatives of cosets of the subgroup $A inter U_2$ in $A$. The
  equalities $[A inter U_i,A inter U_j] = 1 mod U_(i+j+1)$ and
  @eq:l2013-thompson-projections imply $d_b F A_4 = 0$ and
  $
    (A_2 A_3)^pi = 0, quad (d_a F A_3)^pi = 0, quad (d_a F A_2)^(1+sigma) = 0
    "for the type" twisted(3, D_4),
    3A_2 A_3 = 0, quad 3d_a F A_3 = 0, quad 2d_a F A_2 = 0 "for the type" G_2.
  $
  When $d_a F ∋ 1$, we have $A_2^(1+sigma) = A_3^pi = 0$ and $2A_2 = 3A_3 = 0$
  respectively.
]

#lemma[If an abelian subgroup $A$ of $U$ has two corners, then
  $abs(A) < a(U)$.] <lem:l2013-thompson-two-simple-corners>

#proof[
  Using the notation of Lemma @lem:l2013-thompson-projection-relations and the
  representation @eq:l2013-thompson-simple-projections of the subgroup $A$, we
  have $F ∋ 1$ and $d_a = d_b = 1$ up to a diagonal automorphism. Furthermore,
  $abs(A colon A inter U_2) = abs(F)$ and $A_4 = 0$.

  By Lemma @lem:l2013-thompson-projection-relations, for the type $G_2$ we have
  $2A_2 = 3A_3 = 0$. Hence, $A_2 = 0$ when $3K = 0$ and if $6K = K$ then
  $A_3 = 0$ as well. In both cases, $abs(A) < a(U)$ due to
  @eq:l2013-thompson-order-product and Corollary @cor:l2013-thompson-orders.
  Since $(A U_4) slash U_4$ is an abelian subgroup of a factor group
  $U slash U_4 approx U B_2(K)$, using Lemma @lem:l2013-thompson-a2-b2 in the
  case $2K = 0$ we have:
  $
    abs(F) = 2, quad abs(A) <= abs(F) dot abs(A_2) dot abs(U_5) <= 2 dot
    abs(K)^2 < a(U).
  $

  For the type $twisted(3, D_4)$ we have $F subset.eq K_sigma$, and, by Lemma
  @lem:l2013-thompson-projection-relations,
  $A_2^(1+sigma) = A_3^pi = (A_2 A_3)^pi = 0$, and hence
  $A_2 subset.eq Ker(1+sigma)$. When $2K = K$, using Lemma
  @lem:l2013-thompson-cubic-trace we find:
  $
    A_2 = 0, quad abs(A_3) <= abs(Ker(pi)) = abs(K_sigma)^2, quad abs(A) <=
    abs(F) dot abs(A_3) dot abs(U_5) <= abs(K_sigma)^4 < a(U).
  $

  If $2K = 0$ then by Lemma @lem:l2013-thompson-cubic-trace we have
  $A_3 subset.eq K^(1+sigma)$ and $A_2 subset.eq K_sigma$. If
  $abs(A) >= abs(U_3)$ then
  $
    abs(A) = abs(F) dot abs(A_2) dot abs(A_3) dot abs(K_sigma) = abs(U_3), quad
    F = A_2 = K_sigma, quad A_3 = K^(1+sigma).
  $

  Thus, we may assume that a $2a+b$-projection of $gamma(F)$ is contained in
  $K_sigma$. Since $[gamma(F),A inter U_3] = 1$, $K_sigma$ also contains the
  $a+b$-projection of $gamma(F)$. Hence,
  $
    ⟨ gamma(F) ⟩ subset U twisted(3, D_4)(K) inter U D_4(K_sigma) approx U
    G_2(K_sigma)
  $
  and, by Lemma @lem:l2013-thompson-a2-b2 we have $abs(F) = 2 = abs(K_sigma)$.
  Then $abs(A) = abs(U_3) = 2^5 < 2^6 = a(U)$. The lemma is proved.
]

The following lemma easily follows from the commutator relations for $U$.

#lemma[If $Delta_1 := X_(a+b) X_(2a+b) U_5$ and $Delta_2 := X_b U_4$ then
  $T(b) = Delta_1 Delta_2$. If $U$ is of type $G_2$ and $3K = 0$ then the center
  $Z$ of $U$ is $X_(2a+b) U_5$, and the centralizer $C(Delta_1)$ is $T(b)$;
  otherwise, $Z = U_5$, $C(Delta_1) = Delta_2$ and $C(Delta_2) = Delta_1$.
  Furthermore, if $U$ is of type $G_2$ and $3K = K$ then
  $Delta_1 approx Delta_2 approx UT(3, K)$, else if $U$ is of type
  $twisted(3, D_4)$ then
  $Delta_2 approx UT(3, K_sigma)$.] <lem:l2013-thompson-centralizers>

#lemma[A large abelian subgroup $A$ of $U G_2(K)$ is one of the following:
  #enum(
    numbering: "a)",
    [$U_2$ or its $(X_a n_a union X_b n_b)$-conjugates when $3K = 0$;],
    [a subgroup $B$-conjugate to $(⟨ alpha ⟩ times ⟨ beta_1 lr((1)) ⟩) dot U_4$
      for $abs(K) = 2$ or $4$;],
    [a subgroup $B$-conjugate to $M_1 dot M_2$ for $3K = K$, $abs(K) > 2$, $M_i$
      being an arbitrary maximal abelian subgroup of $Delta_i$, $i = 1,2$.],
  )

  When $6K = K$, the subgroup $M_1 dot M_2$ coincides with $U_3$ or
  $X_(a+b) U_4$ up to an automorphism of the form $varsigma_d$ and to
  $(X_a n_a)$-conjugacy, and when $2K = 0$, it is $G(K)$-conjugate to $U_3$,
  $beta_d lr((K)) U_4$ or to
  $
    lr({x_b lr((t)) x_(3a+b) lr((t)) | t in K}) beta_d lr((K)) U_5 quad (d in
      K).
  $ <eq:l2013-thompson-even-product>
] <lem:l2013-thompson-g2-classification>

#proof[
  #source(9, printed: 71) Clearly, $A$ contains the center $Z$. If
  $A subset.eq.not U_2$, then there exists a corner $r = a$ or $b$ of $A$ and a
  representation @eq:l2013-thompson-simple-projections with $d_r = 1$ and
  $d_(overline(r)) = 0$; furthermore, $r+w_(overline(r)) lr((r)) in G^+$ and
  $w_r$ induces a substitution $tilde(w)_r$ on $G^+ without lr({r})$:
  $
    tilde(w)_a = (b quad 3a+b)(a+b quad 2a+b)(3a+2b), quad tilde(w)_b = (a quad
      a+b)(3a+b quad 3a+2b)(2a+b).
  $

  For the type $G_2$, when $i = ht(w_(overline(r)) lr((r)))$ and $3K = 0$ we
  have $A_i = 0$ by Lemma @lem:l2013-thompson-projection-relations. Hence,
  Corollary @cor:l2013-thompson-orders, Lemma @lem:l2013-thompson-a2-b2 and
  @eq:l2013-thompson-order-product give
  $
    T(r) supset.eq A supset.eq C(T(r)) = X_(w_r lr((overline(r)))) Z = X_(w_r
    lr((overline(r)))) X_(2a+b) U_5;
    A = gamma(K) X_(w_r lr((overline(r)))) Z, quad gamma(K) = lr(
      {x_r lr((t))
        x_(w_(overline(r)) lr((r))) lr((c t)) | t in K}
    ) mod C(T(r)).
  $

  Having cancelled the scalar $c in K$ with $X_(overline(r))$-conjugation, we
  map $A$ into $n_(overline(r))^(-1) U_2 n_(overline(r))$.

  Let $3K = K$. Then $(X_a U_3) slash U_5 approx UT(3, K)$, and if $2K = K$,
  then $T(a) slash U_4 approx UT(3, K)$. By Lemma
  @lem:l2013-thompson-projection-relations, either $r = a$, $A supset.eq U_4$
  and $A_3 = 0 = 2A_2$, or $r = b$ and $A_4 = A_2 A_3 = 0$. When two out of
  three projections $A_2$, $A_3$ and $A_4$ are zero, the remaining projection
  and $F$ are both equal to $K$, since $abs(A) >= abs(U_3)$. Hence
  $ A = gamma(K) U_4 "when" r = a, quad A = gamma(K) beta(K) U_5 "when" r = b, $
  $beta(t)$ being the coset representatives of $U_5$ in $A inter U_2$ where
  $beta(t) = x_q lr((t)) mod Q(q)$ for the angle $q$ of $A inter U_2$. When
  $r = b$ we define $lr({q,s}) := lr({a+b,2a+b})$. Due to Lemmas
  @lem:l2013-thompson-a2-b2 and @lem:l2013-thompson-centralizers, there exist
  maps $std.hide(t)'$, $std.hide(t)''$ and $c,d in K$, such that
  $
    gamma(t) = x_b lr((t)) x_s lr((t')) x_(3a+b) lr((c t)), quad beta(v) = x_q
    lr((v)) x_s lr((d v)) x_(3a+b) lr((v'')) in A quad (t,v in K),
    1 = [gamma(t),beta(v)] = [x_b lr((t)),x_(3a+b) lr((v''))] [x_s lr((t')),x_q
      lr((v))] = x_(3a+2b) lr((plus.minus 3v t' plus.minus v'' t)),
  $
  and hence $t' = 1' dot t$ and $v'' = (plus.minus 3 dot 1') v$ for a suitable
  choice of the signs. If $q = 2a+b$ then $d = 0$ and
  $X_(overline(r))$-conjugacy cancels the scalar $1'$; when $q = a+b$, the
  scalar $1'$ is similarly defined up to addition of squares from $K$. Up to
  $B$-conjugacy of $A$ we have $1' = 0$ and
  $A = (A inter Delta_1)(A inter Delta_2)$, $A inter Delta_i$ being arbitrary
  maximal abelian subgroups of $Delta_i$, $i = 1,2$.

  When $6K = K$, the exceptional automorphism from
  [@bib:l2013-thompson-Levchuk1990, Theorem 1] of the group $U$ cancels the
  scalar $c$ in $A inter Delta_2$, and the $U$-conjugacy implies either
  $n_a^(-1) A n_a = U_3$ or $X_(a+b) U_4$. With a glance of Lemma
  @lem:l2013-thompson-a2-b2, when $r = a$ we are able to cancel the $a+b$- and
  $2a+b$-projections in $gamma(F)$ by means of $U$-conjugacy; thus we transform
  $A$ to the form
  $
    X_a U_4 = n_b^(-1) (X_(a+b) U_4) n_b = (n_a n_b)^(-1) (X_b X_(2a+b) U_5) n_a
    n_b.
  $

  If $2K = 0$ then by means of diagonal $h(chi)$-conjugacy we achieve $c = 1$
  (when $chi(a) = u in K^sharp$, $chi(b) = u^(-1)$ and $chi(3a+b) = u^2$),
  obtaining $A$ in the form @eq:l2013-thompson-even-product.
  #ed-note[With the stated character values, diagonal conjugacy sends the
    coefficient $c$ to $u^3 c$. Cubing need not be surjective, for example over
    $GF(4)$ or $GF(16)$. Thus this step alone does not justify the claimed
    normalization for every field; this observation does not establish a
    counterexample to Theorem @th:l2013-thompson-g2-large.]
  Similarly, when $r = a$, we obtain a subgroup
  $
    lr({x_a lr((t)) x_(2a+b) lr((t)) | t in K}) U_4 = n_b^(-1) beta_1 lr((K))
    U_4 n_b = (n_a n_b)^(-1) X_b beta_1 lr((K)) U_5 n_a n_b.
  $

  Finally, we find the subgroups $A = gamma(F) beta_d lr((A_2)) U_4$, where
  $
    gamma(t) = x_a lr((t)) x_(2a+b) lr((c t)) quad (t in F), quad A_2 != 0, quad
    2K = 0, quad c,d in K.
  $
  The relations
  $
    1 = [gamma(t),beta_d lr((v))] = x_(3a+b) lr((t^2 v+t d v)) x_(3a+2b)
    lr(((v^2+c v)t))
  $
  show that for all $t in F$ and $v in A_2$ we have
  $
    (t+d)t A_2 = 0, quad (v+c)v F = 0, quad F = lr({0,d}), quad A_2 = lr({0,c}),
    quad abs(A) = 4abs(K)^2.
  $

  #source(10, printed: 72) By Corollary @cor:l2013-thompson-orders, we obtain
  $abs(K) = 2$ or $4$. Clearly, if $abs(K) = 2$ then $A ⊴ U$, and up to diagonal
  conjugacy $A$ has the form
  $
    (⟨ x_a lr((1)) x_(2a+b) lr((1)) ⟩ times ⟨ beta_1 lr((1)) ⟩) dot U_4.
  $ <eq:l2013-thompson-small-field>
]

For the type $twisted(3, D_4)$ the description is similar. If $A subset.eq T(a)$
and hence $T(a) supset.eq A supset.eq C(T(a)) = U_4$, then $A$ has the form
$
  beta(A_2) x_(2a+b) lr((A_3)) U_4, quad beta(v) := x_(a+b) lr((v)) x_(2a+b)
  lr((tilde(v))) quad (v in A_2)
$ <eq:l2013-thompson-d4-form>
for some map $tilde(std.hide(v)): A_2 arrow.r K$. Due to Lemmas
@lem:l2013-thompson-cubic-trace and @lem:l2013-thompson-projection-relations the
commutativity of $A$ is equivalent to the inclusion
$A_2 A_3 subset.eq Ker(pi) = K^(1-sigma)$. Due to the maximality of $A$, the
projections of $A_2$ and $A_3$ are both $K_sigma$-modules, as well as $Ker(pi)$.
If one of the projections are zero or equals $K$ then we have either $A = U_3$
or $A = beta(K) U_4$ for $tilde(std.hide(v))$ from $End(K^+)$; besides,
$
  [beta(t),beta(v)] = x_(3a+2b) lr((plus.minus (t tilde(v) - tilde(t) v)^pi)),
  quad (t tilde(v) - tilde(t) v)^pi = 0 quad (t,v in K).
$

Thus, $x_a lr((d))$-conjugation transforms the subgroup $X_(a+b) U_4$ into
$beta(K) U_4$, where
$
  tilde(t) = overline(overline(d)) overline(t) + overline(d)
  overline(overline(t)), quad
  (t tilde(v) - tilde(t) v)^pi = [d (overline(t) overline(overline(v)) -
      overline(v) overline(overline(t)) + overline(v) overline(overline(t)) -
      overline(t) overline(overline(v)))]^pi = (d dot 0)^pi = 0 quad (t,v in K).
$

When both $K_sigma$-modules $A_2$ and $A_3$ are nonzero, their dimension is $1$
or $2$. Up to $n_a$- and diagonal conjugacy, the dimension of $A_2$ is less or
equals the dimension of $A_3$, and $1 in A_2$. Therefore we may choose
$s in A_2$ such that
$ A_3 subset.eq (K_sigma + K_sigma s) A_3 = A_3 + s A_3 subset.eq K^(1-sigma). $

If the dimension of $A_3$ is $2$ then the inclusions turn into equalities, and
multiplication by $s$ induces a $K_sigma$-linear transformation of a
$2$-dimensional module $K^(1-sigma)$ with a characteristic root $s$. Since the
field $K$ does not contain a quadratic extension of the subfield $K_sigma$,
$A_2$ is a $1$-dimensional $K_sigma$-module. Hence $A_2 = K_sigma$ and
$A_3 = K^(1-sigma)$. It follows that $abs(A) = abs(U_3)$ or $abs(K) = 8$ and $A$
is $B$-conjugated to a normal subgroup of $U$. Moreover we now find the Thompson
subgroups.

#lemma[For the group $U G_2(K)$, $abs(K) > 2$, and $U twisted(3, D_4)(K)$,
  $abs(K_sigma) > 2$, we have $J(U) = J_e lr((U)) = U$. Besides,
  $J_e lr((U)) = 1$ and $J(U) = T(a)$ in $U twisted(3, D_4)(8)$ and
  $
    J_e lr((U)) = 1, quad J(U) = ⟨ alpha ⟩ times ⟨ alpha^(n_b) ⟩, quad alpha =
    x_a lr((1)) x_(2a+b) lr((1)) "in" U G_2(2).
  $
] <lem:l2013-thompson-rank-two-thompson>

Remark @rem:l2013-thompson-e6-thompson from Section @sec:l2013-thompson-e6,
[@bib:l2013-thompson-Suleimanova2011E8] and Lemma
@lem:l2013-thompson-rank-two-thompson give Theorem @th:l2013-thompson-thompson.
