#import "../../main-defs.typ": *
#import "defs.typ": *

=== Extremal subgroups <sec:l2012-extremal-en-extremal-subgroups>

#source(5, printed: 102) Let $U = U G(K)$. According to
[@bib:l2012-extremal-en-Parker1997] and [@bib:l2012-extremal-en-Parker1998], a
normal abelian subgroup $A$ in $U$ is said to be _extremal_ if
$A subset.not U_2$. Therefore, there exists a simple corner $p$ in $A$, i.e.,
$A subset.not 〈 X_r | r in G^+, r != p 〉$ (see also
[@bib:l2012-extremal-en-Carter1972, § 8.1]). For the purpose of application to
the revision of the classification of finite simple groups and etc., C. Parker
and P. Rowley
[@bib:l2012-extremal-en-Parker1997–@bib:l2012-extremal-en-Parker2003] studied
the groups $U$, having extremal subgroups, and simple corners of such subgroups.

Now, we correct some flaws in [@bib:l2012-extremal-en-Parker1997] and
[@bib:l2012-extremal-en-Parker1998]. For $U D_4 lr((K))$ over a field $K$ of
characteristic 2, the example in [@bib:l2012-extremal-en-Parker1997, pp.
396–397] gives some extremal subgroups with three simple corners (see also
[@bib:l2012-extremal-en-Parker1997, Theorem 1.3]). By
[@bib:l2012-extremal-en-Parker1998, Theorem 1.2], if $U twisted(2, D_4)(K)$ has
an extremal subgroup with two simple corners then $2K = 0$. But we now show that
if $U twisted(2, D_4)(K)$ and $U D_4 lr((K))$ were chosen as above, then, in
fact, $|K| = 4$ and $|K| = 2$, respectively.

Let $Phi$ be a root system of type $D_4$, and let $overline(" ")$ be a symmetry
of order 3 of the Coxeter graph of $Phi$. We consider simple roots $r$,
$overline(r)$, $overline(overline(r))$, and $q = overline(q)$. Clearly,
$U D_4 lr((K))$ and $U twisted(2, D_4)(K)$ contain the element

$
  theta.alt := x_r lr((1)) x_(overline(r)) lr((1))
  x_(overline(overline(r))) lr((1)) x_(s-r) lr((1))
  x_(s-overline(r)) lr((1)) x_(s-overline(overline(r))) lr((1))
  quad (s := q+r+overline(r)+overline(overline(r))).
$ <eq:l2012-extremal-en-d4-extremal-element>

#theorem[The groups $U D_4 lr((K))$ for $|K| > 2$ and $U twisted(2, D_4)(K)$ for
  $|K| > 4$ have no extremal subgroups with $>= 3$ or $>= 2$ simple corners,
  respectively. The normal closure of @eq:l2012-extremal-en-d4-extremal-element
  in $U D_4 lr((2))$, and $U twisted(2, D_4)(4)$ is an extremal subgroup with
  three and two simple corners,
  respectively.] <th:l2012-extremal-en-parker-rowley>

#proof(qed: true)[Note that if $U$ is of type $D_4$ and $twisted(2, D_4)$ then
  every its extremal subgroup contains $U_4$, by Lemma
  @lem:l2012-extremal-en-hypercenters-incident, and also $U_3 = C(U_3)$.

  Let $U = U D_4 lr((K))$. Suppose that $r,q,s$ are chosen as above. Assume that
  there exists an extremal subgroup $M$ in $U$ with $>= 3$ simple corners. Then
  we have

  $
    U_4 subset M subset C(U_4) = T(r) T(overline(r))
    T(overline(overline(r))), quad
    cal(L)(M) = {r,overline(r),overline(overline(r))},
  $
  $
    U/T(r) tilde.eq U/T(overline(r)) tilde.eq
    U/T(overline(overline(r))) tilde.eq UT(4, K).
  $

  By [@bib:l2012-extremal-en-Levchuk1976, Theorem @th:l1976-maximal-abelian],
  all corners in $M$ are q-connected and $2K = 0$. Setting

  $
    xi(t) := x_r lr((t)) x_(overline(r)) lr((t))
    x_(overline(overline(r))) lr((t)),
    quad eta(t) := x_(q+r) lr((t)) x_(q+overline(r)) lr((t))
    x_(q+overline(overline(r))) lr((t)),
    quad kappa_p lr((t)) := x_(s-p) lr((t)) x_(s-overline(p)) lr((t)),
  $

  up to conjugation of $M$ by a diagonal automorphism we easily obtain

  $
    M = xi(F) mod U_2, quad
    M inter U_2 = [M,X_q] = eta(K) mod U_3,
  $
  $
    M inter U_3 = [eta(K),U] = U_4 dot
    product_(p in Pi without {q}) kappa_p lr((K)),
  $

  where $F$ is an additive subgroup $F$ of $K$ and $F supset.eq GF(2)$.
  Therefore, for some map $tilde(" "): F arrow.r K$ and
  $v_r,v_(overline(r)),v_(overline(overline(r))) in K$, every $gamma in M$ may
  be written modulo $M inter U_3$ in the form

  $
    gamma = xi(f) (x_(q+r) lr((v_r))
      x_(q+overline(r)) lr((v_(overline(r))))
      x_(q+overline(overline(r))) lr((v_(overline(overline(r))))))
    x_(s-r) lr((tilde(f))) quad (f in F).
  $

  Since $s+q$ is equal to the highest root $rho$ and
  $[xi(F),kappa_p lr((K))] = 1$, we obtain

  $
    [gamma,kappa_p lr((K))] = [x_(q+r) lr((v_r))
      x_(q+overline(r)) lr((v_(overline(r))))
      x_(q+overline(overline(r))) lr((v_(overline(overline(r))))),
      kappa_p lr((K))] = x_rho lr(((v_p+v_(overline(p)))K)) = 1
  $

  #source(6, printed: 103) and therefore
  $v_r = v_(overline(r)) = v_(overline(overline(r)))$. Consequently,

  $ gamma = xi(f) x_(s-r) lr((tilde(f))) mod M inter U_2. $

  Also we note that every $omega in M inter U_2$ may be written modulo
  $M inter U_3$ as $omega = eta(t) x_(s-r) lr((t'))$ for some $t,t' in K$.

  Now, taking into account that $U_3$ is abelian, we obtain

  $
    1 = [gamma,omega] = [gamma,x_(s-r) lr((t'))]
    [xi(f),eta(t)] [x_(s-r) lr((tilde(f))),eta(t)]
    = x_s lr((t'f)) x_rho lr((tilde(f)t)) [xi(f),eta(t)]
    = x_s lr((t'f+f^2 t)) x_rho lr((tilde(f)t+f t^2)).
  $

  When $f = 1$, the equality $t'f+f^2 t = 0$ implies $t' = t$ for every
  $t in K$.

  Analogously, for all $f in F$ and $t in K$, we obtain $f = tilde(f)$,
  $t^2+t = 0$, and hence $|K| = 2 = |F|$. Consequently, $M$ coincides with the
  normal closure

  $
    {(U_4 times 〈 [theta.alt,x_(q+r) lr((1))],
        [theta.alt,x_(q+overline(r)) lr((1))] 〉)
      ⋉ 〈 [theta.alt,x_q lr((1))] 〉} ⋉ 〈 theta.alt 〉
  $ <eq:l2012-extremal-en-d4-normal-closure>

  of the element $theta.alt$ from @eq:l2012-extremal-en-d4-extremal-element in
  $U D_4 lr((2))$. Moreover, @eq:l2012-extremal-en-d4-normal-closure is the
  unique extremal subgroup in $U D_4 lr((2))$ with three simple corners.

  Let $M$ be an extremal subgroup in $U = U twisted(2, D_4)(K)$ possessing at
  least two simple corners. Take the twisted automorphism
  $theta in Aut D_4 lr((K))$ of order 2 such that
  $theta(x_r lr((1))) = x_(overline(r)) lr((1))$,
  $theta(X_(overline(overline(r)))) = X_(overline(overline(r)))$. Then the
  system $zeta(Phi)$ is of type $B_3$ and $cal(L)(M) = {a,b}$, where
  $a = zeta(r)$, $b = zeta(overline(overline(r)))$.

  Up to conjugation by a diagonal automorphism, we obtain $theta.alt in U_2 M$.
  Using the argument of previous case, we get

  $
    x_(a+zeta(q)+b) lr((K_sigma)) U_4
    = [[theta.alt,X_(zeta(q))],X_b] subset M, quad |K_sigma| = 2,
  $

  and, finally, $M$ coincides with the subgroup
  @eq:l2012-extremal-en-d4-normal-closure in
  $U D_4 lr((2)) inter U twisted(2, D_4)(4)$. This completes the proof of
  Theorem @th:l2012-extremal-en-parker-rowley.
]

A description of maximal abelian normal subgroups of $U$ in Sections
@sec:l2012-extremal-en-rank-two–@sec:l2012-extremal-en-f4-e6 and
[@bib:l2012-extremal-en-Levchuk2008, Theorem @th:l2008-normal-classical-maximal]
(for the classical types) gives also a description of extremal subgroups and
hence a new solution to the Parker–Rowley problem.

=== The case of Lie rank $<= 2$ <sec:l2012-extremal-en-rank-two>

Let $U$ be the group $U G(K)$ of exceptional type over a field $K$. In this
section we prove the following theorem.

#theorem[If $U$ is of rank $<= 2$ then all maximal abelian normal subgroups in
  $U$ are exhausted by the following subgroups:

  #enum(
    numbering: "(a)",
    [$〈 gamma 〉 U_2$ ($gamma in U without U_2$) for $G = twisted(2, B_2)$;],
    [$U_2$ for $G = twisted(2, G_2)$ (or $G = G_2$ and $3K = 0$);],
    [$U_3$ for $G = G_2$ if $6K = K$, and, additionally,
      $beta_c lr((K)) dot U_4$ ($c in K$) for $2K = 0$, and also
      $〈 alpha 〉 times 〈 beta_1 lr((1)) 〉$ for $|K| = 2$, where

      $
        alpha = x_a lr((1)) x_(2a+b) lr((1)), quad
        beta_c lr((t)) = x_(a+b) lr((t)) x_(2a+b) lr((t c));
      $
    ],
    [#source(7, printed: 104) $U_3$ for $G = twisted(3, D_4)$, and, when
      $2K = 0$, additionally, up to conjugation by a diagonal automorphism,
      $beta_c lr((K_sigma)) x_(2a+b) lr((K^(1+sigma))) dot U_4$ ($c in K$), and
      also

      $
        〈 alpha 〉 times 〈 beta_1 lr((1)) 〉 times x_(2a+b) lr((K^(1+sigma)))
      $

      if $|K_sigma| = 2$.
    ],
  )] <th:l2012-extremal-en-rank-two-maximal>

#proof(qed: true)[Consider an arbitrary maximal abelian normal subgroup $M$ of
  $U$. Note that the Coxeter number $h$ is even and $U_(h/2)$ is an abelian
  normal subgroup for every root system $Phi$ of type $!= A_n$.

  The Coxeter number of a root system of type $G_2$ is equal to 6. Therefore,
  the normal subgroup $U_3$ (i.e., $T(2a+b)$) is abelian in the group $U$ of
  type $G_2$ or $twisted(3, D_4)$. For $M subset.not U_3$, the intersection
  $M inter U_2$ has the corner $a+b$ and

  $ U_4 = [X_a,M inter U_2] U_5 subset.eq M subset.eq C(U_4) = T(a). $

  Thus, up to conjugation of $M$ by a diagonal automorphism, there exist some
  additive subgroups $F,Q,P$ of $K$ ($1 in Q$, $1 in F$ or $F = 0$) and a map
  $tilde(" "): Q arrow.r K$ such that

  $
    M = x_a lr((F)) mod U_2, quad M inter U_2 = beta(Q) x_(2a+b) lr((P)) U_4,
  $

  where $beta(v) := x_(a+b) lr((v)) x_(2a+b) lr((tilde(v))) in M$ ($v in Q$).

  Suppose that $U = U G_2 lr((K))$. If $6K = K$ then $U_3$ is a
  self-centralizing subgroup and each normal subgroup $H$ of the group
  $U G_2 lr((K))$ is incident with $U_3$ by Lemma
  @lem:l2012-extremal-en-hypercenters-incident. It follows that $M = U_3$. Since
  $[M inter U_2,M] = x_(2a+b) lr((2F K)) mod U_4$, we have $2F = 0$. In
  particular, $T(a+b)$ (i.e., $U_2$) is a unique maximal abelian normal subgroup
  for $3K = 0$.

  When $2K = 0$, the relations

  $
    [beta(Q),x_(2a+b) lr((P))] = x_(3a+b) lr((3Q P)) mod U_5, quad
    [beta(u),beta(v)] = x_(3a+2b) lr((3(u tilde(v)+v tilde(u))))
  $

  show that $P = 0$ and $tilde(v) = v d$ ($v in Q$) for a fixed
  $d = tilde(1) in K$. Consequently, the intersection $M inter U_2$ is contained
  into the abelian normal subgroup

  $
    cal(M)_(c,d) = {x_(a+b) lr((c t)) x_(2a+b) lr((t d)) | t in K} U_4
    quad ((c,d) != (0,0))
  $

  for $c = 1$. Assume that $M subset.not U_2$. Then $1 in F$ and
  $alpha = x_a lr((1)) x_(2a+b) lr((f)) in M$ for $f in K$. Since
  $[alpha,X_b] U_4 subset.eq M inter U_2$, we obtain

  $
    M inter U_2 = cal(M)_(1,1), quad 1 = [alpha,cal(M)_(1,1)]
    = x_(3a+2b) lr(({t^2+t f | t in K})).
  $

  Hence, $f = 1$ and $|K| = 2$. On the other hand,
  $〈 x_a lr((1)) x_(2a+b) lr((1)) 〉 cal(M)_(1,1)$ is an abelian normal
  subgroup of order $|K|^4 = 2^4$ for $|K| = 2$. If $|K| > 2$ then
  $M = U_3 = cal(M)_(0,1)$ or $M = cal(M)_(1,d)$ for an arbitrary $d in K$.

  For $U$ of type $twisted(3, D_4)$, the ideal
  $K^(1+sigma+sigma^2) = {t+overline(t)+overline(overline(t)) | t in K}$
  of the subfield $K_sigma$ is non-zero (see also
  [@bib:l2012-extremal-en-Parker1998, Lemma 2.3]), and hence
  $K_sigma = K^(1+sigma+sigma^2)$. Since $K_sigma inter K^(1+sigma) = 2K_sigma$,
  we get

  $
    K supset.eq K^(1+sigma)+K^(1+sigma+sigma^2)
    supset.eq K^(sigma^2) = K, quad K = K^(1+sigma)+K_sigma;
  $
  $
    1 = [[X_a,beta(1)],beta(1)] = [x_(2a+b) lr((K^(1+sigma))),beta(1)]
    = x_(3a+2b) lr(((K^(1+sigma))^(1+sigma+sigma^2))).
  $

  Hence, $0 = 2K^(1+sigma+sigma^2) = 2K_sigma = 2K$, whence the sum
  $K^(1+sigma)+K_sigma$ is direct and $P = K^(1+sigma)+(P inter K_sigma)$.
  Taking into account the relations

  $
    1 = [x_(2a+b) lr((P inter K_sigma)),beta(1)]
    = x_(3a+2b) lr(((P inter K_sigma)^(1+sigma+sigma^2))),
  $

  #source(8, printed: 105) we deduce $0 = 3(P inter K_sigma) = P inter K_sigma$
  and hence $P = K^(1+sigma) = P^sigma$. Also, $M inter U_3$ centralizes
  $M inter U_2$ and $x_(a+b) lr((K_sigma)) U_3$. Therefore,

  $
    1 = [beta(Q inter K^(1+sigma)),x_(2a+b) lr((P))]
    = x_(3a+2b) lr(((P (Q inter K^(1+sigma)))^(1+sigma+sigma^2))),
  $
  $
    ((overline(v)+overline(overline(v)))
      (Q inter K^(1+sigma)))^(1+sigma+sigma^2)
    = 0, quad
    (v+overline(v)+overline(overline(v)))
    (Q inter K^(1+sigma))^(1+sigma+sigma^2)
    = 0 quad (v in K).
  $

  Summarizing the last two equalities, we get
  $(v(Q inter K^(1+sigma)))^(1+sigma+sigma^2) = 0$ for all $v in K$.
  Consequently, $Q inter K^(1+sigma) = 0$ (otherwise $K^(1+sigma+sigma^2) = 0$)
  and $Q subset.eq K_sigma$.

  Choose a system $beta(Q)$ of coset representatives of $M inter U_3$ in
  $M inter U_2$ such that $tilde(Q) subset.eq K_sigma$. Using the isomorphism
  $U twisted(3, D_4)(K) inter U D_4 lr((K_sigma)) tilde.eq U G_2 lr((K_sigma))$
  we obtain $tilde(v) = d v$ for $d = tilde(1)$. Therefore, $M inter U_2$
  coincides with

  $
    cal(M)_d = {x_(a+b) lr((v)) x_(2a+b) lr((d v)) | v in K_sigma}
    x_(2a+b) lr((K^(1+sigma))) U_4.
  $

  For $F != 0$, $alpha = x_a lr((1)) x_(2a+b) lr((f)) in M$ may be chosen with
  $f in K_sigma$. The subgroup $〈 alpha 〉 beta(Q) U_4$ is normal in
  $U twisted(3, D_4)(K) inter U D_4 lr((K_sigma))$. As above,
  $〈 alpha 〉 beta(Q) U_4$ is abelian if and only if $f = 1$ and
  $|K_sigma| = 2$. Note that $〈 x_a lr((1)) x_(2a+b) lr((1)) 〉 cal(M)_1$ is an
  abelian normal subgroup in $U twisted(3, D_4)(K)$ for $|K| = 8$. If
  $|K_sigma| > 2$ then either $M = U_3$ or $M$ coincides with $cal(M)_d$ for an
  arbitrary $d in K$.

  If $K$ possesses an automorphism $sigma$ such that $3sigma^2 = 1$ then
  $U twisted(2, G_2)(K)$ is represented by the elements $(t,u,v)$ and

  $
    (t,u,v)(t',u',v') = (t+t',u+u'-t(t')^(3sigma),
      v+v'-u t'+t(t')^(3sigma+1)-t^2(t')^(3sigma))
  $

  (see [@bib:l2012-extremal-en-Carter1972, 13.6.4 (vii)] and
  [@bib:l2012-extremal-en-Steinberg1967]). The subgroups $(0,0,F)$, $(0,F,K)$,
  and $(F,K,K)$ in $U twisted(2, G_2)(K)$ exhaust all normal subgroups by Lemma
  @lem:l2012-extremal-en-hypercenters-incident, where $F$ is an additive
  subgroup of $K$. Obviously, $U_2$ is abelian and $(F,K,K)$ with $F != 0$ are
  not abelian.

  In [@bib:l2012-extremal-en-Carter1972, 13.6.4 (vi)], $U twisted(2, B_2)(K)$ is
  represented as

  $
    U twisted(2, B_2)(K) = {(t,u) | t,u in K}, quad
    (t,u)(t',u') = (t+t',u+u'+(overline(t))^2 t'),
  $ <eq:l2012-extremal-en-suzuki-multiplication>

  where $K$ possesses a non-trivial automorphism $overline(" ")$ such that
  $overline(overline(x))^2 = x$ ($x in K$). The center $Z_1$ of
  $U twisted(2, B_2)(K)$ is equal to $(0,K)$ and, by Lemma
  @lem:l2012-extremal-en-hypercenters-incident, every normal subgroup is of the
  form either $(0,F)$ or $(F,K)$ for an arbitrary additive subgroup $F$ of $K$.
  For the commuting elements $(t,u)$ and $(t',u')$, we have
  $(overline(t))^2 t' = (overline(t'))^2 t$. When $t' != 0$, up to conjugation
  by a diagonal element, we may assume that $t' = 1$. In this case
  $t = (overline(t))^2 = (overline(overline(t)))^4 = t^2$, whence either $t = 0$
  or $t = 1$. Therefore, the maximal abelian normal subgroups of
  $U twisted(2, B_2)(K)$ are exhausted by the centralizers of the elements of
  order 4; they have the form $(F,K)$ with $|F| = 2$. Thus, Theorem
  @th:l2012-extremal-en-rank-two-maximal is proved.
]

=== The normal structure <sec:l2012-extremal-en-normal-structure>

In this section, we consider the normal structure of $U G(K)$ and describe the
maximal abelian normal subgroups of groups $U E_n lr((K))$, $n = 6,7,8$.

Let $U = U G(K)$ and $H subset.eq U$. Since
$H subset.eq product_(s in cal(L)(H)) T(s)$, there exists a subset $cal(F)(H)$
in $product_(s in cal(L)(H)) X_s$ such that
$cal(F)(H) = H mod product_(s in cal(L)(H)) Q(s)$. As in
[@bib:l2012-extremal-en-Levchuk2008], $cal(F)(H)$ is said to be a _frame_ of
$H$. The following theorem holds.

#theorem[Let $H$ be a subgroup in the group $U$ of classical type or of type
  $E_n$ over a field $K$. Assume that $2K = K$ or $U$ is of type $A_n$ or
  $twisted(2, A_n)$. Then $H lt.closed.eq U$ if and only if
  $cal(F)([H,X_p]) subset.eq H$ for each $p in Pi(G)$.]
<th:l2012-extremal-en-frame-normal>

#source(9, printed: 106) Let us consider the idea of the proof.

Using the representation $pi$ from Section @sec:l2012-extremal-en-preliminaries
of $U$ we define a frame of a subset $pi(H)$ in $(N G(K),compose)$ by the rule
$cal(F)(pi(H)) := pi(cal(F)(H))$. The concept of frame and the representation
$pi$ allow us to apply linear methods, cf. [@bib:l2012-extremal-en-Levchuk1992,
@bib:l2012-extremal-en-Levchuk1990, @bib:l2012-extremal-en-Levchuk2008,
@bib:l2012-extremal-en-Levchuk2009]. The multiplication $compose$ and the
addition on the frame $cal(F)(pi(H))$ coincide modulo
$sum_(r in cal(L)(H)) pi(Q(r))$. Also, we may consider an arbitrary frame in the
module $N G(K)$ as a submodule. When $G = Phi$, we get

#lemma[Let $H subset.eq U Phi(K)$, $pi(H)$ be a subgroup in the adjoint or
  additive group of $N Phi(K)$, and let $p in Phi^+$. Then $pi(cal(F)([H,X_p]))$
  is a $K$-submodule in $N Phi(K)$ coinciding with the frame of
  $pi(H) ast K e_p$.] <lem:l2012-extremal-en-commutator-frame>

#lemma[Let $U = U G(K)$, $H subset.eq U$ and $p in G^+$. Then
  $|cal(L)([H,X_p])| <= 3$.] <lem:l2012-extremal-en-commutator-corner-bound>

#proof(qed: true)[The standard commutator relations show that every corner in
  $[H,X_p]$ can be written in the form $s+p$ for
  $s in union_(r in cal(L)(H)) {r}^+$. Evidently, $|cal(L)(H)| <= rank G$. By
  the well known classification of root systems, for $G = Phi$, the minimal root
  subsystem of $Phi$ containing $cal(L)([H,X_p]) union {p}$ has a connected
  Coxeter graph of rank $<= 4$. Therefore, $|cal(L)([H,X_p])| <= 3$. Using the
  root system $zeta(Phi)$ we get this inequality for $G = twisted(m, Phi)$,
  $p(Phi) = 1$.
]

Now let $U = U G(K)$, $G = twisted(2, Phi)$, $p(Phi) = 1$, $r,s,r+s in G^+$, and
let

$
  x_r lr((F)) subset.eq X_r, quad x_s lr((V)) subset.eq X_s
  quad "for some" F,V subset.eq K, F V != 0.
$

#lemma[
  #enum(
    numbering: "(i)",
    [If $[x_r lr((F)),x_s lr((V))] subset.eq Q(r+s)$ then $r+s$ is of the first
      type, $r$ and $s$ are not of the first type, and, up to conjugation by a
      diagonal automorphism, either $F subset.eq K_sigma$,
      $V subset.eq K^(1-sigma)$ or $G = twisted(2, A_(2n))$,
      $F,V subset.eq K_sigma$.],
    [If $[x_r lr((F)),X_s]$ does not coincide with $0$, $X_(r+s)$ modulo
      $Q(r+s)$ then $s$ is of the first type, $r,r+s$ are not of the first type,
      and $F K_sigma$ is a 1-dimensional $K_sigma$-module.],
  )] <lem:l2012-extremal-en-twisted-projections>

#proof(qed: true)[Firstly, assume that either $r$ (or $s$) is of the first type
  or $r+s$ is not of the first type. Then the basic relations of the twisted
  group $U$ (cf. [@bib:l2012-extremal-en-Carter1972,
  @bib:l2012-extremal-en-Steinberg1967] and [@bib:l2012-extremal-en-Levchuk2009,
  Theorem 2]) show that
  $[x_r lr((u)),x_s lr((v))] = x_(r+s) lr((plus.minus eta)) mod Q(r+s)$ for
  $eta = u v$, $overline(u)v$, $u overline(v)$ or $overline(u)overline(v)$, and
  hence $r+s$ is a corner of the commutator $[x_r lr((F)),x_s lr((V))]$.

  Thus, the assumption $[x_r lr((F)),x_s lr((V))] subset.eq Q(r+s)$ shows that
  $r+s$ is of the first type, $r$ and $s$ are not of the first type, and
  $eta = 0$ for all $u in F$, $v in V$, where either
  $eta = u v+overline(u)overline(v)$ ($u overline(v)+overline(u)v$) or
  $eta = u overline(v)-overline(u)v$ when $G = twisted(2, A_(2n))$. Up to
  conjugation by a diagonal automorphism, we may assume that $1 in F$. It
  immediately follows that either $V subset.eq Ker(1+sigma) = K^(1-sigma)$,
  $F subset.eq K_sigma$ or $G = twisted(2, A_(2n))$, $V,F subset.eq K_sigma$.

  When $[x_r lr((F)),X_s] Q(r+s)$ does not coincide with $Q(r+s)$ and $T(r+s)$,
  we easily infer that $s$ is of the first type, $r+s$ and $r$ are not of the
  first type, and $F K_sigma$ is a 1-dimensional $K_sigma$-module.
]

Using Lemma @lem:l2012-extremal-en-root-commutator, Lemma
@lem:l2012-extremal-en-twisted-projections, and (ii) we obtain the following
lemma.

#lemma[Let $H lt.closed.eq U G(K)$ and $cal(L)(H) = {r}$. Then either
  $H = Q(r) cal(F)(H)$ or (a) $G = twisted(2, Phi)$, $p(Phi) = 1$, $r$ is not of
  the first type, r-projection of $H$ generates a 1-dimensional $K_sigma$-module
  and there exists $s in Pi(G)$ of the first type with $r+s in G^+$, or (b)
  $G = Phi$, $p(Phi)! K = 0$ or $G = twisted(3, D_4)$,
  $2K = 0$.] <lem:l2012-extremal-en-one-corner-normal>

It is well known that for $G = twisted(2, A_(2n))$ every $s in Pi(G)$ is not of
the first type. Using Lemmas @lem:l2012-extremal-en-twisted-projections and
@lem:l2012-extremal-en-one-corner-normal repeatedly we get the following theorem
from [@bib:l2012-extremal-en-Levchuk2008, Theorem @th:l2008-normal-classical].

#theorem[Let $U G(K)$ be of type $B_n$, $C_n$ for $2K = K$ or of type $A_n$,
  $twisted(2, A_n)$. A subgroup $H$ is normal if and only if for each corner $r$
  of $H$ and $p in Pi(G)$ with $r+p in G$ either

  #enum(numbering: "(A)", [#source(10, printed: 107)
    $cal(F)([H,X_p]) Q(r+p) subset.eq H$])

  or $G = B_n$ and

  #enum(numbering: "(A)", start: 2, [for some $q in Pi(G)$ two corners in
    $[H,X_p]$ are q-connected, two corners in $[H,X_q]$ are connected, and
    $cal(F)([H,X_p]) cal(F)([H,X_q]) Q(r+p,r+p+q) subset H$.])]
<th:l2012-extremal-en-classical-normal>

For the group $U$ of type $E_n$, the analogue of this theorem is not satisfied
[@bib:l2012-extremal-en-Suleimanova2008E]. By
[@bib:l2012-extremal-en-Levchuk2008, Theorems @th:l2008-normal-orthogonal and
@th:l2008-normal-classical-maximal], for $U$ of type $D_n$ and $twisted(2, D_n)$
there exists a normal subgroup $M$ such that the height of commutator
$[[dots [[M,U],U] dots],U]$ grows unboundedly together with the grows of $n$,
where the commutator is not generated by the root elements of $M$. To finish the
consideration of remaining groups $U$ in Theorem
@th:l2012-extremal-en-frame-normal we use the normal closures of subgroups which
are similar to the subgroups from Theorem @th:l2012-extremal-en-parker-rowley,
and we get

#lemma[If $H lt.closed.eq U G(K)$ for type $D_n$ (or $twisted(2, D_n)$) and
  $cal(F)([H,X_p]) subset.not H$ for some $p in Pi(G)$ then there exist simple
  corners $r,overline(r)$ (respectively, $zeta(r)$) and a p-connected corner in
  $H$ which have the projections of order 2.]
<lem:l2012-extremal-en-linked-binary-corners>

Our description of abelian normal subgroups uses a specific notation.

For every $Psi subset.eq G^+$, we set $X_Psi = 〈 X_r | r in Psi 〉$. A subset
$Psi$ in $G^+$ is called _normal_ if ${s}^+ subset.eq Psi$ for all $s in Psi$,
and hence $X_Psi lt.closed.eq U G(K)$. By [@bib:l2012-extremal-en-Malcev1945], a
subset $Psi$ in $Phi^+$ is called _abelian_ if $r+s in.not Phi$ for all
$r,s in Psi$. Then $X_Psi$ is the direct product of some root subgroups. For
$H subset.eq U G(K)$, put

$ Psi(H) = {r in G^+ | H inter X_r != 1}. $
<eq:l2012-extremal-en-root-intersections>

Denote by $hat(Psi)(H)$ the set of all corners of the elements in $H$, which are
not in $Psi(H)$, and also all sums in $G^+$ of such corners. Thus, for the
subgroup $H$ in $U Phi(K)$ of the shape @eq:l2012-extremal-en-paired-corners or
@eq:l2012-extremal-en-linked-three-corners from Lemma
@lem:l2012-extremal-en-an-maximal-abelian, $hat(Psi)(H)$ is ${r,r',rho}$ or
${r,r',r+p,r'+p,rho}$, respectively.

Further, we use the elements $alpha(t)$ and $beta(t)$ from
@eq:l2012-extremal-en-paired-corners and
@eq:l2012-extremal-en-linked-three-corners. By
[@bib:l2012-extremal-en-Levchuk2008], for $2K = 0$, $U D_n lr((K))$ has a unique
maximal abelian normal subgroup $M_0$ possessing some simple corners $r$ and
$r' = overline(r)$ with $alpha(1) in M_0$ and
$hat(Psi)(M_0) = {r}^+ union {r'}^+$. For $n = 4$ and some $p,q in Pi(Phi)$,
$M_0$ is of the shape

$
  alpha(K) beta(K) {x_(r+p+q) lr((t)) x_(r'+p+q) lr((t)) | t in K}
  (C(T(r)) inter C(T(r'))).
$ <eq:l2012-extremal-en-d4-paired-closure>

#theorem[Let $M$ be a maximal abelian normal subgroup of the group
  $U = U Phi(K)$, $Psi = Psi(M)$ and $p(Phi)! K = K$. Then $X_Psi subset.eq M$
  and for $M != X_Psi$, up to conjugation by diagonal automorphism, there are
  two cases:

  #enum(
    numbering: "(i)",
    [$M$ is of the form @eq:l2012-extremal-en-paired-corners and
      $X_(hat(Psi)) tilde.eq UT(3, K)$;],
    [$2K = 0$, $p(Phi) = 1$, $X_(hat(Psi)) inter M$ has p-connected corners for
      a simple root $p$.],
  )

  Moreover, in (ii) one of the following subcases holds:

  #enum(
    numbering: "(a)",
    [$M$ is of the form @eq:l2012-extremal-en-linked-three-corners and
      $X_p X_(hat(Psi)) tilde.eq UT(4, K)$,],
    [$U = U D_4 lr((2)) = X_(hat(Psi)) X_p$,],
    [$U$ is of type $D_n$, $E_m$, and
      $X_(hat(Psi)) times X_s tilde.eq [U D_4 lr((K)),U D_4 lr((K))]$ for some
      $s in Psi$,],
    [$M$ is of the form $M_0$ or @eq:l2012-extremal-en-d4-paired-closure,
      respectively, for types $D_n$, $E_m$.],
  )] <th:l2012-extremal-en-abelian-normal>

#proof(qed: true)[Using Lemmas @lem:l2012-extremal-en-corner-full-projection and
  @lem:l2012-extremal-en-one-corner-normal, we easily find that $Psi$ and
  $Psi union {r}^+$ are commutative normal sets in $Phi^+$ for $r in cal(L)(M)$.
  The subgroup $X_Psi$ centralizes $M$, and hence $X_Psi subset.eq M$.
  Obviously, $M = X_Psi$ if #source(11, printed: 108) and only if $Psi$ is a
  maximal commutative normal set in $Phi^+$. Let $hat(Psi) = hat(Psi)(M)$.
  Assuming $M != X_Psi$ we get

  $
    cal(L)(X_(hat(Psi))) = cal(L)(M inter X_(hat(Psi))), quad
    X_Psi = inter_(r in cal(L)(X_(hat(Psi)))) C(T(r)), quad
    M = (M inter X_(hat(Psi))) times X_(Psi without (Psi inter hat(Psi))).
  $

  Each root $r$ in $hat(Psi) without (Psi inter hat(Psi))$ does not commute with
  at least one root of $hat(Psi) without (Psi inter hat(Psi))$, since $X_r$
  centralizes no $M$. Therefore, each corner in $M inter X_(hat(Psi))$ is
  connected with another corner in $M inter X_(hat(Psi))$.

  If there exist corners $r$ and $r'$ in $M inter X_(hat(Psi))$ which are not
  commuting then $[M,X_r][M,X_(r')] subset M$, and the root systems from
  [@bib:l2012-extremal-en-Bourbaki1968] give

  $
    X_(hat(Psi)) tilde.eq UT(3, K), quad hat(Psi) = {r,r',r+r'}, quad
    X_Psi = C{T(r) T(r')}, quad r+r' = rho in Psi.
  $

  Then, by Lemma @lem:l2012-extremal-en-an-maximal-abelian, $M$ is conjugate by
  a diagonal automorphism to @eq:l2012-extremal-en-paired-corners.

  In the other cases, for a simple root $p$, there exist some p-connected
  corners $r$ and $r'$ in $M inter X_(hat(Psi))$ and
  ${r,r',r+p,r'+p,r+r'+p} subset.eq hat(Psi)$ holds. If this inclusion turns
  into an equality then $p(Phi) = 1$, $2K = 0$, $M$ is reduced to the form
  @eq:l2012-extremal-en-linked-three-corners, and

  $ r'+r+p = rho, quad X_p X_(hat(Psi)) tilde.eq UT(4, K). $

  In the other cases, for type $D_n$ and $|cal(L)(X_(hat(Psi)))| = 2$, we have
  $X_(hat(Psi)) = T(r) T(overline(r))$ by [@bib:l2012-extremal-en-Levchuk2008].
  Up to conjugation by a diagonal automorphism, the subgroup $M$ in $U$ is of
  the shape @eq:l2012-extremal-en-d4-paired-closure if $U$ is of type $E_m$.

  The case $|cal(L)(X_(hat(Psi)))| = 3$ is possible when $U$ is of type $E_m$
  and $D_n$. Then two of three corners $r_1,r_2,r_3$ in $M inter X_(hat(Psi))$
  are p-connected, two of them are q-connected, and
  $X_(hat(Psi)) times X_s tilde.eq [U D_4 lr((K)),U D_4 lr((K))]$ for some
  $s in Psi$ and some simple roots $p$, $q != p$. In this case, $M$ has the form

  $
    {x_(r_1) lr((t)) x_(r_2) lr((t)) x_(r_3) lr((t))
      x_(r_2+p) lr((c t)) | t in K}
    {x_(r_1+p) lr((t)) x_(r_2+p) lr((t)) | t in K}
    {x_(r_1+q) lr((t)) x_(r_3+q) lr((t)) | t in K} X_Psi.
  $ <eq:l2012-extremal-en-three-corner-subgroup>

  In the remaining cases, for $U$ of type $D_n$, $M$ has three simple corners
  and $U = U D_4 lr((2)) = X_(hat(Psi)) X_q$ (see Theorem
  @th:l2012-extremal-en-parker-rowley and [@bib:l2012-extremal-en-Levchuk2008,
  Theorem @th:l2008-normal-classical-maximal]).
]

We now list the commutative normal sets $Psi subset.eq Phi$, including all
maximal ones, and all subgroups
@eq:l2012-extremal-en-paired-corners–@eq:l2012-extremal-en-three-corner-subgroup
in $U$ of type $E_m$. For $U E_6 lr((K))$, this enumeration is given up to a
graph automorphism. For a root system $Phi$ of type $E_m$ corresponding to
$m = 6$, 7 or 8, the Coxeter number is equal to $h = 12$, 18 or 30; moreover,

$ Z_k = U_(h-k) subset.eq M subset.eq C(Z_k), quad k = 4,6 "or" 10. $

Choose some simple roots $alpha_i$ ($1 <= i <= m$) as in
[@bib:l2012-extremal-en-Bourbaki1968, Tables V–VII]. When $M$ has a corner of
height $<= 4$, using Lemma @lem:l2012-extremal-en-corner-full-projection we
infer that either $U$ is of type $E_7$ and $M = T(alpha_7)$ or $U$ is of type
$E_6$ and $M$ is one of the subgroups $T(alpha_1)$ and $T(alpha_6)$ or
$M subset.eq (U_4 inter (T(alpha_1) T(alpha_6))) U_5$. We set

$
  vec(delim: #none, a c d e dots f, b) = (a c[d b]'e dots f)
  := a alpha_1+b alpha_2+c alpha_3+d alpha_4+e alpha_5+dots+f alpha_m.
$

#heading(level: 4, numbering: none)[A) The commutative normal sets $Psi$,
  including all maximal ones] <ss:l2012-extremal-en-e-commutative-sets>

Type $E_6$:

$
  {11[10]'10}^+ union {01[21]'21}^+, quad
  {11[10]'11}^+ union {tilde(mu)_4+alpha_1}^+ union {tilde(mu)_4+alpha_6}^+,
  quad {alpha_1}^+, quad {tilde(mu)_4}^+,
$

where $tilde(mu)_4 = (01[21]'10)$ (the highest root of subsystem of type $D_4$
with the root $alpha_4$);

Type $E_7$:

$ {alpha_7}^+, quad {12[32]'210}^+ union {00[11]'111}^+, $
$ {12[31]'210}^+ union {01[21]'111}^+, $
$ {12[21]'210}^+ union {12[21]'111}^+ union {01[21]'211}^+, $
$ {12[21]'110}^+ union {01[21]'221}^+, $
$ {11[21]'210}^+ union {01[21]'211}^+ quad "(not maximal)", $
$ {12[21]'100}^+, quad {01[21]'210}^+; $

#source(12, printed: 109) Type $E_8$:

$ {12[32]'2100}^+, quad {12[31]'3210}^+, $
$ {12[32]'3210}^+ union {12[31]'3211}^+ quad "(not maximal)", $
$ {12[32]'2210}^+ union {12[31]'3321}^+, $
$ {12[42]'3210}^+ union {12[31]'2221}^+, $
$ {13[42]'3210}^+ union {12[21]'2221}^+, $
$ {23[42]'3210}^+ union {11[21]'2221}^+, $
$ {12[32]'3210}^+ union {12[32]'2221}^+ union {12[31]'3221}^+, $
$ {01[21]'2221}^+. $

#heading(level: 4, numbering: none)[B) The roots $r$ defining the subgroup
  @eq:l2012-extremal-en-paired-corners] <ss:l2012-extremal-en-e-paired-roots>

Type $E_6$:
$ (11[11]'00), quad (11[11]'10), quad tilde(mu)_4; $

Type $E_7$:

$ (11[10]'111), quad (12[21]'100), quad (12[21]'110), $
$ (11[21]'210), quad (11[21]'111), quad (11[11]'111); $

Type $E_8$:

$
  (12[32]'2111), quad (12[32]'2211), quad (12[31]'3211), quad (12[32]'3211),
$
$ (12[21]'2221), quad (11[21]'2221), quad (01[21]'2221). $

#heading(level: 4, numbering: none)[C) The pairs ${r,p}$ for $E_6$ and ${r,r'}$
  for $E_7$, $E_8$, defining the subgroup
  @eq:l2012-extremal-en-linked-three-corners]
<ss:l2012-extremal-en-e-linked-pairs>

Type $E_6$:

$
  {(11[11]'00),alpha_5}, quad {(11[11]'10),alpha_6}, quad {(11[11]'10),alpha_4};
$

Type $E_7$:

$ {(12[21]'100),(11[21]'211)}, quad {(12[21]'110),(11[21]'210)}, $
$ {(12[21]'110),(11[21]'111)}, quad {(11[21]'210),(11[21]'111)}, $
$ {(12[21]'210),(11[11]'111)}, quad {(12[31]'210),(11[10]'111)}; $

Type $E_8$:

$ {(12[31]'3221),(12[32]'2111)}, quad {(12[31]'3211),(12[32]'2211)}, $
$ {(12[31]'2221),(12[31]'3211)}, quad {(12[31]'2221),(12[32]'2211)}, $
$ {(12[21]'2221),(12[32]'3211)}, quad {(11[21]'2221),(12[42]'3211)}. $

#heading(level: 4, numbering: none)[D) The corners ${r,r'}$ defining the
  subgroup @eq:l2012-extremal-en-d4-paired-closure with q-connected corners in
  the commutator group $[M,X_p]$] <ss:l2012-extremal-en-e-closure-pairs>

For types $E_6$, $E_7$, and $E_8$ such corners are

$ {(11[10]'10),(01[10]'11)}, quad {(01[21]'210),(01[21]'111)}, $
$ {(12[31]'3210),(12[32]'2210)}, $

respectively.

#heading(level: 4, numbering: none)[E) The pairwise p-connected or q-connected
  corners ${r_1,r_2,r_3}$ of the subgroup
  @eq:l2012-extremal-en-three-corner-subgroup] <ss:l2012-extremal-en-e-triples>

Type $E_8$:
$ {(12[31]'2221),(12[31]'3211),(12[32]'2211)}; $

Type $E_7$:
$ {(12[21]'110),(11[21]'210),(11[21]'111)}; $

Type $E_6$:
$ {(11[11]'10),tilde(mu)_4,(01[11]'11)}. $
