#import "../../main-defs.typ": *
#import "defs.typ": *

=== Bases of the Abelian Factors of $Aut R/R^k$
<sec:l2008-monic-abelian-factors>

#source(7, printed: 386) In this paragraph we study the subgroup $Gamma_s$
($1 < s < k$) of all automorphisms of $R/R^k$ which act identically modulo
$R^s/R^k$. We find an algorithm constructing the bases of a subgroup of tame
automorphisms of the factor $Gamma_s/Gamma_(s+1)$ as a linear space. In the
dimension counts below, $R$ is the augmentation ideal of the free associative
algebra $A_n$.

#lemma[$Aut R/R^k tilde.eq Gamma_2 ⋊ tilde(GL)_n lr((F))$.]
<lem:l2008-monic-linear-semidirect-product>

#proof[It is an obvious consequence of Proposition
  @prop:l2008-monic-affine-reduction.]

To shorten our expressions we use the tensor notation for summation and ordered
n-tuples:

$ (a_i) := (a_1,a_2,dots,a_n), quad a_i b^i := sum_(i=1)^n a_i b^i. $
<eq:l2008-monic-tensor-notation>

Let $F$ be an algebraically closed field. Every element of $Gamma_s/Gamma_(s+1)$
has the form @eq:l2008-monic-monic-endomorphism with an n-tuple
$(phi_1,dots,phi_n)$ over $R^s/R^(s+1)$. The multiplication of two elements of
$Gamma_s/Gamma_(s+1)$ is equivalent to the addition of the corresponding tuples.
If $phi in Gamma_s/Gamma_(s+1)$ then using the notation
@eq:l2008-monic-tensor-notation we write
$phi = (x_i + a_i^(j_1 dots j_s) x_(j_1) dots x_(j_s))$. Let $g in F^times$,
$gamma = g E in GL_n lr((F))$. Then,

$
  tilde(gamma)^(-1) phi tilde(gamma)
  = (x_i + g^(s-1) a_i^(j_1 dots j_s) x_(j_1) dots x_(j_s)).
$
<eq:l2008-monic-scalar-conjugation>

The conjugation @eq:l2008-monic-scalar-conjugation is equivalent to the
multiplication of the tuple $(phi_1,dots,phi_n)$ by a nonzero constant; the zero
tuple corresponds to the identity automorphism. We may define a bijection
$phi arrow.r hat(phi)$ between the elements of $Gamma_s/Gamma_(s+1)$ and the
linear space $V_s$ of the ordered n-tuples over $R^s/R^(s+1)$ with the operation
of addition and multiplication we have just described. Obviously, those
operations preserve the property of the operands to correspond to tame
automorphisms.

Thus, the tame automorphisms from $Gamma_s/Gamma_(s+1)$ induce some subspace
$T V_s$ of $V_s$. In the group $TAut R/R^k$ we introduce the following subset

$ Phi = {phi_i^j | i = 2,3,dots,k-1, j = 1,2,dots,d_i} $
<eq:l2008-monic-layer-bases>

such that the automorphisms ${phi_s^j}_(j=1)^(d_s)$ induce a basis of $T V_s$
for each $s$. Evidently, we may choose a subset $Phi$ containing the
automorphisms of the form @eq:l2008-monic-monomial-shear for all monomials $m_i$
in $R^2/R^k$ not containing $x_1$. Then it is easy to construct an algorithm to
check if a given monic automorphism of $R/R^k$ is tame or wild by consecutively
expressing it in each factor $Gamma_s/Gamma_(s+1)$ using the basis of the linear
space $T V_s$.

We construct an algorithm expressing a given monic automorphism $psi(r)$
($r in F$) in a given subset $Phi' = {phi_i^j}$, $i = 2,3,dots,k-1$,
$j = 1,2,dots,d'_i$ of $Phi$.

#algorithm[

  + Let $psi_2 = psi$.
  + If $psi_s in Gamma_s$ ($2 <= s <= k$) is the identity, then the test is a
    success. Otherwise let ${hat(phi)_s^j}_(j=1)^(d'_s)$ be elements of $T V_s$
    induced by $phi_s^j$, $j = 1,2,dots,d'_s$.
  + Regard $hat(psi)_s lr((r))$ as a polynomial in $r$ with vector-coefficients
    $c_s^u$. Since $r$ is an arbitrary element of the field, we express each
    vector-coefficient $c_s^u$ in $hat(phi)_s^i$, and find

    $
      hat(psi)_s lr((r)) = sum_(i=1)^(d'_s) sum_u alpha_i^u r^u hat(phi)_s^i,
      quad c_s^u = sum_(i=1)^(d'_s) alpha_i^u hat(phi)_s^i.
    $
    <eq:l2008-monic-layer-expansion>

  + #source(8, printed: 387) If the procedure of step 3 did not succeed, then
    $psi_s$ is not expressed in $Phi'$.
  + If step 3 gives the coefficients $b_i lr((r)) = sum_u alpha_i^u r^u$, choose
    $g_i in F^times$ with $g_i^(s-1) = b_i lr((r))$ for each nonzero
    $b_i lr((r))$, put $delta_i = (g_i x_1,dots,g_i x_n)$, and set
    $psi_(s+1) = psi_s product_(i: b_i lr((r)) != 0)
    (delta_i^(-1) phi_s^i delta_i)^(-1)$. Since $psi_(s+1) in Gamma_(s+1)$, we
    proceed to step 2 with $s+1$.

] <rem:l2008-monic-algorithm-one>

For each $tilde(lambda) in tilde(GL)_n lr((F))$ and $phi_i^j in Phi$ an
automorphism $phi' = tilde(lambda)^(-1) phi_i^j tilde(lambda)$ can be expressed
in $Phi$ using algorithm~@rem:l2008-monic-algorithm-one. It should hold for all
elementary and diagonal matrices $lambda$, in particular, for the following
$n times n$ matrices

$ gamma_p lr((r)) = diag(1, 1, dots, r, 1, dots, 1) $
<eq:l2008-monic-diagonal-matrices>

where $r in F^times$ is the p-th element of the diagonal.

Algorithm~@rem:l2008-monic-algorithm-two below is based on the latter
requirement and constructs the sought set $Phi$.#ed-note[The interpolation step
  applies to polynomial parameter families, or Laurent polynomial families after
  clearing denominators. The scalar roots chosen in
  Algorithm~@rem:l2008-monic-algorithm-one need not preserve this dependence in
  subsequent residual families. The argument given here does not justify that
  additional requirement and therefore does not establish the general
  termination assertion below.]

#algorithm[

  + Let ${m_i^s}_(i=1)^(M_s)$ be the set of all monomials of degree $s+1$ over
    $x_2,x_3,dots,x_n$. Initially,
    $Phi' = {(x_1+m_i^s,x_2,dots,x_n) | 1 <= s <= k-2, 1 <= i <= M_s}$.
  + For each fixed constant $r$ there is a finite number of elementary matrix
    types $t(r)$ and a finite number of diagonal matrix types $gamma_p lr((r))$.
    If, as parameter families, for each elementary matrix $t(r)$, diagonal
    matrix $gamma_p lr((r))$ and for each $phi in Phi'$ automorphisms
    $tilde(t)(r)^(-1) phi tilde(t)(r)$ and
    $tilde(gamma)_p lr((r))^(-1) phi tilde(gamma)_p lr((r))$ are expressible in
    $Phi'$, then $Phi = Phi'$ is the sought set.
  + Let $psi(r) in Gamma_s$ be not expressible in $Phi'$ with
    algorithm~@rem:l2008-monic-algorithm-one. Regarding its first unexpressed
    layer $hat(psi)(r)$ as a polynomial, or a Laurent polynomial for diagonal
    conjugations, multiply by a suitable power of $r$ to obtain a polynomial of
    degree $d$. Choose $d+1$ distinct admissible elements $f_0,dots,f_d$ of $F$
    (all nonzero for diagonal conjugations). Add those residuals $psi(f_i)$ to
    $Phi'$ for which $hat(psi)(f_i)$ cannot be linearly expressed in
    ${hat(phi)_s^j}_(j=1)^(d'_s)$, preserving linear independence, and go to
    step 2.

] <rem:l2008-monic-algorithm-two>

The following well-known Lemma~@lem:l2008-monic-vector-interpolation together
with Lemma~@lem:l2008-monic-algorithm-termination prove the correctness of
algorithm~@rem:l2008-monic-algorithm-two.

#lemma[Let $f(r) = alpha_0+alpha_1 r+dots+alpha_p r^p$, where $alpha_i$ are
  vector-coefficients. If $a_0,a_1,dots,a_p$ are different elements of the field
  $F$ then $f(r)$ can be linearly expressed in $f(a_0),f(a_1),dots,f(a_p)$ for
  any $r$.]
<lem:l2008-monic-vector-interpolation>

#lemma[If $F$ is an algebraically closed field then
  algorithm~@rem:l2008-monic-algorithm-two terminates in a finite number of
  steps and constructs such set $Phi$ that any tame automorphism may be
  expressed in $Phi union tilde(GL)_n lr((F))$ in a finite number of steps using
  algorithm~@rem:l2008-monic-algorithm-one.]
<lem:l2008-monic-algorithm-termination>

#proof[$V_s$ is an $n^(s+1)$-dimensional linear space; the chosen elements of
  $Phi$ in layer $s$ induce linearly independent elements of $T V_s$.

  Evidently, the $d+1$ distinct admissible interpolation points required on step
  3 of algorithm~@rem:l2008-monic-algorithm-two always exist. By
  Lemma~@lem:l2008-monic-vector-interpolation, if $hat(psi)(r)$ cannot be
  linearly expressed in ${hat(phi)_s^j}_(j=1)^(d'_s)$ then one of the vectors
  $hat(psi)(f_0),dots,hat(psi)(f_d)$ also cannot be linearly expressed in
  ${hat(phi)_s^j}_(j=1)^(d'_s)$. Thus, algorithm~@rem:l2008-monic-algorithm-two
  adds at least one linearly independent element to $Phi'$ each time step 3 is
  executed. Hence the algorithm finishes in a finite number of steps.

  The obtained set $Phi$ satisfies the following condition: for each
  $phi in Phi$ and any elementary matrix $t(r)$ or a diagonal matrix
  $gamma_p lr((r))$ @eq:l2008-monic-diagonal-matrices automorphisms
  $tilde(t)(r)^(-1) phi tilde(t)(r)$ and
  $tilde(gamma)_p lr((r))^(-1) phi tilde(gamma)_p lr((r))$ can be expressed in
  $Phi$ using algorithm~@rem:l2008-monic-algorithm-one since it was the
  condition of termination.

  Let us show that any automorphism $tilde(lambda)^(-1) e tilde(lambda)$, where
  $tilde(lambda) in tilde(GL)_n lr((F))$, $e = (x_i+delta_i^1 m)$, $m$ being
  some monomial over $x_2,dots,x_n$, may be expressed in $Phi$ using
  algorithm~@rem:l2008-monic-algorithm-one. Elements
  $phi_s^j in Phi inter (Gamma_s without Gamma_(s+1))$ induce some linearly
  independent subset ${hat(phi)_s^j}$ of $T V_s$. Let us prove that
  $tilde(lambda)^(-1) e tilde(lambda)$ can be expressed #source(9, printed: 388)
  in this subset modulo $R^(s+1)$. Any matrix $lambda$ may be decomposed in a
  product of $q$ elementary matrices $t_1,dots,t_q$ for some $q$ and a diagonal
  matrix $gamma$. Initially $e$ is in the span of $Phi$ in its layer. We have:

  $
    tilde(lambda)^(-1) e tilde(lambda)
    = tilde(gamma)^(-1) tilde(t)_q^(-1) dots tilde(t)_1^(-1)
    e tilde(t)_1 dots tilde(t)_q tilde(gamma).
  $
  <eq:l2008-monic-linear-conjugation>

  Using algorithm~@rem:l2008-monic-algorithm-one and the expression of
  $tilde(t)_1^(-1) e tilde(t)_1$ in $Phi$, as above, we obtain:

  $
    tilde(lambda)^(-1) e tilde(lambda)
    = product_(j=1)^w (tilde(gamma)^(-1) tilde(t)_q^(-1) dots
      tilde(t)_2^(-1) (alpha_j^(-1) x_i) phi_s^j (alpha_j x_i)
      tilde(t)_2 dots tilde(t)_q tilde(gamma)) mod Gamma_(s+1).
  $

  Since the element $(alpha_j x_i)$ commutes with any element of
  $tilde(GL)_n lr((F))$,

  $
    tilde(lambda)^(-1) e tilde(lambda)
    = product_(j=1)^w (tilde(gamma)'_j^(-1) tilde(t)_q^(-1) dots
      tilde(t)_2^(-1) phi_s^j tilde(t)_2 dots tilde(t)_q
      tilde(gamma)'_j) mod Gamma_(s+1),
  $
  <eq:l2008-monic-shorter-conjugations>

  where $tilde(gamma)'_j = tilde(gamma)(alpha_j x_i)$. Each multiplier in
  @eq:l2008-monic-shorter-conjugations is similar to
  $tilde(lambda)^(-1) e tilde(lambda)$ in @eq:l2008-monic-linear-conjugation
  only with $q-1$ elementary matrices remaining. By induction we decompose
  $tilde(gamma) tilde(lambda)^(-1) e tilde(lambda) tilde(gamma)^(-1)$ in
  ${hat(phi)_s^j}$ modulo $R^(s+1)$. Since $gamma$ is a product of diagonal
  matrices of the form $gamma_p lr((r))$, we repeat the same reasoning for
  diagonal matrices.]

The following theorem gives a sufficient condition of an automorphism to be
wild. Let $A_n$ be a free associative algebra over a field $F$, as above, and
$A'_n$ be a free associative algebra over the algebraic closure of the field
$F$. Denote by $R'$ an ideal $〈x_1,x_2,dots,x_n〉$ of $A'_n$.

#theorem[Let $phi in Aut A_n$. Reduce $phi$ by a tame affine factor as in
  Proposition~@prop:l2008-monic-affine-reduction, and let $tilde(phi)$ be the
  induced monic automorphism of $R'/R'^k$. Let $Phi$ be the set obtained by
  means of algorithm~@rem:l2008-monic-algorithm-two. If $tilde(phi)$ cannot be
  expressed in $Phi$ using algorithm~@rem:l2008-monic-algorithm-one, then $phi$
  is a wild automorphism of $A_n$.]
<th:l2008-monic-wildness-criterion>

In the case of algebraically closed fields, the constructed set
@eq:l2008-monic-layer-bases allows us to describe all wild automorphisms of the
free nilpotent algebra $R/R^k$. The problem of automorphism lifting for some
free nilpotent groups and algebras is studied in different papers, see
[@bib:l2008-monic-Gupta1992], [@bib:l2008-monic-Gupta1995], etc.

The following lemma describes all automorphisms of a free nilpotent algebra
$R/R^3$ modulo the tame subgroup $TAut R/R^3$. We choose endomorphisms of $R$:

$ sigma_1 = (x_1+x_1 x_2,x_2,dots,x_n), quad sigma_2 = tau(sigma_1) $

for the opposite anti-automorphism $tau: x_i x_j dots x_l arrow.r x_l dots x_j
x_i$ of the ideal $R$. Also set
$tau(phi_1, dots, phi_n) = (tau(phi_1),dots,tau(phi_n))$.#ed-note[Here $R$ is
  the augmentation ideal of the unital free associative algebra $A_n$. No
  automorphism of this $R$ has the quadratic part $sigma_1$ or $sigma_2$.
  Indeed, its unital extension induces an automorphism of the commutative
  quotient $B_n$. An automorphism of $B_n$ has a nonzero constant Jacobian
  determinant. For either displayed quadratic part the linear term of that
  determinant is $x_2$, while terms of degree at least three in the images
  contribute only terms of degree at least two to the Jacobian entries. This
  contradiction holds in every characteristic. The conditional assertion of
  Lemma~@lem:l2008-monic-quadratic-wild-classes therefore has no instance in
  $Aut R$; the displayed quadratic tensors do define automorphisms of the
  nilpotent factor $R/R^3$.]

#lemma[Assume $n >= 3$. If $phi in Aut R$ and $phi = sigma_1$ or $sigma_2$
  modulo $R^3$, then $phi$ is wild. Moreover,

  $ Aut R = 〈phi,tau(phi),TAut R〉 mod R^3. $
]
<lem:l2008-monic-quadratic-wild-classes>

#proof[Let us consider the five endomorphisms

  $
    phi_1 = (x_1+x_2 x_2,x_2,dots,x_n),
    quad phi_3 = (x_1+x_1 x_3,x_2-x_2 x_3,x_3,dots,x_n),
  $
  $ phi_2 = (x_1+x_2 x_3,x_2,dots,x_n), quad phi_4 = tau(phi_3), $
  $ phi_5 = (x_1+x_1 x_3,x_2+x_3 x_2,x_3-x_3 x_3,x_4,dots,x_n). $

  Modulo $R^3$ we have

  #source(10, printed: 389)
  $
    phi_3 = (x_1,x_2+x_1,x_3,dots,x_n)^(-1) dot phi_2 dot
    (x_1,x_2+x_1,x_3,dots,x_n) dot
    (x_1-x_2 x_3,x_2,dots,x_n) dot (x_1,x_2+x_1 x_3,x_3,dots,x_n),
  $

  $
    tau(phi_5)^(-1) = (x_3,x_2+x_3,x_1+x_3,x_4,dots,x_n)^(-1) dot phi_2 dot
    (x_3,x_2+x_3,x_1+x_3,x_4,dots,x_n) dot
    (x_1+x_2 x_3+x_3 x_3,x_2,dots,x_n) dot
    (x_1,x_2+x_3 x_1+x_3 x_3,x_3,dots,x_n) dot
    (x_1,x_2,x_3-x_2 x_1,x_4,dots,x_n) dot
    (x_1,x_3,x_2,x_4,dots,x_n) dot phi_4 dot (x_1,x_3,x_2,x_4,dots,x_n) dot
    (x_3,x_1,x_2,x_4,dots,x_n) dot phi_3 dot (x_2,x_3,x_1,x_4,dots,x_n).
  $

  It is obvious that $phi_1$ and $phi_2$ are the initial elements of $Phi$ in
  algorithm~@rem:l2008-monic-algorithm-two, and the remaining elements are
  constructed by conjugating those elements with elementary matrices, i.e.,
  using the transformations from algorithms~@rem:l2008-monic-algorithm-one and
  @rem:l2008-monic-algorithm-two. The substitutions over $x_1,dots,x_n$ may also
  be considered as the products of elementary matrices. The whole set $Phi$
  linearly generating $T V_2$ would consist of elements up to a substitution
  equal to $phi_i$, $i = 1,dots,5$.

  One may notice that any element $xi_0^(-1) phi_i xi_0$ in the set
  ${xi^(-1) phi_i xi | xi in S_n}$ is uniquely defined by not more than 3
  indices $k,l,m$. Hence to check that $Phi$ and $GL_n lr((F))$ generate
  $TAut R/R^3$ we don’t have to consider all cases of the position $(i,j)$ of
  $r$ in the elementary matrix $t(r)$. We may let the indices be $1,2,3$ (since
  there exists a transformation mapping $k,l,m$ in $1,2,3$) and consider
  $4 times 4$ elementary matrices. Hence we can in a finite number of steps
  prove that for each $n$ such set $Phi$ really satisfies the condition of
  algorithm~@rem:l2008-monic-algorithm-two termination.

  The dimension of $V_2$ is, obviously, $n^3$. Let $tau_i$ be an automorphism,
  exchanging $x_2$ and $x_i$. Then it is easy to verify that $|Phi| = n^3-2n$
  and $2n$ corresponds to the remaining wild automorphisms $tau_i sigma_1
  tau_i$ and $tau_i sigma_2 tau_i$.]
