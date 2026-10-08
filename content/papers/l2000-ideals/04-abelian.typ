#import "defs.typ": *

=== Abelian ideals of $R_n lr((K,J))$ <sec:l2000-ideals-abelian>

In this section we apply Theorem~@th:l2000-ideals-boundary-classification in
order to describe maximal abelian ideals in the ring $R_n lr((K,J))$ when
$K=ZZ_(p^m)$ and $J=(p)$. It is convenient now to assume that always $J^0=K$.

#theorem[
  Suppose that $K=ZZ_(p^m)$ and $J=(p)$. If $m$ is even, then
  $M_n lr((J^(m/2)))$ is unique maximal abelian ideal of the ring
  $R_n lr((K,J))$, $n>=2$. If $m=2s+1$ is an odd integer, then the ring
  $R_n lr((K,J))$ has $(n-2)p+1$ maximal abelian ideals which have the form:
  $
    N_(i,i-1) lr((J^s))+M_n lr((J^(s+1))),
    quad 1<i<=n, quad "if" n=2 "and" s=0 "or" n>2;
  $
  $
    J^s e+N_21 lr((J^s))+M_2 lr((J^(s+1)))
    quad "if" n=2 "and" s>0;
  $
  $
    N_(i+1,i-1) lr((J^s))+M_n lr((J^(s+1)))+J^s lr((e_(i 1)+c e_(n i))),
    quad 1<i<n, quad 1<=c<p.
  $
] <th:l2000-ideals-maximal-abelian>

#source(10, printed: "3511")
#proof[
  Let $H$ be an arbitrary maximal abelian ideal of $R_n lr((K,J))$ and
  $T=pi_(n 1) lr((H))$. Since
  $
    (sum_(k,u)a_(k u)e_(k u))e_(1 n)(sum_(v,t)b_(v t)e_(v t))
    =sum_(k,t)(a_(k 1)b_(n t))e_(k t)
  $
  we obtain $pi_(n 1) lr((H ast (J e_(1 n)H)))
  =pi_(n 1) lr((H(J e_(1 n))H))=T J T$. However, $H ast (J e_(1 n)H)=0$ since
  $H$ is an abelian ideal. Hence $T^2 J=0$. Taking into account inclusions
  @eq:l2000-ideals-projection-bounds we obtain
  $H M_n lr((J T))=M_n lr((J T))H=0$ and
  $ M_n lr((J T)) subset.eq H subset.eq M_n lr((T)) $
  <eq:l2000-ideals-maximal-abelian-bounds>
  since $H$ is a maximal abelian ideal.

  Now we find centralizer $C(M_n lr((T)))$ of $M_n lr((T))$ in the ring
  $R_n lr((K,J))$. Let $Ann_K T$ be the annihilator of $T$ in $K$, and
  $alpha=||a_(u v)|| in R_n lr((K,J))$. Then $alpha$ is in the centralizer
  $C(T e_(k m))$ of $T e_(k m)$ in $R_n lr((K,J))$ if and only if
  $a_(k k)=a_(m m) quad mod (Ann_K T)$ and all other elements of $k$-th column
  and $m$-th row of $alpha$ are contained in $Ann_K T$. Therefore
  $ C(M_n lr((T)))=J e+M_n lr((Ann_K T)) inter R_n lr((K,J)) $
  where $e$ is the identity matrix. It is clear that $M_n lr((T))$ is an abelian
  ideal if and only if $T^2=0$. If $Ann_K T=T subset.eq J$ then the ideal
  $M_n lr((T))$ of $R_n lr((K,J))$ is maximal abelian because any ideal of the
  ring $R_n lr((K,J))$ which is between $M_n lr((T))$ and
  $J e+M_n lr((T)) (=C(M_n lr((T))))$ is equal to $M_n lr((T))$.

  Each ideal of our ring $K$ is equal to $J^t$ for some $t$, $0<=t<=m$, and
  $Ann_K J^t=J^(m-t)$. It follows that if $m$ is even then $M_n lr((J^(m/2)))$
  is a maximal abelian ideal of $R_n lr((K,J))$. Suppose that $T=J^s$. Then we
  have $J^(2s+1)=J T^2=0$ and hence $2s+1>=m$. If $d$ is the integer part of
  $(m+1)/2$ then $M_n lr((J^d)) subset.eq M_n lr((J T))$ or
  $H subset.eq M_n lr((T)) subset.eq M_n lr((J^d))$. Since $M_n lr((J^d))$ is an
  abelian ideal we have $H supset.eq M_n lr((J^d))$ and so $(m-1)/2<=s<=d$. When
  $m$ is even we obtain $d=m/2$ and $H=M_n lr((J^(m/2)))$.

  Assume that $m$ is an odd integer. Then we have $m=2s+1$ and $T=J^s$,
  $J^(s+1)=J T=Ann_K T$. When $s=0$ the conclusion of our theorem holds by
  [@bib:l2000-ideals-Levchuk1976, Theorem~@th:l1976-maximal-abelian]. Let $s$ be
  a positive integer. By @th:l2000-ideals-boundary-classification and by
  @eq:l2000-ideals-maximal-abelian-bounds there exists a set of corners $Lc$ as
  in @eq:l2000-ideals-corners such that
  $ H=A+sum_((i,j) in Lc)Q_(i j) lr((T))+M_n lr((J T)) $
  where $A subset.eq sum_((i,j) in Lc)T e_(i j)$. It is not difficult to show
  that
  $
    C(N_(i j) lr((T)))=J e+
    {N_(j+1,i-1) lr((K))+M_n lr((Ann_K T))} inter R_n lr((K,J)).
  $

  #source(11, printed: "3512")
  Suppose that $(i,j) in Lc$ and $i<=j$. If $i<n$ then
  $N_(i+1,i) lr((T)) subset.eq H$ and so
  $
    H subset.eq C(N_(i+1,i) lr((T))) inter M_n lr((T))
    =T e+N_(i+1,i) lr((T))+M_n lr((J T)).
  $
  Hence $i=j$ and $n=2$. For $j>1$ we obtain the same result. Clear that
  $T e+N_21 lr((T))+M_2 lr((J T))$ for $T=J^s$ is a maximal abelian ideal of
  $R_2 lr((K,J))$. As above all ideals $N_(i+1,i) lr((T))+M_n lr((J T))$ are
  maximal abelian in the ring $R_n lr((K,J))$ for $n>2$.

  We now consider the case when $N_(i+1,i) lr((T)) subset.not H$ for all $i$. It
  is clear that $H subset.eq NT_n lr((T))+M_n lr((J T))$ and if
  $(i_1,j_1),(i_r,j_r) in Lc$ as in @eq:l2000-ideals-corners then
  $1<i_1<=j_r<n$. Suppose, if possible, that $x e_(i 1) in H$ for some $i_1<=i$
  and $x in (T without (J T))$. Then we have $H subset.eq C(x e_(i 1))$ and so
  $pi_(u i) lr((H)) subset.eq Ann_K x=J T$ for all $u$. Consequently $i_1=j_r$
  and if $i=i_1$ then $H inter (T e_(i 1))=J T e_(i 1)$ and
  $H inter (T e_(n i))=J T e_(n i)$. Therefore $H$ is placed in the abelian
  ideal $T(e_(i 1)+c e_(n i))+N_(i+1,i-1) lr((T))+M_n lr((J T))$ for some
  $c in K$ such that $T c=T$. Clear that we can choose $c$ such that $1<=c<p$.

  Finally note that the number of all maximal abelian ideals in the ring
  $R_n lr((K,J))$ for odd $m$ is equal to $(n-1)+(n-2)(p-1)=(n-2)p+1$.
  Theorem~@th:l2000-ideals-maximal-abelian is proved.
]
