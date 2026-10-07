#import "../../main-defs.typ": *
#import "../../statements.typ": *
#import "defs.typ": *
#import "diagrams/roots.typ": coxeter-rows

=== Centralizers of graph automorphisms <sec:l2022-graph-centralizers>

For a reduced root system $Phi$, it is well-known that the number

$ p(Phi) := max{frac(lr((r,r)), lr((s,s))) | r,s in Phi} $

is equal to 1 or 2, or $Phi$ is of type $G_2$ and $p(Phi) = 3$.

The root systems of the same length (i.e. with $p(Phi) = 1$), having a
non-trivial symmetry of order 2, are exhausted by the types $A_n$, $D_n$ and
$E_6$ with Coxeter graphs, correspondingly,

#source(4, printed: 681)
#coxeter-rows(("A", "D", "E"))

In these cases the graph automorphism $theta$ is defined for the Chevalley
algebra and for its subalgebra $N Phi(K)$. In addition, either $theta$ is of
order 2, or $Phi$ is of type $D_4$ and $theta^3 = 1$.

By [@bib:l2022-graph-Serre1966, Ch. V, Sec. 15], a Coxeter graph gives a _Dynkin
diagram_, if we mark each node $r$ by a number $(r,r)$ (we assume that short
roots have squared length 1).

The root systems of type $B_n$ and $C_n$ are dual and they have the same Coxeter
graph. However, Dynkin diagrams for these types coincide when $n = 2$. In this
case the root systems are equivalent and the Coxeter graph has a non-trivial
symmetry of order 2, as for types $F_4$ and $G_2$:

#coxeter-rows(("B", "C", "F", "G"))

Note that Chevalley algebras (in contrast to Chevalley groups) of types $F_4$,
$G_2$ and $B_2 = C_2$ do not have a graph automorphism
[@bib:l2022-graph-Seligman1959].

We study the centralizer $C(theta)$ of the graph automorphism $theta$ of the Lie
algebra $N Phi(K)$, i.e. the subalgebra of all $theta$-stationary elements. Note
that the root system of type $A_(2n)$, by [@bib:l2022-graph-Levchuk1982, Lemma
@lem:l1982-parabolic-root-folding], has a homomorphism to the unreduced root
system of type $B C_n$.

The main result of the article is

#theorem[Let $theta$ be a non-trivial graph automorphism of a Lie algebra
  $N Phi(K)$, where $op("rank") Phi >= 4$. Then one of the following statements
  is valid.

  #enum(
    numbering: "(a)",
    [$theta^3 = 1$, $Phi$ is of type $D_4$ and
      $C(theta) tilde.eq N G_2 lr((K))$;],
    [$theta^2 = 1$, $Phi$ is of type $D_n$ ($n >= 4$) and
      $C(theta) tilde.eq N B_(n-1) lr((K))$;],
    [$theta^2 = 1$, $Phi$ is of type $A_(2n-1)$ ($n >= 3$) and
      $C(theta) tilde.eq N C_n lr((K))$;],
    [$theta^2 = 1$, $Phi$ is of type $E_6$ and
      $C(theta) tilde.eq N F_4 lr((K))$;],
    [$theta^2 = 1$, $Phi$ is of type $A_(2n)$ ($n >= 2$) and the centralizer
      $C(theta)$ in $N A_(2n) lr((K))$ is a subalgebra associated with the
      unreduced root system of type $B C_n$.],
  )
] <th:l2022-graph-centralizer-types>

A special case was considered in [@bib:l2022-graph-Egorychev2023, Lemma 3.6].

#lemma[The algebra $R B_n lr((K))$ is represented in the algebra
  $R D_(n+1) lr((K))$ by a centralizer of the graph automorphism $theta$ of
  order 2 of the Lie algebra $R D_(n+1) lr((K))^((-))$.
] <lem:l2022-graph-classical-envelope>
