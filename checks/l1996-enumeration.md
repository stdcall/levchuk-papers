# Enumeration of characteristic subgroups (1996)

The following checks concern the formulas and intermediate arguments in
Egorychev and Levchuk, pp. 49–62. They do not constitute a proof of the
classification of automorphisms or normal subgroups used by the article.

## Exact computations

`sage/l1996_enumeration/check.py` uses independent root-poset antichain
enumeration for A₁–A₆, B₂–B₇, C₂–C₇ and D₄–D₇. It agrees with the
ordinary untwisted cases of Theorem 2. The root-generation hypothesis is
essential: root-poset ideals alone do not describe the characteristic-two
groups of types B and C.

Dynamic enumeration of diagonal paths checks both formulas in Lemma 5
for 1 ≤ X ≤ 24 and 0 ≤ Y ≤ X with the required parity. “Above” means
strictly above after the initial vertex. The endpoint X = 0 is excluded
from formula (5); negative heights and nonintegral endpoints are not used.

The triple sum in Lemma 6, the double sum in Lemma 7, and their substitution
into formula (10) agree with the closed answers for 3 ≤ n ≤ 40. All
arithmetic is rational or integral. These are finite checks, not proofs of
the integral interchanges or the identities for every n.

A separate calculation constructs symplectic root matrices over
GF(2)[x,y], computes every pairwise group commutator, and exhaustively
enumerates root-coordinate supports closed under these commutators for
C₁–C₄. The counts are 2, 7, 26, 99, agreeing with
4ⁿ⁻¹ + binom(2n−1,n). For every pair the calculation checks that the
commutator minus the identity equals the sum of its extracted root
coefficients times their root matrices, and that every product of two
supported target root matrices is zero. Consequently the corresponding
root factors multiply to exactly that matrix, without cross terms: these
are collected root coordinates, rather than unverified matrix-entry
supports. Closure under these commutators allows the root factors to be
reordered within the chosen support, and conjugation by every ambient
root generator preserves the generated subgroup. Distinct supports are
distinguished by the usual unique ordered root factorization.
The calculation concerns root-coordinate subgroups;
completeness among D-invariant subgroups is the external classification
used in Lemma 3. The polynomial calculation includes the quadratic terms
which disappear from the Lie bracket and distinguishes the group problem
from enumeration of Lie ideals. It does not establish the Bₙ assertion
over imperfect fields.

## Formal statements

`lean/LevchukPapers/Enumeration1996/Antichain.lean` proves:

- `antichain_upward_injective`: in any partial order, two antichains with
  equal upward closures coincide. The predicates A and B are the two
  sets of roots; the antichain assumptions are pairwise nonincidence.
  This proves the combinatorial injectivity step in Lemma 1, conditional
  on the root-coordinate description, without a rank bound.
- `commutator_coefficient_determinant`: over any field, the coefficient
  vectors (a,a²), (b,b²) have nonzero determinant for distinct nonzero
  a,b. These are explicit parameter hypotheses, not a hypothesis that
  the desired closure already holds. This isolates the separation step
  behind equation (2); it does not prove the commutator formula itself.
- `substitution_discriminant`: the polynomial identity
  1−4x(1−x)=(1−2x)² used in Lemma 7. Selection of the analytic branch is
  outside this statement.

All three declarations compile with Lean 4.35.0-rc2. The first uses no
axioms; the other two use only the standard propext, Quot.sound, and
(for the field statement) Classical.choice. There are no admitted proofs.

`lean/LevchukPapers/Enumeration1996/C2Characteristic.lean` additionally
formalizes the four root coordinates of the characteristic-two C₂ model.
For an arbitrary commutative ring of characteristic two it proves
associativity of the displayed coordinate multiplication, preservation
of multiplication by the graph map, and that the square of that map
is the coordinatewise Frobenius. It proves bijectivity over every finite
field of characteristic two, deriving square-root existence from
finiteness and reducedness. No fourth-power identity or perfectness
conclusion is assumed. Finally C(1) belongs to the short central-root
coordinate subset and its graph image does not. The six declarations
compile with only the standard axioms and no admitted proofs.
The Sage file additionally checks the multiplication law and the graph
formula as polynomial matrix identities over
GF(2)[s,t,u,v,S,T,U,V]. These two symbolic identities connect the Lean
coordinate operation to the symplectic matrices in every characteristic-two
specialization. This bridge is supplied by Sage rather than a Lean
matrix construction. The formal file therefore
checks the coordinate automorphism, not the general subgroup count.

## Textual and mathematical qualifications

The characteristic-two branch of Theorem 1 is false at n=2, K=GF(4):
it predicts 7 characteristic subgroups of U(C₂,GF(4)), whereas the
explicit group of order 256 has exactly 3, of orders 1,16,256.
`gap/l1996_enumeration/c2_characteristic.g` independently computes the
complete list using GAP's `CharacteristicSubgroups` after an isomorphism
to a pc group. This conclusion concerns this single field and rank;
it is not a replacement formula for every characteristic-two field.

The companion Sage file `sage/l1996_enumeration/c2_characteristic.py`
constructs a maximal unipotent subgroup of the symplectic group in
basis e₁,e₂,f₁,f₂. Put
A=E₁₂+E₄₃, B=E₂₄, C=E₁₄+E₂₃, D=E₁₃ and write
a(s)=I+sA, b(t)=I+tB, c(u)=I+uC, d(v)=I+vD. It verifies an automorphism
on every ordered pair of the 256 elements, given on these generators by
a(s)↦b(s²), b(t)↦a(t), c(u)↦d(u²), d(v)↦c(v).
The subgroup c(GF(4)) is central and invariant under every symplectic
diagonal torus element diag(λ,μ,λ⁻¹,μ⁻¹); the automorphism moves it
to the distinct subgroup d(GF(4)). Thus a subgroup counted by the
D-invariant enumeration need not be characteristic in this case.
The final Sage counterexample run reports 67,117 exact checks, including
the two polynomial matrix bridge identities.
The seven-subgroup computation in Theorem 2 remains consistent: it is
the transfer to the characteristic count that fails.

Levchuk (1990), *Automorphisms of unipotent subgroups of groups of Lie
type of small ranks*, §1 and §3, Remark 2 (p.151), explicitly
includes graph automorphisms among standard automorphisms and discusses
additional semigraphical automorphisms of UB₂ over GF(2) and GF(4).
The later 2001 Theorem 2 repeats the erroneous characteristic-count
branch; repetition does not repair this concrete counterexample.
Both statements now restrict this branch to n>2. This excludes the
counterexample; it does not supply a new count for rank two or a proof
of every remaining field and rank.

The later article *Enumeration in the Chevalley algebras*
(2001), §2, Theorems 2–3, states the field hypothesis as order greater
than two. It also explicitly supplies G=Cₙ in the characteristic-count
case binom(2n,n)−1 and writes the twisted orthogonal index as ²Dₙ₊₁.
These resolve the contradictory characteristic hypothesis, omitted type,
and shifted twisted index in the 1996 theorem statements.

The definition of the root order on p.51 is the usual one: s≤r when
r−s is a nonnegative sum of simple roots. Normal root subgroups therefore
correspond to upward closures. The printed inequalities s≤rᵢ in the
definition of T and its repetitions conflict with this order. The 2001
definition correctly has rᵢ≤s. In type A₂ a subgroup for a simple root
must include the highest-root group, which makes the direction concrete.
This order issue must be treated consistently in the characteristic-two
paragraphs as well; the root-poset checks use the usual order explicitly.

On p.61 the inverse branch for w=x(1−x) through x=0 is
x=(1−sqrt(1−4w))/2. The printed plus branch gives x=1 at w=0.
The subsequent positive square-root coefficient in the integral agrees
with the corrected minus branch. The omitted constant 1/4 in the
transformed integrand has zero residue for n≥1.

Lemma 1's field conditions are intended cumulatively by type, not as a
literal unrestricted disjunction: for Bₙ,Cₙ the ordinary root-poset
description needs 2K=K. Its characteristic-two exception is then handled
in Lemmas 3–4. The 2001 root-ideal lemma states this cumulative condition
explicitly. On p.54 the passage from Cₙ to Bₙ invokes a perfect field;
the theorem statement does not repeat that hypothesis. The available
argument therefore leaves the imperfect-field case unestablished here.

Levchuk (1990), part II, §5, describes the extra characteristic-subgroup
conditions for Cₙ in characteristic different from 2 and 3 and for GF(3),
in agreement with the two subtraction cases in Theorem 1. Levchuk (1992),
§§4 and 6, distinguishes Lie-ideal and adjoint-group questions in small
characteristic. Egorychev–Levchuk (2013), Introduction and main theorem,
recovers the type A Catalan specialization. These comparisons check the
scope and interpretation; they do not independently prove every branch
of Theorem 1, especially the twisted and small-field exceptions.

## Reproduction

Run `sage -python checks/sage/l1996_enumeration/check.py` and
`sage -python checks/sage/l1996_enumeration/c2_characteristic.py` from
the project root. The successful runs on 2026-10-25 report 956 and
67,117 checks. Run
`gap -q -b --quitonbreak checks/gap/l1996_enumeration/c2_characteristic.g`
to reproduce the three characteristic subgroups. Compile both Lean files
in the project's
pinned mathlib environment and inspect their nine `#print axioms` outputs.
General classifications, convergence of the contour manipulations, and
all-field twisted-group enumeration remain
outside the machine-checked scope.
