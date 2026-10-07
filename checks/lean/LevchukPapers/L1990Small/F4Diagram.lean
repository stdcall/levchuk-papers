import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.List.FinRange

namespace Levchuk1990SmallF4Diagram

set_option maxRecDepth 100000
set_option maxHeartbeats 0

instance {A : Type*} [DecidableEq A] : DecidableEq (Fin 4 → A) := fun f g =>
  if h : ∀ i, f i = g i then isTrue (funext h)
  else isFalse (fun he => h (fun i => congrFun he i))

abbrev Coeff := Fin 4 → ℕ
abbrev Vector := Fin 4 → ℤ

/-- The displayed positive-root coordinates, in Bourbaki simple-root order. -/
def positive : Finset Coeff := ([
  ![1,0,0,0], ![0,1,0,0], ![0,0,1,0], ![0,0,0,1],
  ![1,1,0,0], ![0,1,1,0], ![0,0,1,1], ![1,1,1,0],
  ![0,1,2,0], ![0,1,1,1], ![1,1,2,0], ![1,1,1,1],
  ![0,1,2,1], ![1,2,2,0], ![1,1,2,1], ![0,1,2,2],
  ![1,2,2,1], ![1,1,2,2], ![1,2,3,1], ![1,2,2,2],
  ![1,2,3,2], ![1,2,4,2], ![1,3,4,2], ![2,3,4,2]
] : List Coeff).toFinset

/-- Twice the usual Euclidean coordinates, so every root is integral.
The simple vectors are (0,2,-2,0), (0,0,2,-2), (0,0,0,2), (1,-1,-1,-1). -/
def transform (c : Coeff) : Vector :=
  ![(c 3 : ℤ), 2*c 0-c 3, -2*c 0+2*c 1-c 3, -2*c 1+2*c 2-c 3]

def negate (v : Vector) : Vector := fun i => -v i

/-- Independent standard F4 family: eight axes, 24 signed pairs,
and sixteen half-sum roots, all scaled by two. -/
def standard : Finset Vector :=
  let indices := List.finRange 4
  let signs : List ℤ := [-1,1]
  let axes := indices.flatMap (fun i => signs.map (fun s =>
    (fun k => if k = i then 2*s else 0 : Vector)))
  let pairs := indices.flatMap (fun i => indices.flatMap (fun j =>
    if i < j then signs.flatMap (fun s => signs.map (fun t =>
      (fun k => if k = i then 2*s else if k = j then 2*t else 0 : Vector)))
    else []))
  let halves := signs.flatMap (fun a => signs.flatMap (fun b =>
    signs.flatMap (fun c => signs.map (fun d => (![a,b,c,d] : Vector)))))
  (axes ++ pairs ++ halves).toFinset

def fullFromPositive : Finset Vector :=
  positive.image transform ∪ (positive.image transform).image negate

def simpleStep (a b : Coeff) : Prop :=
  ∃ i : Fin 4, ∀ j : Fin 4, b j = a j + if j = i then 1 else 0

instance (a b : Coeff) : Decidable (simpleStep a b) :=
  inferInstanceAs (Decidable (∃ i : Fin 4, ∀ j : Fin 4,
    b j = a j + if j = i then 1 else 0))

def covers : Finset (Coeff × Coeff) :=
  (positive ×ˢ positive).filter (fun p => simpleStep p.1 p.2)

def componentwiseStrict (a b : Coeff) : Prop :=
  (∀ i : Fin 4, a i ≤ b i) ∧ a ≠ b

instance (a b : Coeff) : Decidable (componentwiseStrict a b) :=
  inferInstanceAs (Decidable ((∀ i : Fin 4, a i ≤ b i) ∧ a ≠ b))

/-- Covers in the componentwise partial order on these positive roots:
there is no positive root strictly between the two endpoints. -/
def hasse (a b : Coeff) : Prop :=
  componentwiseStrict a b ∧
    (positive.filter (fun c => componentwiseStrict a c ∧ componentwiseStrict c b)).card = 0

instance (a b : Coeff) : Decidable (hasse a b) :=
  inferInstanceAs (Decidable (componentwiseStrict a b ∧
    (positive.filter (fun c => componentwiseStrict a c ∧ componentwiseStrict c b)).card = 0))

def hassePairs : Finset (Coeff × Coeff) :=
  (positive ×ˢ positive).filter (fun p => hasse p.1 p.2)

theorem hasse_equals_simple_steps : hassePairs = covers := by decide
theorem hasse_card : hassePairs.card = 34 := by decide


/-- Explicit independently checked enumeration of all simple-root covers. -/
def enumeratedCovers : Finset (Coeff × Coeff) := ([
  (![0,0,0,1], ![0,0,1,1]),
  (![0,0,1,0], ![0,0,1,1]),
  (![0,0,1,0], ![0,1,1,0]),
  (![0,1,0,0], ![0,1,1,0]),
  (![0,1,0,0], ![1,1,0,0]),
  (![1,0,0,0], ![1,1,0,0]),
  (![0,0,1,1], ![0,1,1,1]),
  (![0,1,1,0], ![0,1,1,1]),
  (![0,1,1,0], ![0,1,2,0]),
  (![0,1,1,0], ![1,1,1,0]),
  (![1,1,0,0], ![1,1,1,0]),
  (![0,1,1,1], ![0,1,2,1]),
  (![0,1,1,1], ![1,1,1,1]),
  (![0,1,2,0], ![0,1,2,1]),
  (![0,1,2,0], ![1,1,2,0]),
  (![1,1,1,0], ![1,1,1,1]),
  (![1,1,1,0], ![1,1,2,0]),
  (![0,1,2,1], ![0,1,2,2]),
  (![0,1,2,1], ![1,1,2,1]),
  (![1,1,1,1], ![1,1,2,1]),
  (![1,1,2,0], ![1,1,2,1]),
  (![1,1,2,0], ![1,2,2,0]),
  (![0,1,2,2], ![1,1,2,2]),
  (![1,1,2,1], ![1,1,2,2]),
  (![1,1,2,1], ![1,2,2,1]),
  (![1,2,2,0], ![1,2,2,1]),
  (![1,1,2,2], ![1,2,2,2]),
  (![1,2,2,1], ![1,2,2,2]),
  (![1,2,2,1], ![1,2,3,1]),
  (![1,2,2,2], ![1,2,3,2]),
  (![1,2,3,1], ![1,2,3,2]),
  (![1,2,3,2], ![1,2,4,2]),
  (![1,2,4,2], ![1,3,4,2]),
  (![1,3,4,2], ![2,3,4,2])
] : List (Coeff × Coeff)).toFinset

theorem cover_enumeration : covers = enumeratedCovers := by decide

def omitted : Coeff × Coeff := (![0,1,1,0], ![0,1,2,0])

/-- The 1990 figure selects all covers except this single incoming edge.
This definition records the printed selection, not a new root relation. -/
def selected1990 : Finset (Coeff × Coeff) := covers \ {omitted}

theorem positive_distinct : positive.card = 24 := by decide
theorem standard_card : standard.card = 48 := by decide
theorem standard_correspondence : fullFromPositive = standard := by decide
theorem positive_images_distinct : (positive.image transform).card = 24 := by decide
theorem positive_negative_disjoint :
    Disjoint (positive.image transform) ((positive.image transform).image negate) := by decide
theorem full_cover_card : covers.card = 34 := by decide
theorem omitted_is_cover : omitted ∈ covers := by decide
theorem omitted_simple_difference :
    simpleStep omitted.1 omitted.2 ∧
    (∀ j : Fin 4, omitted.2 j = omitted.1 j + if j = 2 then 1 else 0) := by decide
theorem selected_card : selected1990.card = 33 := by decide
theorem unique_missing : covers \ selected1990 = {omitted} := by decide
theorem selected_not_full : selected1990 ≠ covers := by decide

/-- For the missing cover, the backward root string has length one.
The Chevalley absolute coefficient is consequently p+1=2. This is a
finite root-string certificate, not a formalization of the bracket theorem. -/
theorem omitted_root_string :
    (![0,0,2,-2] : Vector) ∈ standard ∧
    (![0,0,2,-4] : Vector) ∉ standard ∧ (1 + 1 : ℕ) = 2 := by decide


/-- All standard roots on the nonpositive backward alpha3 string. -/
theorem backward_string_complete :
    standard.filter (fun v => v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 2 ∧ v 3 ≤ 0) =
      {(![0,0,2,0] : Vector), (![0,0,2,-2] : Vector)} := by decide

theorem omitted_vector_identification :
    transform omitted.1 = (![0,0,2,0] : Vector) ∧
    transform omitted.2 = (![0,0,2,2] : Vector) := by decide

#print axioms cover_enumeration
#print axioms hasse_equals_simple_steps
#print axioms hasse_card
#print axioms backward_string_complete
#print axioms omitted_vector_identification
#print axioms positive_distinct
#print axioms standard_card
#print axioms standard_correspondence
#print axioms positive_images_distinct
#print axioms positive_negative_disjoint
#print axioms full_cover_card
#print axioms omitted_is_cover
#print axioms omitted_simple_difference
#print axioms selected_card
#print axioms unique_missing
#print axioms selected_not_full
#print axioms omitted_root_string

end Levchuk1990SmallF4Diagram
