#import "../../main-defs.typ": *
#import "../../statements.typ" as common
#import "../../statements.typ": counted
#let theorem(body) = common.theorem-like("Theorem", "th", none, true, body)
#let lemma(body) = common.theorem-like("Lemma", "lem", none, true, body)
#let definition(body) = common.theorem-like(
  "Definition",
  "def",
  none,
  true,
  body,
)
#let proposition(body) = common.theorem-like(
  "Proposition",
  "prop",
  none,
  true,
  body,
)
#let example(body) = common.theorem-like("Example", "exm", none, true, body)
#let proof(body, head: [Proof.]) = common.proof(body, head: head, qed: true)
#let NT = math.upright("NT")
#let M = math.upright("M")
#let GL = math.upright("GL")
#let SL = math.upright("SL")
#let OmG = $Omega_G$
#let OmL = $Omega_L$
#let Lc = math.cal("L")
