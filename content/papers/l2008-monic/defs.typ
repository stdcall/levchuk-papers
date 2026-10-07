#import "../../statements.typ" as common
#let theorem(body) = common.theorem-like("Theorem", "th", none, true, body)
#let lemma(body) = common.theorem-like("Lemma", "lem", none, true, body)
#let proposition(body) = common.theorem-like(
  "Proposition",
  "prop",
  none,
  true,
  body,
)
#let corollary(body) = common.theorem-like("Corollary", "cor", none, true, body)
#let example(body) = common.theorem-like("Example", "exm", none, false, body)
#let proof(body) = common.proof(body, head: [Proof.], qed: true)
#let algorithm(body) = common.theorem-like("Algorithm", "rem", none, true, body)
#let hypothesis(body) = common.theorem-like(
  "Hypothesis",
  "hyp",
  none,
  false,
  body,
)
#let Aut = math.op("Aut")
#let TAut = math.op("TAut")
#let NT = math.op("NT")
#let UT = math.op("UT")
#let GL = math.op("GL")
#let diag = math.op("diag")
