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
#let definition(body) = common.theorem-like(
  "Definition",
  "def",
  none,
  true,
  body,
)
#let example(body) = common.theorem-like("Example", "exm", none, true, body)
#let proof(body) = common.proof(body, head: [Proof.], qed: true)
#let sketch(body) = common.proof(body, head: [Sketch of proof.], qed: true)
#let gp = math.op("gp")
#let Z = math.bb("Z")
