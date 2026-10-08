#import "../../main-defs.typ": *
#import "../../statements.typ": *
#import "../../statements.typ" as common
#let theorem(body, numbered: true) = common.theorem-like(
  "Theorem",
  "th",
  none,
  numbered,
  body,
)
#let lemma(body) = common.theorem-like("Lemma", "lem", none, true, body)
#let corollary(body) = common.theorem-like("Corollary", "cor", none, true, body)
#let remark(body) = common.theorem-like("Remark", "rem", none, true, body)
#let example(body) = common.theorem-like("Example", "exm", none, true, body)
#let proof(body, head: [Proof.]) = common.proof(body, head: head, qed: true)
#let NT = math.upright("NT")
#let UT = math.upright("UT")
#let SL = math.upright("SL")
#let Aut = math.op("Aut")
#let End = math.op("End")
