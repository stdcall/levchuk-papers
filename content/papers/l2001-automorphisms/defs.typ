#import "../../main-defs.typ": *
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
#let example(body) = common.theorem-like("Example", "exm", none, true, body)
#let remark(body) = common.theorem-like("Remark", "rem", none, true, body)
#let proof(body) = common.proof(body, head: [Proof.], qed: true)
#let Aut = math.op("Aut")
#let Ann = math.op("Ann")
#let End = math.op("End")
#let Ker = math.op("Ker")
#let NT = math.upright("NT")
#let UT = math.upright("UT")
#let GL = math.upright("GL")
#let diag = math.op("diag")
#let B = math.cal("B")
#let D = math.cal("D")
#let F = math.cal("F")
#let A = math.cal("A")
#let M = math.cal("M")
