#import "../../statements.typ" as common
#let proposition(body) = common.theorem-like(
  "Предложение",
  "prop",
  none,
  true,
  body,
)
#let definition(body) = common.theorem-like(
  "Определение",
  "def",
  none,
  false,
  body,
)
#let proof(body) = common.proof(body, qed: true)
#let Lc = math.cal("L")
#let ht = math.op("ht")
#let sl = math.op("sl")
#let M = math.upright("M")
