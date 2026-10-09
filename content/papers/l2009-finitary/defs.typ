#import "../../statements.typ" as common
#let theorem(body) = common.theorem-like("Теорема", "th", none, true, body)
#let lemma(body) = common.theorem-like("Лемма", "lem", none, true, body)
#let proposition(body) = common.theorem-like(
  "Предложение",
  "prop",
  none,
  true,
  body,
)
#let proof(body) = common.proof(body, head: [Доказательство.], qed: true)
#let Aut = math.op("Aut")
#let UT = math.op("UT")
#let NT = math.op("NT")
#let GL = math.op("GL")
#let SL = math.op("SL")
