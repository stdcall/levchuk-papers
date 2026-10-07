#import "../../statements.typ": theorem-like
#let theorem(body) = theorem-like("Theorem", "th", none, true, body)
#let lemma(body) = theorem-like("Lemma", "lem", none, true, body)
#let definition(body) = theorem-like("Definition", "def", none, true, body)
#let N = math.upright("N")
#let NT = math.op("NT")
