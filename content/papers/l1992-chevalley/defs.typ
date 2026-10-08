#import "../../statements.typ" as common
#let theorem(body) = common.theorem-like("Theorem", "th", none, true, body)
#let proposition(body) = common.theorem-like(
  "Proposition",
  "prop",
  none,
  true,
  body,
)
#let example(body) = common.theorem-like(
  "Example",
  "exm",
  none,
  true,
  body,
)
#let Z = math.bb("Z")
#let ht = math.op("ht")
#let Hom = math.op("Hom")
#let Ker = math.op("Ker")
#let GF = math.op("GF")
#let aut = math.op("aut")
#let NB = math.upright("NB")
#let ND = math.upright("ND")
#let NG = math.upright("NG")
#let UG = math.upright("UG")
