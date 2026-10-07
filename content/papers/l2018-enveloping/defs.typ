#import "../../statements.typ": theorem-like
#let proposition(body) = theorem-like(
  "Предложение",
  "prop",
  none,
  true,
  body,
)
#let Zc = math.cal("Z")
#let Jc = math.cal("J")
#let Dc = math.cal("D")
#let Ah = math.hat("A")
#let St = math.tilde("S")
#let ht = math.op("ht")
#let dim = math.op("dim")
#let Ac = math.cal("A")
#let Lc = math.cal("L")
#let Fc = math.cal("F")
#let qbinom(n, k) = $lr([vec(#n, #k)])_q$
