#import "../../statements.typ" as common
#let theorem(body) = common.theorem-like("Theorem", "th", none, true, body)
#let corollary(body) = common.theorem-like(
  "Corollary",
  "cor",
  none,
  true,
  body,
)
#let corners = math.cal("L")
#let frame = math.cal("F")
#let maximal = math.cal("M")
#let ker = math.op("ker")
