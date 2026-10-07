#import "../../main-defs.typ": *
#import "../../statements.typ": *

#let NT = math.op("NT")
#let UT = math.op("UT")
#let GL = math.op("GL")
#let Lc = math.cal("L")
#let definition(body) = theorem-like("Определение", "def", none, true, body)
#let letter-list(..items) = enum(
  numbering: n => "(" + ("а", "б", "в", "г", "д").at(n - 1) + ")",
  ..items.pos(),
)
