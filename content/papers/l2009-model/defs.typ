#import "../../main-defs.typ": ed-note, source
#import "../../statements.typ" as common
#let theorem(body) = common.theorem-like("Theorem", "th", none, true, body)
#let lemma(body) = common.theorem-like("Lemma", "lem", none, true, body)
#let remark(body) = common.theorem-like("Remark", "rem", none, false, body)
#let NT = math.op("NT")
#let UT = math.op("UT")
#let Der = math.op("Der")
#let Ann = math.op("Ann")
#let Th = math.op("Th")
#let Sop = math.op("op")
#let HC = math.cal("Z")
#let DD = math.cal("L")
