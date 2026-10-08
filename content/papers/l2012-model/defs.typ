#import "../../main-defs.typ": *
#import "../../statements.typ": *
#import "../../statements.typ" as common
#let question(body) = common.theorem-like("Вопрос", "pr", none, true, body)
#let proof(body) = common.proof(body, qed: true)
#let NT = math.upright("NT")
#let UT = math.upright("UT")
#let Aut = math.op("Aut")
#let rad = math.op("rad")
#let SL = math.op("SL")
#let GL = math.op("GL")
#let N = math.upright("N")
