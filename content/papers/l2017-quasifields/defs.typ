#import "../../statements.typ" as common
#let theorem(title: none, numbered: true, body) = common.theorem-like(
  "Theorem",
  "th",
  title,
  numbered,
  body,
)
#let lemma(title: none, numbered: true, body) = common.theorem-like(
  "Lemma",
  "lem",
  title,
  numbered,
  body,
)
#let corollary(title: none, numbered: true, body) = common.theorem-like(
  "Corollary",
  "cor",
  title,
  numbered,
  body,
)
#let proposition(title: none, numbered: true, body) = common.theorem-like(
  "Proposition",
  "prop",
  title,
  numbered,
  body,
)
#let definition(title: none, numbered: true, body) = common.theorem-like(
  "Definition",
  "def",
  title,
  numbered,
  body,
)
#let remark(title: none, numbered: true, body) = common.theorem-like(
  "Remark",
  "rem",
  title,
  numbered,
  body,
)
#let proof(body, head: [Proof.], qed: false) = common.proof(
  body,
  head: head,
  qed: qed,
)
#let Aut = math.op("Aut")
#let GL = math.op("GL")
#let GF = math.op("GF")
#let SL = math.op("SL")
#let Ker = math.op("Ker")
#let char = math.op("char")
#let Z = math.op("Z")
#let KRu = math.frak("R")
#let HRu = math.cal("H") + math.frak("R")
