#import "../../statements.typ" as common
#let Lc = math.cal($L$)
#let res = math.op("res")
#let theorem(title: none, numbered: true, body) = common.theorem-like(
  "Theorem",
  "th",
  title,
  numbered,
  body,
)
#let main-theorem(body) = common.theorem-like(
  "Main Theorem",
  "th",
  none,
  false,
  body,
)
#let lemma(title: none, numbered: true, body) = common.theorem-like(
  "Lemma",
  "lem",
  title,
  numbered,
  body,
)
#let definition(title: none, body) = common.theorem-like(
  "Definition",
  "def",
  title,
  true,
  body,
)
#let example(body) = common.theorem-like("Example", "exm", none, true, body)
#let remark(body) = common.theorem-like("Remark", "rem", none, true, body)
#let proof(body, qed: true) = common.proof(
  body,
  head: [Proof.],
  qed: qed,
)
#let figure-caption() = common.counted("fig", n => [Fig. #n.])

#let question(name) = body => common.theorem-like(
  "Question " + name,
  "pr",
  none,
  false,
  body,
)
