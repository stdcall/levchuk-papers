#import "../../statements.typ" as common
#let ht = math.op("ht")
#let ker = math.op("ker")
#let rank = math.op("rank")
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
