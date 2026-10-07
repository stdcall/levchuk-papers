#import "../../main-defs.typ": *
#import "../../statements.typ": *
#import "../../statements.typ": proof as common-proof

#let NT = math.op("NT")
#let GF = math.op("GF")
#let theorem(title: none, numbered: true, body) = theorem-like(
  "Theorem",
  "th",
  title,
  numbered,
  body,
)
#let lemma(title: none, numbered: true, body) = theorem-like(
  "Lemma",
  "lem",
  title,
  numbered,
  body,
)
#let problem(body) = theorem-like("Problem", "pr", none, true, body)
#let proof(body) = common-proof(body, head: [Proof.])

#import "../../numbering.typ": family-counter, record
#let drawing(body) = block(width: 100%)[
  #family-counter("fig").step()
  #align(center, body)
  #align(center, context [Figure #family-counter("fig").display("1"). #record(
      "fig",
    )])
]
