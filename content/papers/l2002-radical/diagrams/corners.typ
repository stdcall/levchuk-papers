#import "../../../diagrams.typ": matrix-staircases
#import "../../../numbering.typ": record
#let corners-diagram = {
  align(center, matrix-staircases())
  context { record("fig", tag: "*") }
}
