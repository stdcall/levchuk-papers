#import "@preview/cetz:0.5.2": canvas, draw
#import "../../../diagrams.typ": diagram-grid, root-line-baseline
#let dynkin(kind) = context canvas(
  length: 8mm,
  baseline: (0, root-line-baseline(8mm)),
  {
    import draw: *
    // Five displayed vertices represent the classical chain; the fourth
    // interval is the omitted interior of the chain in the printed scheme.
    let ranks = (0, 1, 2, 3, 4)
    let xs = ranks.map(i => 1.5 * (i + if i == 4 { 1 } else { 0 }))
    let lengths = ranks.map(i => if kind == "B" {
      if i == 0 { 1 } else { 2 }
    } else { if i == 0 { 2 } else { 1 } })
    for i in range(ranks.len() - 1) {
      let offsets = if i == 0 { (-0.035, 0.035) } else { (0,) }
      for y in offsets {
        line((xs.at(i) + 0.07, y), (xs.at(i + 1) - 0.07, y), stroke: (
          thickness: 0.5pt,
          dash: if i == 3 { "dashed" } else { "solid" },
        ))
      }
    }
    for (i, x) in xs.enumerate() {
      circle((x, 0), radius: 0.07, fill: white, stroke: 0.5pt)
      content((x, 0.16), $ #lengths.at(i) $, anchor: "south")
    }
  },
)
#let dynkin-pair() = diagram-grid((
  ($B_n:$, dynkin("B"), []),
  ($C_n:$, dynkin("C"), []),
))
