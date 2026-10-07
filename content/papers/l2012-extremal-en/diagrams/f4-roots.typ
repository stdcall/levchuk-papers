#import "@preview/cetz:0.5.2": canvas, draw
#import "../../l1990-small/diagrams/b-f4-roots.typ": (
  height, positive-roots, projection,
)
// The complete F4 positive-root poset; coordinates come from height and
// order within each height, not from positions measured on the source image.
#let f4-roots() = canvas(length: 1mm, {
  import draw: *
  let covers(a, b) = {
    let d = b.zip(a).map(p => p.at(0) - p.at(1))
    d.all(v => v >= 0) and d.sum() == 1
  }
  assert(positive-roots.len() == 24)
  assert(
    positive-roots
      .map(a => positive-roots.filter(b => covers(a.at(0), b.at(0))).len())
      .sum()
      == 34,
  )
  let dx = 32
  let dy = 14
  set-style(stroke: 0.5pt, content: (
    padding: 1.2,
    wrap: text.with(top-edge: "bounds", bottom-edge: "bounds"),
  ))
  for (i, r) in positive-roots.enumerate() {
    let degree = height(r.at(0))
    let level = positive-roots
      .filter(s => height(s.at(0)) == degree)
      .sorted(key: s => projection(s.at(0)))
    let rank = level.position(s => s.at(0) == r.at(0))
    let name = "root-" + str(i)
    content(
      (dx * (rank - (level.len() - 1) / 2), -dy * (degree - 1)),
      r.at(1),
      name: name,
    )
    if degree > 2 {
      let left = rank == 0 and level.len() > 1
      content(
        name + if left { ".west" } else { ".east" },
        text(size: 9pt)[(#r.at(0).map(str).join())],
        anchor: if left { "east" } else { "west" },
      )
    }
  }
  for (i, a) in positive-roots.enumerate() {
    for (j, b) in positive-roots.enumerate() {
      if covers(a.at(0), b.at(0)) {
        line(
          "root-" + str(i) + ".south",
          "root-" + str(j) + ".north",
          stroke: if a.at(0) == (0, 1, 1, 0) and b.at(0) == (0, 1, 2, 0) {
            (dash: "dashed", thickness: 0.5pt)
          } else { 0.5pt },
        )
      }
    }
  }
})
