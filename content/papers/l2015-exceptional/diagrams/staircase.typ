#import "@preview/cetz:0.5.2": canvas, draw

// A representative chain of corners determines the staircase. The dotted
// middle segment denotes the continuation from the second to the last corner.
#let staircase() = canvas(length: 6mm, {
  import draw: *
  let corners = ((3, 1), (5, 3), (8, 6))
  let position(p) = (p.at(1), -p.at(0))
  assert(corners.all(p => p.at(0) > p.at(1)))
  let first = position(corners.first())
  line((0, first.at(1)), first)
  for (index, p) in corners.enumerate() {
    let start = position(p)
    if index + 1 < corners.len() {
      let next = position(corners.at(index + 1))
      if index == 1 {
        let gap = (next.at(1) - start.at(1)) / 3
        line(start, (start.at(0), start.at(1) + gap))
        content(
          ((start.at(0) + next.at(0)) / 2, (start.at(1) + next.at(1)) / 2),
          $dots.down$,
        )
        let stub = start.at(0) + (next.at(0) - start.at(0)) * 2 / 3
        line((stub, next.at(1) - gap), (stub, next.at(1)), next)
      } else { line(start, (start.at(0), next.at(1)), next) }
    } else { line(start, (start.at(0), -10)) }
    content(
      start,
      if index == 0 { $(i_1,j_1)$ } else if index == 1 { $(i_2,j_2)$ } else {
        $(i_m,j_m)$
      },
      anchor: "south-west",
    )
  }
  content((1, -0.5), $0$)
  content((9, -9.5), $0$)
  for k in (2, 4, 6) { content((k, -k + 0.5), $dots.down$) }
  bezier((0, 0), (0, -10), (-0.8, 0), (-0.8, -10))
  bezier((10, 0), (10, -10), (10.8, 0), (10.8, -10))
})
