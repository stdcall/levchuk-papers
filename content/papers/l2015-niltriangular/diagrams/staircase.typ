#import "@preview/cetz:0.5.2": canvas, draw

#let staircase() = canvas(length: 6mm, {
  import draw: *
  let n = 10
  let corners = ((3, 1), (5, 3), (9, 7))
  let position(p) = (p.at(1), -p.at(0))
  let first = position(corners.first())
  line((0.5, first.at(1)), first)
  for (index, p) in corners.enumerate() {
    assert(p.at(0) > p.at(1))
    let point = position(p)
    if index + 1 < corners.len() {
      let next = position(corners.at(index + 1))
      if index == 1 {
        let dx = (next.at(0) - point.at(0)) / 3
        let dy = (next.at(1) - point.at(1)) / 3
        line(
          point,
          (point.at(0), point.at(1) + dy),
          (point.at(0) + dx, point.at(1) + dy),
        )
        content(
          ((point.at(0) + next.at(0)) / 2, (point.at(1) + next.at(1)) / 2),
          $dots.down$,
        )
        line((next.at(0) - dx, next.at(1)), next)
      } else {
        line(point, (point.at(0), next.at(1)), next)
      }
    } else { line(point, (point.at(0), -n - 0.5)) }
    content(
      (point.at(0), point.at(1) + 0.15),
      if index == 0 { $(i_1,j_1)$ } else if index == 1 {
        $(i_2,j_2)$
      } else { $(i_m,j_m)$ },
      anchor: "south",
    )
  }
  for k in (1, 2, 9, 10) { content((k, -k), $0$) }
  for k in (3.5, 5, 6.5, 8) {
    content((k, -k), $dots.down$)
  }
  content((4, -6), $cal(L)$)
  content((8, -3.5), $0$)
  bezier((0, 0), (0, -11), (-0.8, 0), (-0.8, -11))
  bezier((11, 0), (11, -11), (11.8, 0), (11.8, -11))
})
