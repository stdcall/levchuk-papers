#import "@preview/cetz:0.5.2"
// Matrix position (i,j) embeds at (n+j,n - i), |j|<=i.
#let stepline = cetz.canvas(length: 5mm, {
  import cetz.draw: *
  let n = 10
  let corners = ((3, -1), (5, 1), (9, 6))
  let point(i, j) = (n + j, n - i)
  assert(corners.all(c => calc.abs(c.last()) <= c.first() and c.first() <= n))
  for k in range(corners.len() - 1) {
    assert(corners.at(k).first() < corners.at(k + 1).first())
    assert(corners.at(k).last() < corners.at(k + 1).last())
  }
  set-style(stroke: 0.5pt, content: (
    padding: 0.5,
    wrap: text.with(top-edge: "bounds", bottom-edge: "bounds"),
  ))
  let gap = 0.4
  // The omitted apex is cut at y=n-gap; both sloping sides retain the
  // defining equations x=y and x+y=2n of the matrix-position triangle.
  line(point(n, -n), (n - gap, n - gap), (n - gap / 3, n - gap))
  line(
    (n + gap / 3, n - gap),
    (n + gap, n - gap),
    point(n, n),
  )
  let first = point(..corners.first())
  let second = point(..corners.at(1))
  let last = point(..corners.last())
  line(
    (first.at(1), first.at(1)),
    first,
    (first.at(0), second.at(1)),
    second,
    (second.at(0), second.at(1) - 1),
  )
  let tail = corners.last().last() - corners.at(1).last()
  line((last.at(0) - tail / 3, last.at(1)), last, (last.at(0), 0))
  content((second, 50%, last), $dots dots$, anchor: "south")
  content((last.at(0) - tail / 6, last.at(1)), $L$, anchor: "south")
  content((n + first.at(1) / 2, first.at(1)), $0$)
  for (c, ilabel, jlabel) in (
    (corners.first(), $i_1$, $j_1$),
    (corners.at(1), $i_2$, $j_2$),
    (corners.last(), $i_m$, $j_m$),
  ) {
    let p = point(..c)
    content((p.at(1), p.at(1)), ilabel, anchor: "south-east")
    content((p.at(0), 0), jlabel, anchor: "north")
  }
})
