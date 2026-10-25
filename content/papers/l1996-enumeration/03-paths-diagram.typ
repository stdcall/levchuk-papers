#import "@preview/cetz:0.5.2"

#let paths-coordinates = cetz.canvas(length: 4.5mm, {
  import cetz.draw: *
  set-style(stroke: 0.5pt, content: (
    padding: 0.6,
    wrap: text.with(top-edge: "bounds", bottom-edge: "bounds"),
  ))
  let n = 8
  let i = 4
  let A = (-i + 1, i)
  let B = (n, 0)
  let C = (0, n)
  let first-column = n - i - 1
  let last-column = n - 2
  let path = (
    A,
    (-i + 1, i - 1),
    (first-column, i - 1),
    (first-column, 2),
    (last-column, 2),
    (last-column, 0),
  )
  assert(path.all(p => p.at(1) >= 0 and p.at(0) + p.at(1) <= n))
  line((0, 0), (n + 2, 0), mark: (end: ">"))
  line((0, 0), (-n - 2, 0), mark: (end: ">"))
  line((0, 0), (0, n + 2), mark: (end: ">"))
  line((-n, 0), C)
  line(..path)
  let X = (-1, n + 1)
  let Y = (-1, -n - 1)
  line(B, X, stroke: (dash: "dashed"), mark: (end: ">"))
  line(B, Y, stroke: (dash: "dashed"), mark: (end: ">"))
  content((A.at(1) - n, A.at(1)), $A_i lr((-i+1,i))$, anchor: "east")
  line((A.at(1) - n + 0.2, A.at(1)), A, stroke: 0.3pt)
  content(C, $C(0,n)$, anchor: "south-west")
  content(B, $B(n,0)$, anchor: "south-west")
  content(B, $O$, anchor: "north-west")
  content((0, 0), $o$, anchor: "north-west")
  content((n + 2, 0), $x$, anchor: "north")
  content((0, n + 2), $y$, anchor: "south")
  content(X, $X$, anchor: "east")
  content(Y, $Y$, anchor: "north")
})
