#import "@preview/cetz:0.5.2"
#let vertices(start, steps) = {
  let result = (start,)
  for s in steps {
    let p = result.last()
    result.push((p.at(0) + s.at(0), p.at(1) + s.at(1)))
  }
  result
}
#let label-style() = cetz.draw.set-style(stroke: 0.5pt, content: (
  padding: 0.6,
  wrap: text.with(top-edge: "bounds", bottom-edge: "bounds"),
))
#let c-coordinates = cetz.canvas(length: 8mm, {
  import cetz.draw: *
  label-style()
  let n = 5
  let i = 2
  let A = (-i + 1, n - i)
  let C = (n, 0)
  let D = (0, n)
  let path = vertices(A, (
    (0, -1),
    (1, 0),
    (0, -1),
    (1, 0),
    (1, 0),
    (1, 0),
    (0, -1),
    (1, 0),
    (1, 0),
  ))
  assert(path.last() == C)
  assert(path.all(p => p.at(0) + p.at(1) <= n and p.at(1) >= 0))
  let X = (-1, n + 1)
  let Y = (n - 2, -2)
  line((-n, 0), (n + 1, 0), mark: (end: ">"))
  line((0, -1), (0, n + 1), mark: (end: ">"))
  line((-n, 0), D)
  line(C, X, stroke: (dash: "dashed"), mark: (end: ">"))
  line(C, Y, stroke: (dash: "dashed"), mark: (end: ">"))
  line(..path)
  content(D, $D(0,n)$, anchor: "west")
  content(C, $C(n,0)$, anchor: "north-west")
  content(C, $O$, anchor: "south")
  content((0, 0), $0$, anchor: "north-west")
  content((n + 1, 0), $x$, anchor: "west")
  content((0, n + 1), $y$, anchor: "west")
  content(X, $X$, anchor: "south")
  content(Y, $Y$, anchor: "west")
  // Place the long coordinate label outside the triangular domain at the
  // intersection of its row with the left boundary; bounds-based padding
  // keeps the text clear of that boundary.
  content((A.at(1) - n, A.at(1)), $A_i lr((-i+1,n - i))$, anchor: "east")
})
#let b-coordinates = cetz.canvas(length: 7mm, {
  import cetz.draw: *
  label-style()
  let n = 7
  let i = 3
  let t = 5
  let m = 3
  // Original axes point upward (x) and leftward (y).
  let point(x, y) = (-y, x)
  let O = point(n, n)
  let T = point(t, -1)
  let I = point(i, -i)
  let M = point(m, 1)
  let first = vertices(T, ((1, 0), (0, -1), (1, 0), (0, -1)))
  let second = vertices(O, (
    (1, 0),
    (0, -1),
    (1, 0),
    (0, -1),
    (1, 0),
    (0, -1),
    (1, 0),
    (0, -1),
    (1, 0),
    (1, 0),
  ))
  assert(first.last() == I and second.last() == M)
  assert(first.all(p => p.at(1) >= p.at(0)))
  assert(second.all(p => p.at(1) >= calc.abs(p.at(0))))
  line((-n - 1, 0), (n, 0))
  line((0, -2), (0, n + 1), mark: (end: ">"))
  line((0, 0), (-n - 1, 0), mark: (end: ">"))
  line(O, point(n, -n), (0, 0), (-2, -2))
  line(..first)
  line(..second)
  let X = (2, -2)
  let Y = (O.at(0) + 2, O.at(1) + 2)
  line(O, X, stroke: (dash: "dashed"), mark: (end: ">"))
  line(
    (O.at(0) - 2, O.at(1) - 2),
    Y,
    stroke: (dash: "dashed"),
    mark: (end: ">"),
  )
  content(O, $(n,n)$, anchor: "south-east")
  content(O, $O$, anchor: "north")
  content(T, $(t,-1)$, anchor: "south")
  content(I, $(i,-i)$, anchor: "west")
  content(M, $(m,1)$, anchor: "north")
  content((0, 0), $0$, anchor: "north-east")
  content((-n - 1, 0), $y$, anchor: "north")
  content((0, n + 1), $x$, anchor: "west")
  content(X, $X$, anchor: "west")
  content(Y, $Y$, anchor: "south")
})
