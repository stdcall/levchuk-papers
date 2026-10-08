#import "@preview/cetz:0.5.2": canvas, draw
#import "../../diagrams.typ": diagram-grid, root-line-baseline

// Displayed vertices are the endpoints of the classical chains; a dashed
// edge denotes their omitted interior. Branch adjacency defines type D.
#let classical-chain(kind) = context canvas(
  length: 8mm,
  baseline: (0, root-line-baseline(8mm)),
  {
    import draw: *
    let vertices = if kind == "A" {
      ((0, 0), (1.5, 0), (3, 0), (4.8, 0), (6.3, 0))
    } else {
      ((0, 0.3), (0, -0.3), (1.5, 0), (3, 0), (4.5, 0), (6.3, 0), (7.8, 0))
    }
    let edges = if kind == "A" {
      ((0, 1), (1, 2), (2, 3), (3, 4))
    } else { ((0, 2), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6)) }
    let omitted = if kind == "A" { (2, 3) } else { (4, 5) }
    for edge in edges {
      line(vertices.at(edge.first()), vertices.at(edge.last()), stroke: (
        thickness: 0.5pt,
        dash: if edge == omitted { "dashed" } else { "solid" },
      ))
    }
    for vertex in vertices {
      circle(vertex, radius: 0.07, fill: white, stroke: 0.5pt)
    }
  },
)
#let coxeter-a() = diagram-grid((
  ($A_n:$, classical-chain("A"), [($n$ вершин).]),
))
#let coxeter-d() = diagram-grid((
  ($D_n:$, classical-chain("D"), [($n$ вершин).]),
))
