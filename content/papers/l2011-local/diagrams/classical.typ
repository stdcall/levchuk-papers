#import "@preview/cetz:0.5.2": canvas, draw
#import "../../../diagrams.typ": diagram-grid, root-line-baseline

#let dot(a, b) = a.zip(b).map(pair => pair.at(0) * pair.at(1)).sum()
#let simple-roots(kind, rank) = range(rank).map(i => range(rank).map(j => {
  if i == 0 {
    if kind == "D" { if j in (0, 1) { 1 } else { 0 } } else if j == 0 {
      if kind == "C" { 2 } else { 1 }
    } else { 0 }
  } else { if j == i { 1 } else if j == i - 1 { -1 } else { 0 } }
}))
#let classical(kind) = context canvas(
  length: 8mm,
  baseline: (0, root-line-baseline(8mm)),
  {
    import draw: *
    let rank = if kind == "D" { 7 } else { 5 }
    let roots = simple-roots(kind, rank)
    let positions = range(rank).map(i => if kind == "D" {
      if i < 2 { (0, if i == 0 { 0.35 } else { -0.35 }) } else {
        (1.3 * (i - 1), 0)
      }
    } else { (1.4 * i, 0) })
    for i in range(rank) {
      for j in range(i + 1, rank) {
        let inner = dot(roots.at(i), roots.at(j))
        if inner != 0 {
          let strands = if (
            4 * inner * inner
              == 2
                * dot(roots.at(i), roots.at(i))
                * dot(roots.at(j), roots.at(j))
          ) { 2 } else { 1 }
          for dy in if strands == 2 { (-0.035, 0.035) } else { (0,) } {
            let a = positions.at(i)
            let b = positions.at(j)
            line((a.at(0), a.at(1) + dy), (b.at(0), b.at(1) + dy), stroke: (
              thickness: 0.5pt,
              dash: if (kind == "D" and i == 4) or (kind != "D" and i == 2) {
                "dashed"
              } else { "solid" },
            ))
          }
        }
      }
    }
    for (i, position) in positions.enumerate() {
      circle(position, radius: 0.07, fill: white, stroke: 0.5pt)
      if kind in ("B", "C") {
        let squared = dot(roots.at(i), roots.at(i))
        content(
          (position.at(0), position.at(1) + 0.16),
          $#(squared / if kind == "C" { 2 } else { 1 })$,
          anchor: "south",
        )
      }
    }
  },
)
#let classical-diagrams() = diagram-grid((
  ($A_n:$, classical("A"), [($n$ вершин, $n>=1$)]),
  ($B_n:$, classical("B"), [($n$ вершин, $n>=2$)]),
  ($C_n:$, classical("C"), [($n$ вершин, $n>=2$)]),
  ($D_n:$, classical("D"), [($n$ вершин, $n>=4$)]),
))
