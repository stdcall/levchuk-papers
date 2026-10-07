#import "@preview/cetz:0.5.2": canvas, draw
#import "../../../diagrams.typ": diagram-grid, root-line-baseline

#let coxeter-name(kind) = if kind == "B" { $B_n:$ } else if kind == "C" {
  $C_n:$
} else { $G_2:$ }
#let coxeter-note(kind) = if kind == "B" { [$(n >= 3)$] } else if (
  kind == "C"
) { [$(n >= 2)$] } else { [] }
#let coxeter(kind, annotations: true) = context canvas(
  length: 8mm,
  baseline: (0, root-line-baseline(8mm)),
  {
    import draw: *
    let xs = if kind == "G" { (0, 1.5) } else { (0, 1.5, 3, 4.5, 7.5) }
    let labels = if kind == "B" { ($1$, $2$, $2$, $2$, $2$) } else if (
      kind == "C"
    ) {
      ($2$, $1$, $1$, $1$, $1$)
    } else { ($1$, $3$) }
    if annotations {
      content(
        (-0.45, 0),
        coxeter-name(kind),
        anchor: "east",
      )
    }
    for i in range(xs.len() - 1) {
      let ys = if kind == "G" { (-0.06, 0, 0.06) } else if i == 0 {
        (-0.035, 0.035)
      } else { (0,) }
      for y in ys {
        line((xs.at(i) + 0.07, y), (xs.at(i + 1) - 0.07, y), stroke: (
          thickness: 0.5pt,
          dash: if i == 3 { "dashed" } else { "solid" },
        ))
      }
    }
    for (i, x) in xs.enumerate() {
      circle((x, 0), radius: 0.07, fill: white, stroke: 0.5pt)
      content((x, 0.16), labels.at(i), anchor: "south")
    }
    if kind != "G" and annotations {
      content(
        (xs.last() + 0.4, 0),
        coxeter-note(kind),
        anchor: "west",
      )
    }
  },
)

#let coxeter-rows(kinds) = diagram-grid(kinds.map(kind => (
  coxeter-name(kind),
  coxeter(kind, annotations: false),
  coxeter-note(kind),
)))
