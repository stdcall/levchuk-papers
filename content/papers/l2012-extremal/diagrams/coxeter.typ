#import "@preview/cetz:0.5.2": canvas, draw
#import "../../../diagrams.typ": diagram-grid, root-line-baseline

// The article numbers the branch of E_n by alpha_2 at alpha_4.
// B_n starts at the short simple root; C_n starts at the long one.
#let coxeter-name(kind) = if kind == "F" { $F_4:$ } else if kind == "E" {
  $E_n:$
} else if kind == "B" { $B_n:$ } else { $C_n:$ }
#let coxeter-note(kind) = if kind == "E" { [$(n = 6, 7, 8)$] } else if (
  kind == "F"
) { [] } else { [$(n >= 2)$] }
#let coxeter(kind, annotations: true) = context canvas(
  length: 8mm,
  baseline: (0, root-line-baseline(8mm)),
  {
    import draw: *
    let xs = if kind == "F" { (0, 1.5, 3, 4.5) } else { (0, 1.5, 3, 4.5, 7.5) }
    let labels = if kind == "E" {
      ($alpha_1$, $alpha_3$, $alpha_4$, $alpha_5$, $alpha_n$)
    } else if kind == "B" { ($1$, $2$, $2$, $2$, $2$) } else if kind == "C" {
      ($2$, $1$, $1$, $1$, $1$)
    } else { ($1$, $1$, $2$, $2$) }
    if annotations {
      content((-0.45, 0), coxeter-name(kind), anchor: "east")
    }
    for i in range(xs.len() - 1) {
      let a = xs.at(i)
      let b = xs.at(i + 1)
      let double = (kind in ("B", "C") and i == 0) or (kind == "F" and i == 1)
      let dashed = kind != "F" and i == 3
      for y in (if double { (-0.035, 0.035) } else { (0,) }) {
        line((a + 0.07, y), (b - 0.07, y), stroke: (
          thickness: 0.5pt,
          dash: if dashed { "dashed" } else { "solid" },
        ))
      }
    }
    if kind == "E" {
      line((3, -0.07), (3, -0.7), stroke: 0.5pt)
      circle((3, -0.77), radius: 0.07, fill: white, stroke: 0.5pt)
      content((3, -0.9), $alpha_2$, anchor: "north")
    }
    for (i, x) in xs.enumerate() {
      circle((x, 0), radius: 0.07, fill: white, stroke: 0.5pt)
      content((x, 0.16), labels.at(i), anchor: "south")
    }
    if annotations {
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
