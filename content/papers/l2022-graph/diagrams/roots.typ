#import "@preview/cetz:0.5.2": canvas, draw
#import "../../../diagrams.typ": diagram-grid, root-line-baseline

#let bc-one() = canvas(length: 15mm, {
  import draw: *
  set-style(line: (stroke: 0.6pt, mark: (end: "stealth", fill: black)))
  let roots = (-2, -1, 1, 2)
  for r in roots {
    let s = if calc.abs(r) == 1 { 0 } else { r / 2 }
    line((s, 0), (r, 0))
    content(
      (r, -0.15),
      if r == -2 { $-2a$ } else if r == -1 { $-a$ } else if r == 1 {
        $a$
      } else { $2a$ },
      anchor: "north",
    )
  }
  circle((0, 0), radius: 0.025, fill: black)
  content((0, -0.15), $0$, anchor: "north")
})

// Bonds and root lengths define the graphs. A dashed path segment denotes
// the continuation of a classical series; exceptional graphs are complete.
#let coxeter-name(kind) = if kind == "E" { $E_6:$ } else if kind == "F" {
  $F_4:$
} else if kind == "G" { $G_2:$ } else if kind == "A" { $A_n:$ } else if (
  kind == "D"
) { $D_n:$ } else if kind == "B" { $B_n:$ } else { $C_n:$ }
#let coxeter-note(kind) = if kind == "A" { [$(n "nodes", n >= 1)$] } else if (
  kind == "D"
) { [$(n "nodes", n >= 4)$] } else if kind in ("B", "C") {
  [$(n >= 2)$]
} else { [] }
#let coxeter(kind, annotations: true) = context canvas(
  length: 9mm,
  baseline: (0, root-line-baseline(9mm)),
  {
    import draw: *
    let classical = kind in ("A", "B", "C", "D")
    let count = if kind == "G" { 2 } else if kind == "F" { 4 } else { 5 }
    let vertices = range(count).map(i => (1.35 * i, 0))
    let edges = range(count - 1).map(i => (
      i,
      i + 1,
      if kind in ("B", "C") and i == 0 or kind == "F" and i == 1 {
        2
      } else if kind == "G" { 3 } else { 1 },
    ))
    if kind == "E" {
      vertices.push((1.35 * 2, -0.8))
      edges.push((2, count, 1))
    } else if kind == "D" {
      vertices.push((-1.35, 0.5))
      vertices.push((-1.35, -0.5))
      edges.push((count, 0, 1))
      edges.push((count + 1, 0, 1))
    }
    let lengths = if kind == "B" { (1, 2, 2, 2, 2) } else if kind == "C" {
      (2, 1, 1, 1, 1)
    } else if kind == "F" { (2, 2, 1, 1) } else if kind == "G" { (1, 3) } else {
      ()
    }
    if annotations {
      content(
        (if kind == "D" { -1.9 } else { -0.55 }, 0),
        coxeter-name(kind),
        anchor: "east",
      )
    }
    for (a, b, m) in edges {
      for j in range(m) {
        let offset = (j - (m - 1) / 2) * 0.07
        let u = vertices.at(a)
        let v = vertices.at(b)
        line((u.at(0), u.at(1) + offset), (v.at(0), v.at(1) + offset), stroke: (
          thickness: 0.7pt,
          dash: if classical and a == 2 and b == 3 { "dashed" } else {
            "solid"
          },
        ))
      }
    }
    for (i, v) in vertices.enumerate() {
      circle(v, radius: 0.065, fill: white, stroke: 0.5pt)
      if lengths.len() > 0 {
        content(
          (v.at(0), v.at(1) + 0.17),
          $#{ lengths.at(i) }$,
          anchor: "south",
        )
      }
    }
    if classical and annotations {
      content(
        (vertices.at(count - 1).at(0) + 0.4, 0),
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
