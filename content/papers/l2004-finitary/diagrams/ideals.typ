#import "@preview/cetz:0.5.2": canvas, draw
#import "@preview/fletcher:0.5.8": diagram, edge, node
#import "../defs.typ": NT

// Nested initial segments partition both axes into three consecutive blocks.
#let ideal-segments() = canvas(length: 13mm, {
  import draw: *
  let cuts = (0, 1, 2, 3)
  let labels = ($N_V$, $N_T$, $N_L$)
  for (i, body) in labels.enumerate() {
    let cut = cuts.at(i + 1)
    line((0, 4 - cut), (cut, 4 - cut), (cut, 0), stroke: 0.7pt)
    content((cut - 0.48, 4 - cut - 0.3), body)
  }
  content((2.6, 2.6), $0$)
  hobby((-0.3, 3.4), (-0.55, 1.7), (-0.3, 0), stroke: 0.7pt)
  hobby((3.3, 3.4), (3.55, 1.7), (3.3, 0), stroke: 0.7pt)
  // The intersection of the last row block with the first column block.
  for i in range(1, 9) {
    let t = i / 8
    line((0, t), (t, 0), stroke: 0.4pt)
    if i < 8 { line((t, 1), (1, t), stroke: 0.4pt) }
  }
  content((-0.85, 0.5), $overline(L)$, anchor: "east")
  content((0.5, -0.3), $V$)
})
#let isomorphism-square() = diagram(
  spacing: (15mm, 13mm),
  node((0, 0), $G(R)$),
  node((1, 0), $G(R)$),
  node((2, 0), $G(R)$),
  node((0, 1), $G(R_S)$),
  node((1, 1), $G[NT(Omega_1, S_1)]$),
  node((2, 1), $G[NT(Gamma, S_1)]$),
  edge((0, 0), (1, 0), $chi$, "->"),
  edge((1, 0), (2, 0), $lambda$, "->"),
  edge((0, 0), (0, 1), $psi$, "->"),
  edge((2, 0), (2, 1), $theta$, "->"),
  edge((1, 1), (0, 1), $tau$, "->"),
  edge((2, 1), (1, 1), $sigma$, "->"),
)
