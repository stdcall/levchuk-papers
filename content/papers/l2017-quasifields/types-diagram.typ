#import "@preview/cetz:0.5.2": canvas, draw

// The lattice's edges determine its levels and left/central/right branches.
#let structures = (
  skew: (point: (0, 4), body: [Skewfields\ Desarguesian planes]),
  semi: (point: (0, 2), body: [Semifields\ Semifield planes]),
  left-near: (point: (-2.7, 2), body: [Left nearfields\ Dual nearfield planes]),
  near: (point: (2.7, 2), body: [Nearfields\ Nearfield planes]),
  left-quasi: (
    point: (-1.35, 0.7),
    body: [Left quasifields\ Dual translation planes],
  ),
  quasi: (point: (1.35, 0.7), body: [Quasifields\ Translation planes]),
)
#let edges = (
  ("skew", "semi"),
  ("skew", "left-near"),
  ("skew", "near"),
  ("semi", "left-quasi"),
  ("semi", "quasi"),
  ("left-near", "left-quasi"),
  ("near", "quasi"),
)
#let translation-types() = canvas({
  import draw: *
  for (a, b) in edges {
    line(structures.at(a).point, structures.at(b).point, stroke: 0.4pt)
  }
  for (name, node) in structures {
    circle(node.point, radius: 0.035, fill: black, stroke: none)
    let anchor = if name in ("skew", "semi") { "south" } else if (
      name in ("left-near", "left-quasi")
    ) { "north-east" } else { "north-west" }
    content(
      node.point,
      box(fill: white, inset: 1pt, node.body),
      anchor: anchor,
      padding: 4pt,
    )
  }
  content((-4, 4), [Fields\ Pappian planes], anchor: "south")
  content((4.2, 4), [Alternative semifields\ Moufang planes], anchor: "south")
  content((-2, 4.25), [$arrow.l.r.double$])
  content((2, 4.25), [$arrow.l.r.double$])
  content((-2.3, 6.4), [Dickson–Wedderburn])
  content((2.6, 6.4), [Artin–Zorn])
  line((-2.3, 6.1), (-2, 5.1), stroke: 0.4pt)
  line((2.6, 6.1), (2, 5.1), stroke: 0.4pt)
})
