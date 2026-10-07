#import "@preview/cetz:0.5.2": canvas, draw

#let positive-roots = (
  ((1, 0, 0, 0), $q_32$),
  ((0, 1, 0, 0), $q_21 = p_(1,-1)$),
  ((0, 0, 1, 0), $q_10 = p_21$),
  ((0, 0, 0, 1), $p_32$),
  ((1, 1, 0, 0), $q_31$),
  ((0, 1, 1, 0), $q_20 = p_(2,-1)$),
  ((0, 0, 1, 1), $p_31$),
  ((1, 1, 1, 0), $p_43 = q_30$),
  ((0, 1, 2, 0), $q_(2,-1) = p_(2,-2)$),
  ((0, 1, 1, 1), $p_(3,-1)$),
  ((1, 1, 2, 0), $q_(3,-1)$),
  ((1, 1, 1, 1), $p_42$),
  ((0, 1, 2, 1), $p_(3,-2)$),
  ((1, 2, 2, 0), $q_(3,-2)$),
  ((1, 1, 2, 1), $p_41$),
  ((0, 1, 2, 2), $p_(3,-3) = q_43$),
  ((1, 2, 2, 1), $p_(4,-1)$),
  ((1, 1, 2, 2), $q_42$),
  ((1, 2, 3, 1), $p_(4,-2)$),
  ((1, 2, 2, 2), $q_41$),
  ((1, 2, 3, 2), $p_(4,-3) = q_40$),
  ((1, 2, 4, 2), $q_(4,-1)$),
  ((1, 3, 4, 2), $q_(4,-2)$),
  ((2, 3, 4, 2), $q_(4,-3) = p_(4,-4)$),
)

#let height(coefficients) = coefficients.sum()
#let projection(coefficients) = {
  coefficients.zip((-3, -1, 1, 3)).map(pair => pair.at(0) * pair.at(1)).sum()
}
#let follows(a, b) = {
  let difference = b.zip(a).map(pair => pair.at(0) - pair.at(1))
  // The diagram selects 33 of the 34 root-poset covers. The excluded
  // pair is q₂₀ = p₂,₋₁ -> q₂,₋₁ = p₂,₋₂, with coefficients 0110 -> 0120.
  // This records the printed selection, not the completed rendering below.
  // The renderer adds the remaining cover, also shown by the authors in
  // 2012; all three covers incident to 0120 are dashed.
  (
    difference.all(value => value >= 0)
      and difference.sum() == 1
      and (a, b) != ((0, 1, 1, 0), (0, 1, 2, 0))
  )
}


#let covers(a, b) = {
  let d = b.zip(a).map(p => p.at(0) - p.at(1))
  d.all(v => v >= 0) and d.sum() == 1
}
// Barycentric layers; a single-parent branch continues outward.
// Expand compressed layers uniformly to maintain one unit separation.
#let root-layout() = {
  let positions = (:)
  for degree in range(1, 12) {
    let level = positive-roots
      .filter(r => height(r.at(0)) == degree)
      .sorted(key: r => projection(r.at(0)))
    let xs = level
      .enumerate()
      .map(((rank, r)) => {
        if degree == 1 { return 2 * rank - 3 }
        let parents = positive-roots.filter(p => covers(p.at(0), r.at(0)))
        let x = (
          parents.map(p => positions.at(p.at(0).map(str).join())).sum()
            / parents.len()
        )
        if parents.len() == 1 {
          let children = positive-roots.filter(c => covers(
            parents.first().at(0),
            c.at(0),
          ))
          if children.len() > 1 {
            x += (if x < 0 { -1 } else if x > 0 { 1 } else { 0 })
          }
        }
        x
      })
    if xs.len() > 1 {
      let gaps = range(1, xs.len()).map(i => xs.at(i) - xs.at(i - 1))
      if calc.min(..gaps) < 1 {
        let center = xs.sum() / xs.len()
        xs = range(xs.len()).map(i => center + i - (xs.len() - 1) / 2)
      }
    }
    for (r, x) in level.zip(xs) { positions.insert(r.at(0).map(str).join(), x) }
  }
  positions
}
// Both renderings use the authors’ 2012 auxiliary coefficient labels.
// Both renderings draw the complete 34-cover positive-root poset.
#let root-canvas(legend: false) = canvas(length: 1mm, {
  import draw: *
  let positions = root-layout()
  let step = 18
  let horizontal-step = 20
  set-style(stroke: 0.5pt, content: (
    padding: 0.8,
    wrap: text.with(size: 10.5pt, top-edge: "bounds", bottom-edge: "bounds"),
  ))
  for (i, r) in positive-roots.enumerate() {
    let degree = height(r.at(0))
    let x = positions.at(r.at(0).map(str).join())
    let name = "root-" + str(i)
    let stacked = r.at(0) == (1, 1, 1, 1)
    let label = if stacked {
      align(center, {
        set par(leading: 0pt)
        [#r.at(1) \
          #text(size: 8.5pt)[(#r.at(0).map(str).join())]]
      })
    } else { r.at(1) }
    content((horizontal-step * x, -step * (degree - 1)), label, name: name)
    let has-coeff = (
      degree > 2 and r.at(0) != (0, 1, 2, 0)
        or r.at(0) in ((1, 1, 0, 0), (0, 0, 1, 1))
    )
    if has-coeff and not stacked {
      let level = positive-roots
        .filter(s => height(s.at(0)) == degree)
        .sorted(key: s => projection(s.at(0)))
      let rank = level.position(s => s.at(0) == r.at(0))
      let left = rank == 0 and level.len() > 1
      content(
        name
          + if left {
            ".west"
          } else { ".east" },
        text(size: 8.5pt)[(#r.at(0).map(str).join())],
        anchor: if left {
          "east"
        } else { "west" },
        name: "coeff-" + str(i),
      )
    }
  }
  for (i, a) in positive-roots.enumerate() {
    for (j, b) in positive-roots.enumerate() {
      if (
        covers(a.at(0), b.at(0))
      ) {
        line(
          "root-" + str(i) + ".south",
          "root-" + str(j) + ".north",
          stroke: if a.at(0) == (0, 1, 2, 0)
            or a.at(0) == (0, 1, 1, 0) and b.at(0) == (0, 1, 2, 0) {
            (dash: "dashed", thickness: 0.5pt)
          } else { 0.5pt },
        )
      }
    }
  }
  if legend {
    // Anchor above and beside the rightmost coefficient
    // in the last two-vertex lower layer.
    let layer = positive-roots
      .filter(r => height(r.at(0)) == 7)
      .sorted(key: r => positions.at(r.at(0).map(str).join()))
    let root = layer.last()
    let index = positive-roots.position(r => r.at(0) == root.at(0))
    content(
      (rel: (14, step / 3), to: "coeff-" + str(index) + ".east"),
      align(center)[
        $overline(p)_(i j) = q_(i j), quad overline(q)_(i j) = p_(i j)$ \
        $(1 <= |j| < i <= 4)$
      ],
      anchor: "west",
    )
  }
})

#let f4-roots() = root-canvas(legend: true)
