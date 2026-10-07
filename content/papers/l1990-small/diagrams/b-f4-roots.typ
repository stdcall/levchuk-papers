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
  // Retaining that selection does not assert that the full poset lacks
  // this cover; dashed edges are the two outgoing covers of 0120.
  (
    difference.all(value => value >= 0)
      and difference.sum() == 1
      and (a, b) != ((0, 1, 1, 0), (0, 1, 2, 0))
  )
}

#let f4-roots() = canvas(length: 1mm, {
  import draw: *
  assert(positive-roots.len() == 24)
  let coefficients = positive-roots.map(root => root.at(0))
  assert(coefficients.dedup().len() == 24)
  assert(
    coefficients.map(a => coefficients.filter(b => follows(a, b)).len()).sum()
      == 33,
  )
  let horizontal-step = 32
  let vertical-step = 14
  set-style(
    stroke: 0.5pt,
    content: (
      padding: 1.2,
      wrap: text.with(top-edge: "bounds", bottom-edge: "bounds"),
    ),
  )
  for (index, root) in positive-roots.enumerate() {
    let degree = height(root.at(0))
    let level = positive-roots
      .filter(other => height(other.at(0)) == degree)
      .sorted(key: other => projection(other.at(0)))
    let rank = level.position(other => other.at(0) == root.at(0))
    let x = horizontal-step * (rank - (level.len() - 1) / 2)
    let y = -vertical-step * (degree - 1)
    let name = "root-" + str(index)
    content((x, y), root.at(1), name: name)
    if degree > 2 {
      let left-side = rank == 0 and level.len() > 1
      content(
        name + if left-side { ".west" } else { ".east" },
        text(size: 9pt)[(#root.at(0).map(str).join())],
        anchor: if left-side { "east" } else { "west" },
      )
    }
  }
  for (i, a) in positive-roots.enumerate() {
    for (j, b) in positive-roots.enumerate() {
      if follows(a.at(0), b.at(0)) {
        let stroke = if a.at(0) == (0, 1, 2, 0) {
          (dash: "dashed", thickness: 0.5pt)
        } else { 0.5pt }
        line(
          "root-" + str(i) + ".south",
          "root-" + str(j) + ".north",
          stroke: stroke,
        )
      }
    }
  }
  content((horizontal-step, -8.5 * vertical-step), align(center)[
    $overline(p)_(i j) = q_(i j), quad overline(q)_(i j) = p_(i j)$ \
    $(1 <= |j| < i <= 4)$
  ])
})
