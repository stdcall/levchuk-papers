// Each row is (type name, vector diagram, explanatory note).
// Shared columns keep the labels aligned even for diagrams of unequal width.
#let diagram-grid(rows) = block(width: 100%, context {
  set par(first-line-indent: 0pt, justify: false)
  assert(rows.all(row => row.len() == 3))
  let widths = range(3).map(i => rows
    .map(row => measure(row.at(i)).width)
    .fold(0pt, calc.max))
  // Inline boxes share a baseline. Unlike bbox-centering, this keeps an
  // exceptional branch below the chain from moving the type name downward.
  let cells(row) = (
    box(width: widths.at(0), row.at(0))
      + h(0.8em)
      + box(width: widths.at(1), row.at(1))
      + h(0.8em)
      + box(width: widths.at(2), row.at(2))
  )
  stack(dir: ttb, spacing: 0.8em, ..rows.map(row => align(center, cells(row))))
})

// STIX Two Math: MATH.MathConstants.AxisHeight=258, unitsPerEm=1000.
// The canvas baseline lies this far below the y=0 root chain, so its chain
// coincides with the mathematical axis of the adjacent type and condition.
#let root-line-baseline(unit) = -(0.258em.to-absolute() / unit)

#import "@preview/cetz:0.5.2": canvas, draw
// Ordered corners (row,column) determine both boundaries of the formal
// matrix. The second antichain lies above and to the right of the first.
#let matrix-staircases(
  n: 16,
  lower: ((8, 2), (11, 5), (15, 8)),
  upper: ((1, 10), (3, 13), (6, 15)),
) = canvas(length: 5mm, {
  import draw: *
  let at(i, j) = (j, n - i)
  for cs in (lower, upper) {
    assert(cs.all(p => (
      0 < p.at(0) and p.at(0) < n and 0 < p.at(1) and p.at(1) < n
    )))
    for k in range(1, cs.len()) {
      assert(
        cs.at(k).at(0) > cs.at(k - 1).at(0)
          and cs.at(k).at(1) > cs.at(k - 1).at(1),
      )
    }
  }
  let i1 = lower.first().at(0)
  let jr = lower.last().at(1)
  assert(upper.last().at(0) < i1 and upper.first().at(1) > jr)
  set-style(stroke: 0.5pt, content: (
    padding: 0.6,
    wrap: text.with(top-edge: "bounds", bottom-edge: "bounds"),
  ))
  let primary = (at(i1, 0),)
  for (i, j) in lower {
    primary.push(at(i, primary.last().at(0)))
    primary.push(at(i, j))
  }
  primary.push(at(n, jr))
  line(..primary)
  let secondary = (at(0, jr),)
  for (i, j) in upper {
    secondary.push(at(i, secondary.last().at(0)))
    secondary.push(at(i, j))
  }
  secondary.push(at(i1, upper.last().at(1)))
  secondary.push(at(i1, n))
  line(..secondary)
  line(at(0, jr), at(n, jr), stroke: (dash: "dashed"))
  line(at(i1, 0), at(i1, n), stroke: (dash: "dashed"))
  bezier(at(0, 0), at(n, 0), at(0, -1), at(n, -1))
  bezier(at(0, n), at(n, n), at(0, n + 1), at(n, n + 1))
  content(at((i1 + n) / 2, lower.at(1).at(1) / 2), $(T)$)
  content(at((i1 + n) / 2, (jr + n) / 2), $(J T)$)
  content(
    at(upper.at(1).at(0), (upper.at(1).at(1) + n) / 2),
    $(J^2 T)$,
    anchor: "south",
  )
  content(
    at(lower.at(1).at(0) - 0.5, lower.at(1).at(1) - 0.5),
    $cal(L)$,
    anchor: "south-east",
  )
  content(
    at(upper.last().at(0), upper.last().at(1)),
    $cal(L)'$,
    anchor: "south-east",
  )
  for (cs, rs, js, side, row) in (
    (lower, ($i_1$, $i_2$, $i_r$), ($j_1$, $j_2$, $j_r$), -1.5, n + 1),
    (upper, ($k_1$, $k_2$, $k_q$), ($m_1$, $m_2$, $m_q$), n + 1.5, -1),
  ) {
    for (k, (i, j)) in cs.enumerate() {
      content(at(i, side), rs.at(k))
      content(at(row, j), js.at(k))
    }
    content(at((cs.at(1).at(0) + cs.last().at(0)) / 2, side), $dots.v$)
    content(at(row, (cs.at(1).at(1) + cs.last().at(1)) / 2), $dots$)
  }
})
