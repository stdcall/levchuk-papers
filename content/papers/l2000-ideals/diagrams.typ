#import "@preview/cetz:0.5.2": canvas, draw

// Corner pairs determine two increasing-row/increasing-column staircases.
#let ideal-staircases() = canvas(length: 6mm, {
  import draw: *
  let n = 8
  let corners = ((4, 1), (6, 2), (7, 4))
  let secondary = ((1, 5), (2, 6), (3, 8))
  let position(pair) = (pair.last() - 0.5, n - pair.first() + 0.5)
  for pairs in (corners, secondary) {
    let steps = ()
    for (index, pair) in pairs.enumerate() {
      let p = position(pair)
      if index > 0 {
        let previous = position(pairs.at(index - 1))
        steps.push((p.first(), previous.last()))
      }
      steps.push(p)
    }
    line(..steps, stroke: 0.7pt)
  }
  let horizontal = n - corners.first().first() + 0.5
  let vertical = corners.last().last() - 0.5
  line((0.5, horizontal), (n - 0.5, horizontal), stroke: (
    thickness: 0.4pt,
    dash: "dash-dotted",
  ))
  line((vertical, 0.5), (vertical, n - 0.5), stroke: (
    thickness: 0.4pt,
    dash: "dash-dotted",
  ))
  hobby((-0.15, n), (-0.65, n / 2), (-0.15, 0), stroke: 0.7pt)
  hobby((n + 0.15, n), (n + 0.65, n / 2), (n + 0.15, 0), stroke: 0.7pt)
  for (index, pair) in corners.enumerate() {
    let sub = if index == corners.len() - 1 { $r$ } else { index + 1 }
    content((-0.7, position(pair).last()), $i_#sub$, anchor: "east")
    content((position(pair).first(), -0.45), $j_#sub$)
  }
  for (index, pair) in secondary.enumerate() {
    let sub = if index == secondary.len() - 1 { $q$ } else { index + 1 }
    content((position(pair).first(), n + 0.45), $m_#sub$)
    content((n + 0.7, position(pair).last()), $k_#sub$, anchor: "west")
  }
  content((0.8, horizontal + 0.4), $cal(L)$)
  content((n - 1.5, horizontal + 1), $cal(L)'$)
  content((1.1, 1.5), $(T)$)
  content((5.2, 2.4), $(J T)$)
  content((6, 6), $(J^2 T)$)
})
