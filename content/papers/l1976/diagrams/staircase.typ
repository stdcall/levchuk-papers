#import "@preview/cetz:0.5.2"

// Schematic matrix staircase: the middle corners are omitted.
#let staircase(n: 7, corners: ((2, 1), (3, 2), (6, 5))) = {
  let diagram = cetz.canvas(length: 5mm, {
    import cetz.draw: *
    let position(i, j) = (j, n - i)
    let omitted-row = calc.floor(
      (corners.at(1).first() + corners.last().first()) / 2,
    )
    for (index, corner) in corners.enumerate() {
      let (i, j) = corner
      let start-column = if index == 0 { 1 } else if index == 2 {
        j - 1
      } else { corners.at(index - 1).last() }
      let end-row = if index == corners.len() - 1 { n } else if index == 1 {
        omitted-row
      } else { corners.at(index + 1).first() }
      line(
        position(i, start-column),
        position(i, j),
        position(end-row, j),
        stroke: 0.7pt,
      )
    }
    for j in range(1, n + 1) {
      content(position(omitted-row + 1, j), $dot$)
    }
    content(
      position(corners.first().first(), 1),
      $cal(L)$,
      anchor: "south",
      padding: 0.25em,
    )
  })
  math.equation(block: true, math.lr(sym.paren.l + diagram + sym.paren.r))
}
