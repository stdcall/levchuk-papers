#import "@preview/cetz:0.5.2": canvas, draw

// The rows display the index ranges -i+1,...,i-1 (B) and
// -i,...,-1,1,...,i-1 (C). Middle indices and rows are abbreviated.
#let coefficient(i, j) = $a_(#i,#j)$
#let omitted = $dots$
#let matrix-rows(kind) = {
  let initial = if kind == "B" {
    (
      (coefficient(1, 0),),
      (coefficient(2, -1), coefficient(2, 0), coefficient(2, 1)),
    )
  } else {
    (
      (coefficient(1, -1),),
      (coefficient(2, -2), coefficient(2, -1), coefficient(2, 1)),
    )
  }
  let final = if kind == "B" {
    (
      coefficient($n$, $-n+1$),
      omitted,
      coefficient($n$, -1),
      coefficient($n$, 0),
      coefficient($n$, 1),
      omitted,
      coefficient($n$, $n-1$),
    )
  } else {
    (
      coefficient($n$, $-n$),
      omitted,
      coefficient($n$, -2),
      coefficient($n$, -1),
      coefficient($n$, 1),
      omitted,
      coefficient($n$, $n-1$),
    )
  }
  (..initial, range(5).map(_ => $dot$), final)
}

#let classical-matrix(kind) = canvas(length: 1mm, {
  import draw: *
  let rows = matrix-rows(kind)
  let column-step = 14
  let row-step = 9
  let bottom = -(rows.len() - 1) * row-step
  let half-width = (rows.last().len() - 1) * column-step / 2
  set-style(stroke: 0.6pt, content: (padding: 0.4))
  for (i, row) in rows.enumerate() {
    for (j, cell) in row.enumerate() {
      let x = (j - (row.len() - 1) / 2) * column-step
      content((x, -i * row-step), cell)
    }
  }
  let margin = column-step * 0.65
  let apex = row-step * 0.7
  line((-2, apex), (-half-width - margin, bottom), stroke: 0.6pt)
  line((2, apex), (half-width + margin, bottom), stroke: 0.6pt)
  content(
    (half-width + 2.2 * margin, bottom / 2),
    if kind == "B" { $Phi = B_n,$ } else { $Phi = C_n.$ },
    anchor: "west",
  )
})

#let classical-matrices() = {
  align(center, classical-matrix("B"))
  align(center, classical-matrix("C"))
}
