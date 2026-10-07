#let collection-cover() = {
  let ink = rgb("202d2e")
  set page(
    margin: 0pt,
    fill: rgb("f5efe1"),
    numbering: none,
    header: none,
    footer: none,
  )
  set text(fill: ink)
  set par(first-line-indent: 0pt)
  let surname = text(
    size: 43pt,
    weight: "bold",
    tracking: 1pt,
    [ЛЕВЧУК],
  )
  place(top + center, dy: 22mm, context {
    let name = [ВЛАДИМИР МИХАЙЛОВИЧ]
    let original = text(size: 11pt, tracking: 0.9pt, name)
    let factor = measure(surname).width / measure(original).width
    text(size: factor * 11pt, tracking: factor * 0.9pt, name)
  })
  place(top + center, dy: 31mm, surname)
  place(top + center, dy: 59mm, image(
    "../assets/levchuk-portrait.svg",
    width: 119mm,
  ))
  place(top + center, dy: 193mm, text(size: 29pt)[Сборник работ])
  place(top + center, dy: 215mm, line(length: 22mm, stroke: 0.6pt + ink))
  place(top + center, dy: 225mm, text(
    size: 11pt,
    [Группы · Кольца · Алгебры],
  ))
  pagebreak()
}
