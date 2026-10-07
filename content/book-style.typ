#import "main-defs.typ": reference-rules
#import "statements.typ": numbered-display
#import "numbering.typ": restart-counters, zero-section-numbering
#import "bibliography-data.typ": publications
#let articles = json("../articles.json")

// Wrap a wide display at its existing top-level operators and separators.
// Nested indices, arguments and fractions remain whole mathematical objects.
#let math-sequence = [].func()
#let display-width(body) = {
  measure(
    math.equation(block: false, math.display(body)),
  ).width
}
#let case-lines(body) = {
  if body.func() != math-sequence { return (body,) }
  let rows = ()
  let row = ()
  for child in body.children {
    if child.func() == linebreak {
      rows.push(math-sequence(row))
      row = ()
    } else { row.push(child) }
  }
  if row.len() > 0 { rows.push(math-sequence(row)) }
  rows
}
#let grouped-factor(body) = {
  if body.func() != math.lr { return false }
  let inside = body.body
  if inside.func() != math-sequence or inside.children.len() == 0 {
    return false
  }
  let first = inside.children.first()
  first.has("text") and first.text in ("{", "[")
}
#let large-operator(body) = {
  let base = if body.func() == math.attach { body.base } else { body }
  base.has("text") and base.text in ("∑", "∏")
}
#let reflow-display(body, width) = {
  if display-width(body) <= width { return body }
  if body.func() == math.cases {
    return math.cases(
      reverse: body.reverse,
      ..body
        .children
        .map(row => case-lines(
          reflow-display(row, width - 1.5 * text.size),
        ))
        .flatten(),
    )
  }
  if body.func() != math-sequence { return body }
  let chunks = ()
  let chunk = ()
  let has-grouped-factor = body.children.any(grouped-factor)
  for child in body.children {
    let separator = (
      child.func() == h
        or large-operator(child)
        or (
          has-grouped-factor
            and (
              grouped-factor(child) or child.func() == math-sequence
            )
        )
        or (
          child.has("text")
            and child.text in ("+", "-", "−", "=", "∘", "·", "⋅", "→", "↦")
        )
    )
    if separator and chunk.len() > 0 {
      chunks.push(chunk)
      chunk = ()
    }
    chunk.push(child)
    if (
      child.func() == linebreak
        or (
          child.has("text") and child.text in (",", ";")
        )
    ) {
      chunks.push(chunk)
      chunk = ()
    }
  }
  if chunk.len() > 0 { chunks.push(chunk) }
  // Keep a short clause introduced by quad whole, including comparisons,
  // arithmetic bounds and comma-separated index values.
  let clauses = ()
  let clause = ()
  for chunk in chunks {
    if chunk.first().func() == h and clause.len() > 0 {
      clauses.push(clause)
      clause = ()
    }
    clause.push(chunk)
  }
  if clause.len() > 0 { clauses.push(clause) }
  let joined = ()
  for clause in clauses {
    let whole = clause.flatten()
    if (
      whole.first().func() == h and display-width(math-sequence(whole)) <= width
    ) {
      joined.push(whole)
    } else { joined += clause }
  }
  chunks = joined
  let result = ()
  let line = ()
  for chunk in chunks {
    let candidate = math-sequence((..line, ..chunk))
    if line.len() > 0 and display-width(candidate) > width {
      result.push(linebreak())
      if chunk.first().func() == h { chunk = chunk.slice(1) }
      line = ()
    }
    result += chunk
    line += chunk
    if chunk.last().func() == linebreak { line = () }
  }
  math-sequence(result)
}
#let formula-rules(body) = {
  show math.equation: set text(font: "STIX Two Math")
  show math.equation: it => {
    show ":": math.class("punctuation", ":")
    show "〈": symbol("⟨")
    show "〉": symbol("⟩")
    show "≥": sym.gt.eq.slant
    show "≤": sym.lt.eq.slant
    show regex("[\u{0391}-\u{03A9}]"): math.upright
    it
  }
  show math.mat: math.display
  show math.equation.where(block: false): it => context {
    set math.lr(size: 1em)
    let bounded = text(top-edge: "bounds", bottom-edge: "bounds", it)
    let shown = if measure(bounded).height > 1.2 * text.size {
      bounded
    } else { it }
    if measure(shown).width <= 8 * text.size { box(shown) } else { shown }
  }
  set math.cases(gap: 0.6em)
  body
}
#let book-style(body) = {
  set document(
    title: "В. М. Левчук. Сборник работ",
    author: "В. М. Левчук",
    date: none,
  )
  set page(
    width: 176mm,
    height: 250mm,
    margin: (x: 20mm, top: 21mm, bottom: 21mm),
    numbering: "1",
    footer: context if page.numbering != none {
      align(center, text(size: 10pt, counter(page).display(page.numbering)))
    },
  )
  set text(
    font: ("Libertinus Serif", "STIX Two Math"),
    size: 12pt,
    lang: "ru",
    fill: rgb("202020"),
  )
  set par(
    justify: true,
    linebreaks: "optimized",
    leading: 0.65em,
    spacing: 0.75em,
    first-line-indent: 1.25em,
  )
  set enum(numbering: "1)")
  show regex("т\\. е\\."): [т.~е.]
  show regex("т\\. д\\."): [т.~д.]
  show regex("т\\. п\\."): [т.~п.]
  show regex("-(й|я|е|м|го|му)\\b"): it => it.text.replace("-", "‑")
  show link: set text(fill: rgb("202020"))
  set heading(numbering: (..n) => {
    let values = n.pos()
    if values.len() == 2 {
      ""
    } else if values.len() > 3 {
      values.slice(2).map(str).join(".") + "."
    } else { "§ " + str(values.last()) + "." }
  })
  show heading.where(level: 1): set heading(numbering: none)
  show outline.entry: it => context {
    set block(breakable: false)
    set par(first-line-indent: 0pt, justify: false)
    let target = it.element
    let name = if target.has("label") { str(target.label) } else { "" }
    let article-index = articles.position(item => "ch:" + item.id == name)
    let parts = query(heading.where(level: 1, outlined: true)).filter(
      item => not item.has("label"),
    )
    let part-index = parts.position(item => (
      item.location() == target.location()
    ))
    let prefix = if article-index != none {
      [#(article-index + 1).]
    } else if part-index != none {
      [#numbering("I", part-index + 1).]
    } else { none }
    let inner = if article-index == none { it.inner() } else {
      let article = articles.at(article-index)
      let year = publications.at(article.publication).year
      it.body() + [~(#year) #box(width: 1fr, it.fill) #sym.wj#it.page()]
    }
    link(target.location(), it.indented(prefix, inner))
  }
  show heading: it => {
    set par(first-line-indent: 0pt, justify: false)
    set text(size: if it.level <= 2 { 16pt } else { 12pt })
    if it.numbering != none {
      restart-counters(it.level)
      [#metadata((
        kind: "numbered",
        family: "heading",
        level: it.level,
        tag: if it.numbering == zero-section-numbering { 0 } else { none },
      ))<numbered>]
    }
    block(width: 100%, above: 1.4em, below: 0.8em, sticky: true, align(
      left,
      strong[
        #if it.numbering != none and it.level != 2 [#numbering(
            it.numbering,
            ..counter(heading).at(it.location()),
          )
        ]
        #it.body
      ],
    ))
  }
  set math.equation(numbering: none, supplement: none)
  show: formula-rules
  show math.equation.where(block: true): it => layout(size => {
    if it.has("label") and str(it.label).starts-with("eq:") {
      numbered-display(it, width: size.width, reflow: reflow-display)
    } else {
      let body = reflow-display(it.body, size.width)
      if body == it.body { it } else {
        math.equation(
          block: true,
          numbering: it.numbering,
          number-align: it.number-align,
          supplement: it.supplement,
          body,
        )
      }
    }
  })
  show: reference-rules
  body
}
