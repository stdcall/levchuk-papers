#import "numbering.typ": *
#import "main-defs.typ": in-bibliography
#let references-in(it) = {
  if it.func() == ref { (it.target,) } else if it.has("children") {
    it.children.map(references-in).flatten()
  } else if it.has("body") { references-in(it.body) } else { () }
}

// Head of a numbered object: steps the family's counter, leaves the record
// and shows the object's own number with `format`.
#let counted(family, format) = {
  family-counter(family).step()
  if family == "exm" { section-examples.step() }
  context {
    record(family)
    format(object-number(family, here()).last())
  }
}

// Number of a displayed formula with a label, `$ … $
// <eq:homomorphism-path-equation>`; the show rule of book-style.typ calls this
// for every labelled display. A display listed in `formula-tags`
// (numbering.typ) is tagged with a letter, "(F)", and not counted.
#let numbered-display(it, body: none, width: none, reflow: none) = {
  let body = if body == none { it.body } else { body }
  let name = str(it.label)
  let tag = formula-tags.at(name, default: none)
  if tag == none {
    let skip = formula-skips.at(name, default: 0)
    family-counter("eq").update(n => n + 1 + skip)
  }
  context {
    record("eq", tag: tag)
    let shown = object-number("eq", here(), tag: tag).map(str).join(".")
    let shown = if tag != none { emph(shown) } else { shown }
    let number = text(font: "Libertinus Serif", style: "normal")[(#shown)]
    // A centred body needs the same reserve on both sides. Leave a full
    // em between its right edge and the actual (possibly primed) number.
    let body = if width != none and reflow != none {
      reflow(body, width - 2 * (measure(number).width + text.size))
    } else { body }
    math.equation(
      block: true,
      // Upright also inside the italic text of a theorem.
      numbering: _ => number,
      number-align: end + horizon,
      body,
    )
  }
}

// Rebuilding a statement's first or last paragraph (to take a head or an
// ending) joins its pieces as `+` and `join` do, flattening nested sequences
// one level, but keeps a labelled sequence whole (`#eg
// <exm:additive-group-of-field>`, a problem closing a proof): `+` would merge
// it into its neighbours and lose its label. A rebuilt labelled object gets its
// label back.
#let sequence = [].func()
#let join-pieces(pieces) = sequence(
  pieces
    .map(it => if it.func() == sequence and not it.has("label") {
      it.children
    } else { (it,) })
    .flatten(),
)
#let keep-label(original, rebuilt) = {
  if original.has("label") [#rebuilt#original.label] else { rebuilt }
}

// Put `head` at the start of the first paragraph of `body`.
#let prepend-heading(body, head) = {
  if body.func() == block {
    let fields = body.fields()
    let inner = fields.remove("body")
    block(prepend-heading(inner, head), ..fields)
  } else if body.func() == sequence and body.children.len() > 0 {
    let children = body.children
    let first = children.position(it => (
      it.func()
        not in (
          [ ].func(),
          parbreak,
        )
    ))
    if first == none { join-pieces((head, body)) } else {
      keep-label(body, join-pieces((
        ..children.slice(0, first),
        prepend-heading(children.at(first), head),
        ..children.slice(first + 1),
      )))
    }
  } else { head + body }
}

// Put `ending` after the last word or formula of `body`.
#let append-ending(body, ending) = {
  if body.func() == math.equation and body.block {
    if body.has("label") and str(body.label).starts-with("eq:") {
      // Keep the proof mark below the equation number in the right column.
      return [#body#align(right, ending)]
    }
    // A display does not span the line by itself; widen it so that the mark
    // stands at the right margin on the display's last line.
    block(width: 100%, {
      place(bottom + right, ending)
      body
    })
  } else if body.func() in (block, box) {
    let fields = body.fields()
    let inner = fields.remove("body")
    body.func()(append-ending(inner, ending), ..fields)
  } else if body.func() == sequence and body.children.len() > 0 {
    let children = body.children
    let last = children
      .rev()
      .position(it => it.func() not in ([ ].func(), parbreak))
    if last == none { join-pieces((body, ending)) } else {
      let index = children.len() - last - 1
      keep-label(body, join-pieces((
        ..children.slice(0, index),
        append-ending(children.at(index), ending),
        ..children.slice(index + 1),
      )))
    }
  } else { body + ending }
}

// A statement is a run of ordinary paragraphs with a little extra space
// around it, as in the book, not a block of its own: then Typst's paragraph
// indent works as in the book. The statement's head is indented like a new
// paragraph, so is the paragraph after the statement, while text that
// continues a sentence after a display formula stays flush left (a block
// would break the chain of paragraphs and lose the first two indents).
//
// Typst does not indent a paragraph that follows a display. A statement
// starts a new paragraph even there, so its first paragraph is indented
// always (`all: true`, the amount of book-style.typ); the rest of the
// statement follows the ordinary rule.
#let indent-first(body) = {
  let styled(it) = {
    set par(first-line-indent: (amount: 1.25em, all: true))
    it
  }
  let breaks(it) = (
    it.func() in (parbreak, block, grid, table, figure, list, enum, terms)
      or (it.func() == math.equation and it.block)
  )
  if body.func() == sequence and body.children.len() > 0 {
    let end = body.children.position(breaks)
    if end == none { styled(body) } else {
      join-pieces((
        styled(join-pieces(body.children.slice(0, end))),
        ..body.children.slice(end),
      ))
    }
  } else { styled(body) }
}

// The space around a statement is the paragraph spacing and a little more.
// It is weak and collapses with the paragraph spacing and with the space of
// a neighbouring statement, so two statements in a row are as far apart as
// a statement and a paragraph, not twice as far.
#let statement-space = context v(par.spacing + 0.35em, weak: true)
#let statement-intro(body) = {
  // A statement opening with prose and a display keeps the introductory
  // paragraph with that display. The remaining paragraphs stay in the
  // ordinary flow and retain their usual indentation and page breaks.
  if body.func() != sequence { return indent-first(body) }
  let children = body.children
  let first-break = children.position(it => (
    it.func() in (parbreak, block, grid, table, figure, list, enum, terms)
      or (it.func() == math.equation and it.block)
  ))
  if first-break == none { return indent-first(body) }
  let next = children
    .slice(first-break)
    .find(it => (
      it.func() not in ([ ].func(), parbreak)
    ))
  if next == none or next.func() != math.equation or not next.block {
    return indent-first(body)
  }
  keep-label(body, join-pieces((
    block(
      sticky: true,
      above: 0pt,
      par(
        first-line-indent: (amount: 1.25em, all: true),
        join-pieces(children.slice(0, first-break)),
      ),
    ),
    ..children.slice(first-break),
  )))
}
#let statement-block(body) = {
  statement-space
  statement-intro(body)
  parbreak()
  statement-space
}

// Shared journal typography, independent of an article's language and counters.
#let statement-text(family, body) = {
  set text(style: if family in ("th", "lem", "cor", "prop") {
    "italic"
  } else { "normal" })
  statement-block(body)
}

#let theorem-like(kind, family, title, numbered, body) = {
  let head = {
    if numbered { family-counter(family).step() }
    if family == "th" and numbered {
      counter("numbered:theorem-cor").update(0)
    }
    context {
      set text(style: "normal")
      record(family, numbered: numbered)
      strong[#kind#if numbered [
          #object-number(family, here()).map(str).join(".")].]
      if title != none { [ (#title)] }
      [ ]
    }
  }
  statement-text(family, prepend-heading(body, head))
}
#let theorem(title: none, numbered: true, body) = theorem-like(
  "Теорема",
  "th",
  title,
  numbered,
  body,
)
#let lemma(title: none, numbered: true, body) = theorem-like(
  "Лемма",
  "lem",
  title,
  numbered,
  body,
)
#let corollary(title: none, numbered: true, body) = theorem-like(
  "Следствие",
  "cor",
  title,
  numbered,
  body,
)
#let theorem-corollary(body) = {
  counter("numbered:theorem-cor").step()
  let head = context {
    set text(style: "normal")
    record("cor", parent: "th")
    let number = object-number("cor", here(), parent: "th")
    strong[Следствие #number.map(str).join("."). ]
  }
  statement-text("cor", prepend-heading(body, head))
}
#let remark(title: none, numbered: true, body) = theorem-like(
  "Замечание",
  "rem",
  title,
  numbered,
  body,
)
#let example(title: none, numbered: true, body) = theorem-like(
  "Пример",
  "exm",
  title,
  numbered,
  body,
)

#let remark-item(body) = {
  family-counter("rem").step()
  context [#record("rem")#body]
}
#let proof-head = [Доказательство.]
#let condition(body) = block({
  context {
    record("cond")
    let n = object-number("cond", here()).last()
    [$(Gamma_(#str(n)))$ ]
  }
  body
  family-counter("cond").step()
})
#let primed-condition(base, body) = block({
  let targets = references-in(base)
  assert(
    targets.len() == 1,
    message: "A primed condition needs one native reference",
  )
  context {
    let target = str(targets.first())
    record("cond", prime: target)
    let number = object-number("cond", here(), prime: target).last()
    [$(Gamma'_(#number.trim("′", at: end)))$ ]
  }
  body
})
#let repeated-statement(kind, number, body) = statement-text(
  "th",
  prepend-heading(body, text(style: "normal", strong[#kind #number. ])),
)
#let proof(body, head: proof-head, qed: false) = {
  set text(style: "normal")
  let body = if qed { append-ending(body, [ $square.stroked$]) } else { body }
  let head = if head == none { none } else {
    set text(style: "italic", weight: "regular")
    show strong: it => it.body
    show emph: it => it.body
    head
  }
  statement-block(
    if head == none { body } else { prepend-heading(body, [#head ]) },
  )
}
#let bib-item(body) = {
  family-counter("bib").step()
  block(above: 0.6em, below: 0.6em, {
    set par(first-line-indent: 0pt, hanging-indent: 1.5em)
    in-bibliography.update(true)
    context [#record("bib")#object-number("bib", here()).last(). #body]
    in-bibliography.update(false)
  })
}
