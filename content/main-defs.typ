#import "numbering.typ": (
  numbered-record, place-key, record-location, record-number,
)

#let in-bibliography = state("in-bibliography", false)
#let editorial-notes = sys.inputs.at("editorial-notes", default: "on") != "off"
#let current-work = state("current-article", "")
#let source(n, printed: none) = context [#metadata((
  kind: "source",
  work: current-work.get(),
  file-page: n,
  printed-page: printed,
  position: here().position(),
))]

#let number-text(body) = text(weight: "semibold", style: "normal", body)
#let reference-body(it, caption) = context {
  let prefix = str(it.target).split(":").first()
  let target = it.element
  let record = if target != none { numbered-record(it.target) }
  let number = if record != none { record-number(record) }
  let named = record != none and record.value.kind == "named"
  let passage = prefix == "pass" and target != none
  // Native equations retain their semantic labels after the display rule.
  let pending = record == none and not passage
  let destination = if passage { target.location() } else if not pending {
    record-location(record)
  }
  let printed = if pending { "?" } else if passage or prefix == "ch" {
    let folio = counter(page).at(destination)
    let pattern = destination.page-numbering()
    if pattern == none { str(folio.first()) } else {
      numbering(pattern, ..folio)
    }
  } else if number == none {
    ""
  } else if prefix not in ("bib", "sec", "ch") {
    number.map(str).join(".")
  } else {
    str(number.last())
  }
  let body = if caption { it.supplement } else if named {
    if target.func() == heading { target.body } else { target.caption.body }
  } else if prefix == "eq" {
    [(#number-text(printed))]
  } else if prefix == "cond" {
    if printed.ends-with("′") {
      $(Gamma'_(#number-text(printed.trim("′", at: end))))$
    } else { $(Gamma_(#number-text(printed)))$ }
  } else { number-text(printed) }
  // Catalogue navigation is separate from an article's author citations.
  let mention = (
    prefix == "bib"
      and not in-bibliography.get()
      and not str(it.target).starts-with("bib:pub-")
  )
  let reference = metadata((
    kind: "cross-reference",
    bibliographic-mention: mention,
    target: str(it.target),
    resolved: not pending,
    printed: printed,
    position: here().position(),
    target-position: if destination != none { destination.position() },
  ))
  if mention { [#reference<bibliographic-mention>] } else {
    [#reference<cross-reference>]
  }
  if pending { body } else { link(destination, body) }
}

#let reference-rules(body) = {
  show ref: it => {
    let caption = it.supplement not in (auto, none, [])
    let shown = reference-body(it, caption)
    box(shown)
  }
  body
}


#let editorial-note-counter = counter("editorial-note")
#let ed-note(body) = if editorial-notes {
  editorial-note-counter.step()
  context {
    let mark = "*" + str(editorial-note-counter.get().first()) + ")"
    let suffix = if text.lang == "en" { [Ed.] } else { [Прим. ред.] }
    footnote(numbering: _ => mark)[#text(style: "normal")[#body~— #emph(
        suffix,
      )]]
    counter(footnote).update(n => n - 1)
  }
}
#let Aut = math.op("Aut")
#let Ann = math.op("Ann")
#let char = math.op("char")
#let id = math.op("id")
#let diag = math.op("diag")
#let End = math.op("End")
#let per = math.op("per")
#let Ker = math.op("Ker")
#let GF = math.upright("GF")
#let UT = math.upright("UT")
#let NC = math.upright("NC")
#let SL = math.upright("SL")
#let GL = math.upright("GL")
#let ru-enum(n) = "абвгдежзийклмнопрстуфхцчшщэюя".clusters().at(n - 1) + ")"
#let twisted(n, body) = math.attach(body, tl: n)
#let NT = math.class("normal", math.upright("NT"))
