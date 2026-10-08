#import "main-defs.typ": current-work, editorial-note-counter
#import "numbering.typ": family-counter, family-depth, section-examples
#import "numbering.typ": article-depths, article-groups, article-prefixes
#import "numbering.typ": introduction-section-numbering, zero-section-numbering
#import "bibliography-data.typ": publications
#import "bibliography-style.typ": bib-authors, rich-bib-text

#let part-title(body) = {
  pagebreak(weak: true)
  v(28%)
  heading(level: 1, numbering: none, body)
}

#let article-style(language: "ru", body) = {
  set text(lang: language)
  body
}

// The introduction has no printed number; its author number remains structural.
#let article-introduction(body, number: 0) = {
  assert(number in (0, 1), message: "An introduction starts at section 0 or 1")
  let style = if number == 0 { zero-section-numbering } else {
    introduction-section-numbering
  }
  heading(level: 3, numbering: style, body)
  if number == 0 {
    context counter(heading).update((..counter(heading).get().slice(0, 2), 0))
  }
}

#let article-begin(work, depths: (:), groups: (:), prefixes: (:)) = {
  pagebreak(weak: true)
  current-work.update(work)
  article-depths.update(depths)
  article-groups.update(groups)
  article-prefixes.update(prefixes)
  for family in family-depth.keys() {
    family-counter(family).update(0)
  }
  section-examples.update(0)
  counter("numbered:theorem-cor").update(0)
  editorial-note-counter.update(0)
  counter(footnote).update(0)
}

#let paper-title(key) = rich-bib-text(publications.at(key).title)
#let paper-abstract(language: none, body) = context {
  let language = if language == none { text.lang } else { language }
  block(above: 0.8em, below: 0.8em, {
    set text(size: 10.5pt, lang: language)
    set par(first-line-indent: 0pt, spacing: 0.5em)
    strong(if language == "ru" { [Аннотация.] } else { [Abstract.] })
    [ ]
    body
  })
}
#let paper-keywords(language: none, body) = context {
  let language = if language == none { text.lang } else { language }
  block(above: 0.4em, below: 1em, {
    set text(size: 10.5pt, lang: language)
    set par(first-line-indent: 0pt)
    strong(if language == "ru" { [Ключевые слова:] } else { [Keywords:] })
    [ ]
    body
  })
}
#let paper-citation(key, funding: none) = {
  let entry = publications.at(key)
  block(above: 0.5em, below: 1.8em, {
    set par(first-line-indent: 0pt)
    set text(size: 10pt)
    bib-authors(entry.author)
    if funding != none { footnote(funding) }
    linebreak()
    emph(rich-bib-text(entry.at("shortjournal", default: entry.journal)))
    [, #entry.year, #entry.volume]
    if "number" in entry { [, № #entry.number] }
    [, ]
    entry.pages.replace("--", "–")
    [.]
    if "doi" in entry {
      [ #link("https://doi.org/" + entry.doi, "DOI: " + entry.doi)]
    }
  })
}
