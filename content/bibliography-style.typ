#import "bibliography-data.typ": bibliography-data
#import "main-defs.typ": in-bibliography

// annotation preserves the original compound punctuation, substituting
// {title}, {pages}, etc. from this record and {Key.pages} from a related
// component. userb holds an original journal spelling where shortjournal
// has not been verified; userc names the part associated with a DOI.
#let rich-bib-text(value) = {
  let value = value.replace("'", "’").replace("\\&", "&")
  let math-text = (
    "ABA": "$A B A$",
    "GL_3(q)": "$upright(\"GL\")_3 lr((q))$",
    "R_n(K, J)": "$R_n lr((K, J))$",
    "N\\Phi(K)": "$N Phi lr((K))$",
    "(B,N)": "$(B,N)$",
  )
  let position = 0
  for match in value.matches(
    regex("\\$[^$]+\\$|_[^_]+_|[A-Z][₀₁₂₃₄₅₆₇₈₉]+"),
  ) {
    value.slice(position, match.start)
    let part = match.text
    if part.starts-with("_") {
      emph(part.slice(1, -1))
    } else if part.starts-with("$") {
      eval(math-text.at(part.slice(1, -1), default: part), mode: "markup")
    } else {
      let digits = "₀₁₂₃₄₅₆₇₈₉".clusters()
      let subscript = part
        .slice(1)
        .clusters()
        .map(c => str(digits.position(d => d == c)))
        .join()
      eval("$" + part.first() + "_" + subscript + "$", mode: "markup")
    }
    position = match.end
  }
  value.slice(position)
}
#let bib-backlinks(target) = context {
  let refs = query(<bibliographic-mention>).filter(it => {
    let value = it.value
    (
      type(value) == dictionary
        and value.at("kind", default: none) == "cross-reference"
        and value.at("target", default: none) == target
        and value.at("bibliographic-mention", default: true)
    )
  })
  let seen = ()
  let pages = ()
  for mention in refs {
    let loc = mention.location()
    if not seen.contains(loc.page()) {
      seen.push(loc.page())
      let position = loc.position()
      let destination = (
        page: position.page,
        x: position.x,
        y: calc.max(0pt, position.y - 8pt),
      )
      let pattern = loc.page-numbering()
      let folio = counter(page).at(loc)
      let shown = if pattern == none { str(folio.first()) } else {
        numbering(pattern, ..folio)
      }
      pages.push(box(context [
        #metadata((
          kind: "page-reference",
          resolved: true,
          target: "bib-mention:" + target,
          position: here().position(),
          target-position: position,
          // Typst adds 10pt above the coordinate destination as well.
          destination-offset-pt: 18,
          description: shown,
        ))
        #link(destination, shown)
      ]))
    }
  }
  if pages.len() > 0 { [ #text(size: 9pt)[\[#pages.join(", ")\]]] }
}
#let background-reading(body) = block(inset: (left: 1em), body)

#let bib-authors(value) = {
  value
    .split(" and ")
    .map(name => {
      let parts = name.split(",")
      if parts.len() == 2 {
        parts.last().trim().replace(" ", "\u{a0}") + " " + parts.first().trim()
      } else if parts.len() == 3 {
        (
          parts.at(2).trim().replace(" ", "\u{a0}")
            + " "
            + parts.first().trim()
            + " "
            + parts.at(1).trim()
        )
      } else { name }
    })
    .join(", ")
}

#let default-bib-template(entry) = {
  let value = "{title}. "
  if "journal" in entry {
    value += "{journal}"
  } else if "booktitle" in entry {
    value += "В кн.: {booktitle}"
  }
  if "publisher" in entry {
    if "journal" in entry or "booktitle" in entry { value += ". " }
    if "location" in entry { value += "{location}: " } else if (
      "address" in entry
    ) { value += "{address}: " }
    value += "{publisher}"
  }
  if "year" in entry { value += ", {year}" }
  if "volume" in entry { value += ", {volume}" }
  if "number" in entry { value += ", № {number}" }
  if "pages" in entry { value += ", {pages}" } else if "pagetotal" in entry {
    value += ", {pagetotal} с."
  }
  value + "."
}

#let bib-description(
  key,
  data: bibliography-data,
  target: none,
  related-dois: true,
  print-language: false,
  backlinks: true,
) = {
  let entry = data.at(key)
  let authors = bib-authors(entry.author)
  if authors != "" {
    authors
    if authors.ends-with(".") { [ ] } else { [. ] }
  }
  let template = entry
    .at("annotation", default: default-bib-template(entry))
    .replace(
      regex(
        "\\s*\\(("
          + "[Ii]n Russian\\.?|[Ii]n English\\.?|"
          + "на русском языке|на английском языке)\\)",
      ),
      "",
    )
    .split("\"")
    .enumerate()
    .map(pair => {
      let (i, part) = pair
      if i == 0 { part } else {
        (if calc.odd(i) { "“" } else { "”" }) + part
      }
    })
    .join()
  let position = 0
  for match in template.matches(regex("\\{([^{}]+)\\}")) {
    rich-bib-text(template.slice(position, match.start))
    let token = match.captures.first().split(".")
    let data = if token.len() == 1 { entry } else {
      assert(
        token.first() in entry.at("related", default: "").split(","),
        message: "Template references an unrelated bibliography record",
      )
      data.at(token.first())
    }
    let field = token.last()
    if field == "journal" {
      emph(rich-bib-text(data.at("shortjournal", default: data.at(
        "userb",
        default: data.at("journal", default: ""),
      ))))
    } else if field == "pages" {
      rich-bib-text(data.at(field).replace("--", "–"))
    } else {
      rich-bib-text(data.at(field))
    }
    position = match.end
  }
  rich-bib-text(template.slice(position))

  for component in (
    (key,)
      + if related-dois {
        entry.at("related", default: "").split(",").filter(k => k != "")
      } else { () }
  ) {
    let record = data.at(component)
    if "doi" in record {
      let part = if "userc" in record { " (" + record.userc + ")" } else { "" }
      [
        #link(
          "https://doi.org/" + record.doi,
          "DOI" + part + ": " + record.doi,
        )]
    }
  }
  if print-language {
    let language = entry.at("language", default: none)
    let names = (russian: "на русском языке", english: "на английском языке")
    if language in names { [ (#names.at(language)).] }
  }
  if backlinks {
    bib-backlinks(if target == none { "bib:" + key } else { target })
  }
}
