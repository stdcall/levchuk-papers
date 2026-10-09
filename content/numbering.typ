// Every family is numbered continuously throughout the article.
#let family-counter(family) = counter("numbered:" + family)
#let section-examples = counter("numbered:exm-section")
#let article-depths = state("article-numbering-depths", (:))
#let article-groups = state("article-numbering-groups", (:))
#let article-prefixes = state("article-numbering-prefixes", (:))
#let zero-section-numbering(..numbers) = []
#let introduction-section-numbering(..numbers) = []
#let formula-skips = (:)
#let formula-tags = ("eq:l1975-automorphisms-presentation": "A")
#let family-depth = (
  th: 0,
  lem: 0,
  cor: 0,
  rem: 0,
  exm: 0,
  eq: 0,
  bib: 0,
  tab: 0,
  fig: 0,
  pr: 0,
  prop: 0,
  def: 0,
  exc: 0,
  cond: 0,
)
#let place-key(location) = counter(heading).at(location)
#let restart-counters(level) = context {
  for family in family-depth.keys() {
    let depth = article-depths
      .get()
      .at(family, default: family-depth.at(family))
    if depth > 0 and level <= depth + 2 { family-counter(family).update(0) }
  }
}
#let numbered-record(target) = {
  if query(target).len() != 1 { return none }
  let record = query(selector(<numbered>).within(target)).at(0, default: none)
  if record != none { return record }
  let element = query(target).first()
  // Native unnumbered headings and figures retain their semantic targets.
  // A figure's number belongs to its native kind-specific counter.
  if element.func() == heading and element.numbering == none {
    return (
      value: (kind: "named", family: "heading", level: element.level),
      element: element,
    )
  }
  if element.func() == figure {
    return (
      value: (
        kind: if element.numbering == none { "named" } else { "numbered" },
        family: if element.kind == table { "tab" } else { "fig" },
        tag: if element.numbering != none {
          counter(figure.where(kind: element.kind))
            .at(element.location())
            .last()
        },
      ),
      element: element,
    )
  }
  none
}
#let record-location(record) = if type(record) == dictionary {
  record.element.location()
} else { record.location() }
#let object-number(
  family,
  location,
  prime: none,
  tag: none,
  numbered: true,
  parent: none,
) = {
  if not numbered { return none }
  if tag != none { return (tag,) }
  if parent == "th" {
    return (
      ..object-number("th", location),
      counter("numbered:theorem-cor").at(location).first(),
    )
  }
  if prime != none {
    let base = numbered-record(label(prime))
    if base == none { return ("?",) }
    return (str(base.value.number.last()) + "′",)
  }
  let depth = article-depths
    .at(location)
    .at(family, default: family-depth.at(family))
  let heading-numbers = place-key(location)
  let prefixes = article-prefixes.at(location)
  let prefix-depth = prefixes.at(family, default: depth)
  let scope = if prefix-depth > 0 and heading-numbers.len() > 2 {
    heading-numbers.slice(2, calc.min(2 + prefix-depth, heading-numbers.len()))
  } else { () }
  // A prefix can name a section while the object counter remains global.
  // Before the first section the explicitly requested prefix is zero.
  let scope = if family in prefixes {
    scope + range(scope.len(), prefix-depth).map(_ => 0)
  } else { scope }
  let group = article-groups.at(location).at(family, default: (family,))
  let own = group.map(it => family-counter(it).at(location).first()).sum()
  (..scope, own)
}
#let record-number(record) = {
  let value = record.value
  if value.kind == "named" { return none }
  if value.family == "heading" {
    if value.at("tag", default: none) != none { return (value.tag,) }
    let numbers = counter(heading).at(record-location(record))
    if value.level >= 4 { numbers.slice(2) } else { (numbers.last(),) }
  } else {
    object-number(
      value.family,
      record-location(record),
      numbered: value.at("numbered", default: true),
      prime: value.at("prime", default: none),
      tag: value.at("tag", default: none),
      parent: value.at("parent", default: none),
    )
  }
}
#let record(family, ..flags) = context [#metadata((
  kind: "numbered",
  family: family,
  ..flags.named(),
  number: object-number(family, here(), ..flags.named()),
))<numbered>]
