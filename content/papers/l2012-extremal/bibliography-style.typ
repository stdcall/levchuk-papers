#import "../../bibliography-data.typ": read-bib
#import "../../bibliography-style.typ" as common
#let data = read-bib("papers/l2012-extremal/references.bib")
#let bib-description(key) = common.bib-description(
  key,
  data: data,
  target: "bib:l2012-extremal-" + key,
)
#let abstract-citation() = common.bib-description(
  "Levchuk2012Abstract",
  data: data,
)
