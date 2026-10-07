#import "../../bibliography-data.typ": read-bib
#import "../../bibliography-style.typ" as common
#let data = read-bib("papers/l2001-enumeration/references.bib")
#let bib-description(key) = common.bib-description(
  key,
  data: data,
  target: "bib:l2001-enumeration-" + key,
)
