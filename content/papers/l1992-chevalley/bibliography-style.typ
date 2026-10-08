#import "../../bibliography-data.typ": read-bib
#import "../../bibliography-style.typ" as common
#let data = read-bib("papers/l1992-chevalley/references.bib")
#let bib-description(key) = common.bib-description(
  key,
  data: data,
  related-dois: false,
  target: "bib:l1992-chevalley-" + key,
)
