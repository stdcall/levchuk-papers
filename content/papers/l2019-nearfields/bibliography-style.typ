#import "../../bibliography-data.typ": read-bib
#import "../../bibliography-style.typ" as common
#let data = read-bib("papers/l2019-nearfields/references.bib")
#let bib-description(key) = common.bib-description(
  key,
  data: data,
  related-dois: false,
  target: "bib:l2019-nearfields-" + key,
)
