#import "../../bibliography-data.typ": read-bib
#import "../../bibliography-style.typ" as common
#let data = read-bib("papers/l2019-nonfinitary/references.bib")
#let bib-description(key) = common.bib-description(
  key,
  data: data,
  target: "bib:l2019-nonfinitary-" + key,
)
