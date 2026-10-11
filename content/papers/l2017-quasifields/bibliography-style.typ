#import "../../bibliography-data.typ": read-bib
#import "../../bibliography-style.typ" as common
#let data = read-bib("papers/l2017-quasifields/references.bib")
#let bib-description(key) = {
  common.bib-description(
    key,
    data: data,
    related-dois: false,
    target: "bib:l2017-quasifields-" + key,
    backlinks: false,
  )

  common.bib-backlinks("bib:l2017-quasifields-" + key)
}
