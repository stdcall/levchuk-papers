#import "../../collection.typ": (
  article-begin, article-style, paper-citation, paper-title,
)
#import "../../main-defs.typ": source
#show: article-style.with(language: "en")
#let series = ("th", "lem", "prop", "cor", "exm", "rem")
#article-begin(
  "l2001-automorphisms",
  depths: (th: 1, lem: 1, prop: 1, cor: 1, exm: 1, rem: 1),
  groups: (
    th: series,
    lem: series,
    prop: series,
    cor: series,
    exm: series,
    rem: series,
  ),
)
#source(1, printed: 473)
== #paper-title("Kuzucuoglu2001RadicalAutomorphismsEn") <ch:l2001-automorphisms>
#paper-citation("Kuzucuoglu2001RadicalAutomorphismsEn")
#include "01-introduction.typ"
#include "02-fundamental.typ"
#include "03-automorphism-group.typ"
#include "04-structure.typ"
#include "80-bibliography.typ"
