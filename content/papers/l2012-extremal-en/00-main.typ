#import "../../collection.typ": (
  article-begin, article-style, paper-citation, paper-title,
)
#show: article-style.with(language: "en")
#article-begin(
  "l2012-extremal-en",
  depths: (th: 1, lem: 1),
  groups: (th: ("th", "lem"), lem: ("th", "lem")),
)

#let title() = paper-title("Levchuk2012ExtremalAbelianEn")

== #title() <ch:l2012-extremal-en>

#paper-citation("Levchuk2012ExtremalAbelianEn")

#include "01-body.typ"
#include "02-body.typ"
#include "03-body.typ"
#include "80-bibliography.typ"
