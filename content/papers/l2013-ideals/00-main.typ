#import "../../collection.typ": (
  article-begin, article-introduction, article-style, paper-citation,
  paper-title,
)
#show: article-style.with(language: "en")
#article-begin(
  "l2013-ideals",
  depths: (th: 1, lem: 1, exm: 1),
  groups: (
    th: ("th", "lem", "exm"),
    lem: ("th", "lem", "exm"),
    exm: ("th", "lem", "exm"),
  ),
)

== #paper-title("Egorychev2013NilpotentIdealEnumerationEn") <ch:l2013-ideals>

#paper-citation("Egorychev2013NilpotentIdealEnumerationEn")

#include "01-introduction.typ"
#include "02-ideals.typ"
#include "03-paths.typ"
#include "04-proof.typ"
#include "80-bibliography.typ"
