#import "../../collection.typ": (
  article-begin, article-style, paper-citation, paper-title,
)
#show: article-style.with(language: "en")
#article-begin("l1992-chevalley", groups: (
  th: ("th", "prop"),
  prop: ("th", "prop"),
))
== #paper-title("Levchuk1992ChevalleyUnipotentEn") <ch:l1992-chevalley>
#paper-citation("Levchuk1992ChevalleyUnipotentEn")
#include "01-normal.typ"
#include "02-twisted.typ"
#include "03-carpets.typ"
#include "04-automorphisms.typ"
#include "05-unitriangular.typ"
#include "06-ideals.typ"
#include "80-bibliography.typ"
