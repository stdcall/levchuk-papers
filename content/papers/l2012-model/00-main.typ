#import "../../collection.typ": (
  article-begin, article-style, paper-citation, paper-title,
)
#show: article-style.with(language: "ru")
#article-begin(
  "l2012-model",
  depths: (th: 1, lem: 1, rem: 1, pr: 1),
  groups: (
    th: ("th", "lem", "rem", "pr"),
    lem: ("th", "lem", "rem", "pr"),
    rem: ("th", "lem", "rem", "pr"),
    pr: ("th", "lem", "rem", "pr"),
  ),
)
== #paper-title("Levchuk2012ModelStructuralProblemsRu") <ch:l2012-model>
#paper-citation("Levchuk2012ModelStructuralProblemsRu")
#include "01-models.typ"
#include "02-associated.typ"
#include "03-chevalley.typ"
#include "04-congruence.typ"
#include "80-bibliography.typ"
