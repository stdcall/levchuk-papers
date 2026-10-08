#import "../../collection.typ": (
  article-begin, article-style, paper-citation, paper-title,
)
#show: article-style.with(language: "en")
#article-begin(
  "l2004-finitary",
  depths: (th: 1, lem: 1, cor: 1, rem: 1, exm: 1),
  groups: (
    th: ("th", "lem", "cor", "rem", "exm"),
    lem: ("th", "lem", "cor", "rem", "exm"),
    cor: ("th", "lem", "cor", "rem", "exm"),
    rem: ("th", "lem", "cor", "rem", "exm"),
    exm: ("th", "lem", "cor", "rem", "exm"),
  ),
)
== #[#paper-title("Kuzucuoglu2004FinitaryIsomorphismsEn")]
<ch:l2004-finitary>
#paper-citation("Kuzucuoglu2004FinitaryIsomorphismsEn")
#include "01-introduction.typ"
#include "02-central-series.typ"
#include "03-isomorphisms.typ"
#include "04-main-proof.typ"
#include "80-bibliography.typ"
