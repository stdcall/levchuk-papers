#import "../../collection.typ": (
  article-begin, article-style, paper-citation, paper-title,
)
#import "../../main-defs.typ": source
#show: article-style.with(language: "en")
#article-begin(
  "l2000-ideals",
  depths: (th: 1, lem: 1, def: 1, prop: 1, exm: 1),
  groups: (
    th: ("th", "lem", "def", "prop", "exm"),
    lem: ("th", "lem", "def", "prop", "exm"),
    def: ("th", "lem", "def", "prop", "exm"),
    prop: ("th", "lem", "def", "prop", "exm"),
    exm: ("th", "lem", "def", "prop", "exm"),
  ),
)
#source(2, printed: "3503")
== #[#paper-title("Kuzucuoglu2000MatrixIdealsEn")] <ch:l2000-ideals>
#paper-citation("Kuzucuoglu2000MatrixIdealsEn")
#include "01-introduction.typ"
#include "02-structural.typ"
#include "03-construction.typ"
#include "04-abelian.typ"
#include "80-bibliography.typ"
