#import "../../collection.typ": article-begin, paper-citation, paper-title
#import "../../main-defs.typ": source

#article-begin(
  "l2015-niltriangular",
  depths: (th: 1, lem: 1, def: 1),
  groups: (
    th: ("th", "lem", "def"),
    lem: ("th", "lem", "def"),
    def: ("th", "lem", "def"),
  ),
)
#source(1, printed: 37)
== #[#paper-title(
  "Levchuk2015NiltriangularGeneralizationsRu",
)] <ch:l2015-niltriangular>
#paper-citation("Levchuk2015NiltriangularGeneralizationsRu")

#include "01-finitary.typ"
#include "02-automorphisms.typ"
#include "03-nonfinitary.typ"
#include "04-canonical-basis.typ"
#include "80-bibliography.typ"
