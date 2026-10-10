#import "../../collection.typ": (
  article-begin, article-style, paper-citation, paper-title,
)
#show: article-style.with(language: "en")
#article-begin("l2017-quasifields")

#let title() = paper-title("Levchuk2017QuasifieldTranslationPlanesEn")

== #title() <ch:l2017-quasifields>

#paper-citation("Levchuk2017QuasifieldTranslationPlanesEn")

#include "01-introduction.typ"
#include "02-remarks.typ"
#include "03-order16.typ"
#include "04-planes.typ"
#include "05-primitivity.typ"
#include "06-order32.typ"
#include "07-order64.typ"
#include "08-powers.typ"
#include "09-orders.typ"
#include "80-bibliography.typ"
