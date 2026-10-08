#import "book-style.typ": book-style
#import "collection.typ": part-title
#import "cover.typ": collection-cover
#show: book-style
#collection-cover()
#counter(page).update(1)
#set page(numbering: "i")
#outline(title: [Содержание], depth: 2)
#pagebreak()
#include "01-preface.typ"
#pagebreak()
#counter(page).update(1)
#set page(numbering: "1")

#part-title[
  Унитреугольные группы и ассоциированные кольца]
#include "papers/l1974/00-main.typ"
#include "papers/l1975-automorphisms/00-main.typ"
#include "papers/l1976/00-main.typ"
#include "papers/l1983/00-main.typ"
#include "papers/l1987-rings/00-main.typ"
#include "papers/l2000-ideals/00-main.typ"
#include "papers/l2001-automorphisms/00-main.typ"
#include "papers/l2002-radical/00-main.typ"
#include "papers/l2004-finitary/00-main.typ"
#include "papers/l2005-sylow/00-main.typ"
#include "papers/l2008-monic/00-main.typ"
#include "papers/l2011-local/00-main.typ"

#part-title[
  Группы и алгебры Шевалле: подгруппы и автоморфизмы]
#include "papers/l1982-parabolic/00-main.typ"
#include "papers/l1990-small/00-main.typ"
#include "papers/l1990-chevalley/00-main.typ"
#include "papers/l1992-chevalley/00-main.typ"
#include "papers/l2009-finitary/00-main.typ"
#include "papers/l2016-hypercentral/00-main.typ"

#part-title[
  Абелевы подгруппы унипотентных групп]
#include "papers/l2008-normal/00-main.typ"
#include "papers/l2012-extremal-en/00-main.typ"
#include "papers/l2012-extremal/00-main.typ"
#include "papers/l2013-thompson/00-main.typ"

#part-title[
  Идеалы нильтреугольных алгебр и задачи перечисления]
#include "papers/l2001-enumeration/00-main.typ"
#include "papers/l2013-ideals/00-main.typ"
#include "papers/l2015-exceptional/00-main.typ"
#include "papers/l2015-niltriangular/00-main.typ"
#include "papers/l2018-enveloping/00-main.typ"
#include "papers/l2019-nonfinitary/00-main.typ"
#include "papers/l2020-nonassoc/00-main.typ"
#include "papers/l2022-graph/00-main.typ"

#part-title[
  Теория моделей групп и колец]
#include "papers/l2008-model/00-main.typ"
#include "papers/l2009-model/00-main.typ"
#include "papers/l2012-model/00-main.typ"
#include "papers/l2018-malcev/00-main.typ"

#include "95-publications.typ"
