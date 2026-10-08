#import "main-defs.typ" as book-defs
#import "papers/l1974/defs.typ" as l1974
#import "papers/l1976/defs.typ" as l1976
#import "papers/l1982-parabolic/defs.typ" as l1982
#import "papers/l1983/defs.typ" as l1983
#import "papers/l2012-extremal/defs.typ" as l2012
#import "papers/l2018-enveloping/defs.typ" as l2018
#import "papers/l2013-ideals/defs.typ" as l2013
#import "papers/l2015-niltriangular/defs.typ" as l2015-niltriangular
#import "papers/l2008-monic/defs.typ" as l2008-monic
#import "papers/l2013-thompson/defs.typ" as l2013-thompson
#import "papers/l2019-nonfinitary/defs.typ" as l2019-nonfinitary

#import "papers/l2011-local/defs.typ" as l2011-local

#import "papers/l2008-model/defs.typ" as l2008-model

#import "papers/l2018-malcev/defs.typ" as l2018-malcev

#import "papers/l2012-model/defs.typ" as l2012-model

#let articles = json("../articles.json")
#let scopes = (
  l2012-model: dictionary(l2012-model),
  l2018-malcev: dictionary(l2018-malcev),
  l2008-model: dictionary(l2008-model),
  l2011-local: dictionary(l2011-local),
  l1974: dictionary(l1974),
  l1976: dictionary(l1976),
  l1982-parabolic: dictionary(l1982),
  l1983: dictionary(l1983),
  l2012-extremal: dictionary(l2012),
  l2018-enveloping: dictionary(l2018),
  l2013-ideals: dictionary(l2013),
  l2015-niltriangular: dictionary(l2015-niltriangular),
  l2008-monic: dictionary(l2008-monic),
  l2013-thompson: dictionary(l2013-thompson),
  l2019-nonfinitary: dictionary(l2019-nonfinitary),
)
#let correction-article(id) = articles.find(it => id.starts-with(it.id + "-"))
#let correction-markup(id, field) = {
  let article = correction-article(id)
  assert(article != none, message: "Correction does not name an article")
  eval(
    field,
    mode: "markup",
    scope: dictionary(book-defs) + scopes.at(article.id, default: (:)),
  )
}
