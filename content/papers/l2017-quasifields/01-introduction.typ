#import "../../main-defs.typ": source
#import "../../collection.typ": (
  article-introduction, paper-abstract, paper-keywords,
)

#source(1, printed: 688)

#paper-abstract(language: "en")[
  It is well-known that the constructions and classification of non-Desarguesian
  projective planes are closely connected with ones for quasifields. We consider
  the problems on structure of finite quasifields and semifields: automorphisms
  and autotopisms, maximal subfields and their orders, the spectrum of orders of
  non-zero elements and hypotheses about generated subsets of the multiplicative
  loop.
]

#paper-keywords(language: "en")[
  Quasifield, semifield, translation plane, semifield plane, spread set.
]

#article-introduction(number: 1)[Introduction]
<sec:l2017-quasifields-introduction>

The failure from properties of commutativity and associativity of fields leads
to concept of _semifield_ (or _quasitelo_, by Kurosh
[@bib:l2017-quasifields-Kurosh1963, II.6.1]). It is a (simple) ring, where
non-zero elements form a multiplicative loop, i.e., a group without property of
associativity. The weakening also of two-sided distributivity to one-sided one
gives a general concept of _quasifield_.

The investigations of quasifields had been more century ago when Veblen,
Maclagan-Wedderburn [@bib:l2017-quasifields-Veblen1907] and Dickson
[@bib:l2017-quasifields-Dickson1906] used quasifields in the constructions of
projective translation planes. Also, this plane is Desarguesian iff its
coordinatizating quasifield is a field.

The investigations of problems of construction and classification of projective
planes and quasifields from 1960s (Kleinfeld
[@bib:l2017-quasifields-Kleinfeld1960], Knuth [@bib:l2017-quasifields-Knuth1963,
@bib:l2017-quasifields-Knuth1965], etc) usually use computer calculations. The
development to 2007 is reflected by Johnson, Jha, Biliotti
[@bib:l2017-quasifields-Johnson2007] in Handbook (861 pages). Note that the
structure of even known proper (or not being a field) finite semifields is
poorly studied.

We discuss certain problems on structure of finite quasifields and semifields in
next section. Closely related constructions of projective translation planes and
their coordinatizing quasifields are considered in section
§~@sec:l2017-quasifields-planes. Further we consider some results.
