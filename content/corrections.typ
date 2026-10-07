#import "corrections-defs.typ": articles, correction-article, correction-markup
#import "collection.typ": paper-citation, paper-title
#import "book-style.typ": formula-rules
#let entries = json("../corrections.json").entries
#set document(
  title: "В. М. Левчук. Сборник работ. Исправления",
  author: "В. М. Левчук",
  date: none,
)
#set page(width: 176mm, height: 250mm, margin: 20mm, numbering: "1")
#set text(font: ("Libertinus Serif", "STIX Two Math"), size: 11pt, lang: "ru")
#set par(justify: true, leading: 0.65em, spacing: 0.8em)
#show: formula-rules
#align(center, text(size: 16pt, weight: "bold")[Исправления])

В. М. Левчук, _Сборник работ_. Номера страниц относятся к исходным текстам
статей.

#if entries.len() == 0 [Подтверждённых исправлений нет.] else {
  for article in articles {
    let own = entries.filter(it => correction-article(it.id).id == article.id)
    if own.len() == 0 { continue }
    heading(level: 1)[#paper-title(article.publication)]
    paper-citation(article.publication)
    let section = none
    for entry in own {
      if entry.section != section {
        section = entry.section
        heading(level: 2, section.split(" · ").last())
      }
      block(breakable: false, above: 0.65em)[
        #metadata((correction: entry.id))
        *#entry.id.replace(article.id + "-", "")* · с. #entry.printed_page,
        #correction-markup(entry.id, entry.place)

        Напечатано: #correction-markup(entry.id, entry.original)

        Исправлено: #correction-markup(entry.id, entry.corrected)

        #correction-markup(entry.id, entry.reason)
      ]
    }
  }
}
