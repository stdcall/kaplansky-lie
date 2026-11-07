#import "../main-defs.typ": source

#let front-page(body) = page(header: none, footer: none, {
  set par(first-line-indent: 0pt, justify: false)
  body
})
// A series line between two rules, across the type area.
#let ruled(body) = block(
  width: 100%,
  stroke: (top: 0.9pt, bottom: 0.9pt),
  inset: (y: 1.8mm),
  align(center, text(size: 9pt, tracking: 0.05em, body)),
)

// Page 2: the title of the original.
#let english-title-page() = front-page[
  #source(2)
  #ruled[CHICAGO LECTURES IN MATHEMATICS]
  #align(center)[
    #v(20mm)
    #text(size: 15pt, weight: "bold", tracking: 0.03em)[
      LIE ALGEBRAS\
      AND LOCALLY COMPACT\
      GROUPS
    ]
    #v(13mm)
    #text(size: 13pt, weight: "bold", tracking: 0.03em)[IRVING KAPLANSKY]
    #v(22mm)
    #text(size: 11.5pt)[
      The University of Chicago Press\
      Chicago and London 1971
    ]
  ]
]

// Page 3: the title.
#let russian-title-page() = front-page[
  #source(3)
  #ruled[БИБЛИОТЕКА СБОРНИКА «МАТЕМАТИКА»]
  #align(center)[
    #v(16mm)
    #text(font: "Liberation Sans", size: 14pt, weight: "bold")[И. Капланский]
    #v(4mm)
    #line(length: 16mm, stroke: 0.6pt)
    #v(6mm)
    #text(font: "Liberation Sans", size: 16pt, weight: "bold")[
      АЛГЕБРЫ ЛИ\
      И ЛОКАЛЬНО КОМПАКТНЫЕ\
      ГРУППЫ
    ]
    #v(14mm)
    #text(size: 10pt)[
      Перевод с английского\
      Е. А. ГОРИНА
    ]
  ]
  #v(1fr)
  #block(
    width: 100%,
    stroke: (top: 0.9pt),
    inset: (top: 1.8mm),
    align(center, text(size: 9.5pt, tracking: 0.05em)[
      ИЗДАТЕЛЬСТВО «МИР» МОСКВА 1974
    ]),
  )
]

// Page 4: the annotation and the imprint.
#let annotation-page() = front-page[
  #source(4)
  #text(font: "Liberation Sans", size: 8.5pt, weight: "bold")[УДК 512; 519.46]
  #v(30mm)
  #pad(left: 10mm, {
    set par(justify: true, first-line-indent: (amount: 1.5em, all: true))
    set text(size: 9.5pt)
    [Теория групп Ли и алгебр Ли используется во многих разделах математики и ее
      приложений. Изложению этой теории посвящено очень много современных
      обзоров, монографий и курсов лекций. Среди них книга И.~Капланского~---
      известного американского математика~--- выделяется простотой и четкостью
      изложения, глубиной подхода к рассматриваемым вопросам.]
    parbreak()
    [В первой части книги дается подробное вполне доступное студентам младших
      курсов изложение теории алгебр Ли над произвольным полем. Тщательно
      подобранные задачи дают возможность читателю проверить свое владение
      материалом. Вторая часть посвящена структуре локально компактных групп без
      малых подгрупп.]
    parbreak()
    [Книга написана с присущим автору мастерством. Она несомненно заинтересует
      математиков ряда специальностей, в первую очередь алгебраистов, и будет
      полезна преподавателям, аспирантам и студентам университетов и
      пединститутов.]
  })
  #v(1fr)
  #align(center, text(size: 9.5pt, style: "italic")[
    Редакция литературы по математическим наукам
  ])
  #v(9mm)
  #grid(
    columns: (auto, 1fr),
    align: (left + horizon, right + horizon),
    text(size: 8.5pt)[К $frac("20203—014", "041(01)—74")$ 14—74],
    text(size: 9pt)[© Перевод на русский язык, «Мир», 1974],
  )
]
