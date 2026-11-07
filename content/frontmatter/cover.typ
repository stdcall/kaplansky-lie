// The front cover: green paper with a light band at the spine, the mark of the
// series «Библиотека сборника „Математика“» with its big letter М, the author
// and the title in bold italics.
#let green = rgb("8aa35f")
#let paper = rgb("f4f0e2")

// The big letter of the mark: a light М with a black outline.
#let big-letter(width, height, stem) = {
  let inner = 0.36 * height
  let notch = 0.62 * height
  polygon(
    fill: paper,
    stroke: (paint: black, thickness: 2.6pt, join: "miter"),
    (0mm, 0mm),
    (stem, 0mm),
    (width / 2, notch - 0.2 * height),
    (width - stem, 0mm),
    (width, 0mm),
    (width, height),
    (width - stem, height),
    (width - stem, inner),
    (width / 2, notch + 0.12 * height),
    (stem, inner),
    (stem, height),
    (0mm, height),
  )
}

#let cover() = page(
  width: 130mm,
  height: 200mm,
  margin: 0mm,
  fill: green,
  numbering: none,
  header: none,
  footer: none,
)[
  #set text(font: "Libertinus Serif", lang: "ru", hyphenate: false)
  #set par(first-line-indent: 0pt, spacing: 0pt, justify: false)
  #let at(x, y, body) = place(top + left, dx: x, dy: y, body)
  // The band at the spine.
  #at(0mm, 0mm, rect(width: 13.7mm, height: 200mm, fill: paper, stroke: none))
  // The black bar of the name of the series, with the rest of the word.
  #at(0mm, 16.8mm, rect(
    width: 47.8mm,
    height: 12.4mm,
    fill: black,
    stroke: none,
  ))
  #at(13.6mm, 17.9mm, scale(x: 54%, origin: left + top, text(
    font: "Liberation Sans",
    size: 27pt,
    weight: "bold",
    fill: paper,
    tracking: 0.03em,
  )[АТЕМАТИКА]))
  #at(13.6mm, 11.9mm, scale(x: 55%, origin: left + top, text(
    font: "Liberation Sans",
    size: 12pt,
    weight: "bold",
    fill: black,
  )[БИБЛИОТЕКА СБОРНИКА]))
  #at(2.1mm, 11.7mm, big-letter(10.4mm, 39.5mm, 2.7mm))
  // The author and the title, centred on the green field.
  #let centred(y, body) = place(top + left, dx: 13.7mm, dy: y, block(
    width: 116.3mm,
    align(center, body),
  ))
  #centred(74mm, text(
    size: 15pt,
    weight: "bold",
    style: "italic",
    tracking: 0.05em,
  )[
    И. КАПЛАНСКИЙ
  ])
  #centred(83mm, circle(radius: 0.8mm, fill: black, stroke: none))
  #centred(88mm, {
    set par(leading: 1.05em)
    text(size: 25pt, weight: "bold", style: "italic", tracking: 0.04em)[
      Алгебры Ли\
      и локально\
      компактные\
      группы
    ]
  })
  #centred(150mm, circle(radius: 0.8mm, fill: black, stroke: none))
]
