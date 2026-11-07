#import "main-defs.typ": reference-rules
#import "statements.typ": (
  numbered-display, paragraph-indent, paragraph-resume, unnumbered-display,
)

// The page: 84×108/32 as printed, with the type area of the book.
#let body-margin = (x: 12.5mm, top: 18mm, bottom: 13mm)

// A page that opens a chapter has neither running head nor folio.
#let opening-page() = {
  query(heading.where(level: 1))
    .map(it => it.location().page())
    .contains(here().page())
}

// The running head: on even pages the folio and «Гл. I. Алгебры Ли»; on odd
// pages the section and the folio: the first section that begins on the page,
// or else the section in force, in the short form of the book where it has
// one. Unnumbered chapters (От переводчика, Список литературы) give their
// title on both.
#let running-header = context {
  if opening-page() { return }
  let here-page = here().page()
  let chapters = query(heading.where(level: 1).before(here()))
  if chapters.len() == 0 { return }
  let chapter = chapters.last()
  let chapter-head = if chapter.numbering == none { chapter.body } else {
    let number = counter(heading).at(chapter.location()).first()
    [Гл.~#numbering("I", number). #chapter.body]
  }
  let even = calc.even(counter(page).get().first())
  let middle = if even or chapter.numbering == none { chapter-head } else {
    let sections = query(heading.where(level: 2)).filter(it => (
      it.location().page() >= chapter.location().page()
        and it.location().page() <= here-page
    ))
    let on-page = sections.find(it => it.location().page() == here-page)
    let section = if on-page != none { on-page } else if sections.len() > 0 {
      sections.last()
    }
    if section == none { chapter-head } else {
      let number = str(counter(heading).at(section.location()).at(1))
      let title = if section.supplement in (none, auto, []) {
        section.body
      } else { section.supplement }
      [#number. #title]
    }
  }
  let folio = text(weight: "semibold", counter(page).display())
  set text(size: 9.5pt)
  set par(first-line-indent: 0pt, justify: false)
  block(width: 100%, inset: (bottom: 2.5pt), stroke: (bottom: 0.6pt), grid(
    columns: (2.2em, 1fr, 2.2em),
    align: (left + bottom, center + bottom, right + bottom),
    if even { folio }, emph(middle), if not even { folio },
  ))
}

// An inline formula taller than the text line takes the room it needs, so
// that it does not run into the neighbouring lines; also used by the
// corrections list.
#let inline-equation(it) = context {
  // Inside a diagram (cd sets the full bounds of the text) a formula keeps
  // its full height, so that arrows meet its indices, not run into them.
  if text.top-edge == "bounds" and text.bottom-edge == "bounds" {
    return box(it)
  }
  // As in TeX, a line is opened up only where the formula would otherwise
  // reach into the lines above or below: above about 0.85em (a fraction, a
  // tall superscript) or more than 0.38em below the baseline.
  let ink = measure({
    set text(top-edge: "bounds", bottom-edge: "bounds")
    it
  })
  let above = measure({
    set text(top-edge: "bounds", bottom-edge: "baseline")
    it
  }).height
  let tall = above > 0.85em.to-absolute()
  let deep = ink.height - above > 0.38em.to-absolute()
  let equation = if tall or deep {
    text(
      top-edge: if tall { "bounds" } else { "cap-height" },
      bottom-edge: if deep { "bounds" } else { "baseline" },
      it,
    )
  } else { it }
  // Keep short inline relations intact at line/page boundaries; long
  // equations retain native mathematical line breaking. Letters joined to
  // a formula ("$G$-модуль") stay on its line.
  if ink.width <= 6em.to-absolute() { box(equation) } else { equation }
  sym.wj
}

// Headings print their formulas bold, as the book does («1. NSS-группы»); a
// chapter title is in capitals except its formulas.
#let bold-math(body) = {
  show math.equation: it => {
    let parts = if it.body.has("children") { it.body.children } else {
      (it.body,)
    }
    if parts.any(p => p.func() == metadata and p.value == "bold-math") {
      it
    } else {
      math.equation(block: it.block, [#metadata("bold-math")#math.bold(
          it.body,
        )])
    }
  }
  body
}
#let upper-text(body) = {
  if body.func() == math.equation { body } else if body.func() == [].func() {
    body.children.map(upper-text).join()
  } else if body.func() == text { upper(body) } else { body }
}

// Rules of the text and of formulas, shared by the book and the
// corrections sheet.
#let text-math-rules(body) = {
  show regex("[тТ]\\. [едпо]\\.|и\\. о\\.|н\\. э\\."): it => box(it)
  // A text hyphen following inline math belongs to the preceding symbol.
  show regex("-"): it => [#text("\u{2060}")#it]
  // No line begins with a dash: «Пуанкаре—Биркгофа», «$A$~— кольцо».
  show "—": it => [#sym.wj#it]
  // Words inside formulas («если», «для») take the text face, italic where
  // emphasised; STIX Two Math has no Cyrillic.
  show math.equation: set text(font: ("STIX Two Math", "Libertinus Serif"))
  // As in TeX: delimiters keep their size around indices and fractions
  // unless a formula asks for growing ones (`lr(…, size: auto)`); the colon
  // of "f: A -> B" is punctuation; ≥ and ≤ are slanted, as printed.
  set math.lr(size: 1em)
  show math.equation: it => {
    show ":": math.class("punctuation", ":")
    show "≥": sym.gt.eq.slant
    show "≤": sym.lt.eq.slant
    // Emphasised words inside a formula in the italic of the text face;
    // STIX Two Math has no Cyrillic italic.
    show emph: e => text(font: "Libertinus Serif", style: "italic", e.body)
    it
  }
  show math.equation.where(block: false): inline-equation
  body
}

#let book-style(body) = {
  set page(
    width: 130mm,
    height: 200mm,
    margin: body-margin,
    numbering: "1",
    header: running-header,
    header-ascent: 30%,
    footer: none,
  )
  set text(font: "Libertinus Serif", size: 10.5pt, lang: "ru")
  set par(
    justify: true,
    leading: 0.55em,
    spacing: 0.55em,
    first-line-indent: paragraph-indent,
  )
  set heading(numbering: (..numbers) => {
    let n = numbers.pos()
    if n.len() == 1 { "Глава " + numbering("I", n.first()) + "." } else {
      str(n.last()) + "."
    }
  })
  // «Глава I» in italics above the title in capitals, as printed; the first
  // paragraph after a heading is indented.
  show heading.where(level: 1): it => {
    let numbered = it.numbering != none
    if numbered {
      context [#metadata((
        kind: "numbered",
        family: "heading",
        level: 1,
        number: (counter(heading).at(it.location()).first(),),
      ))<numbered>]
    }
    set par(first-line-indent: 0pt, justify: false)
    block(width: 100%, above: 13mm, below: 11mm, sticky: true, align(center, {
      if numbered {
        let number = context numbering(
          "I",
          counter(heading).at(it.location()).first(),
        )
        text(size: 11.5pt, weight: "regular", style: "italic")[Глава #number]
        v(7mm)
      }
      text(size: 12.5pt, weight: "regular", bold-math(upper-text(it.body)))
    }))
    paragraph-resume
  }
  show heading.where(level: 2): it => {
    if it.numbering != none {
      context [#metadata((
        kind: "numbered",
        family: "heading",
        level: 2,
        number: counter(heading).at(it.location()).slice(0, 2),
      ))<numbered>]
    }
    set par(first-line-indent: 0pt, justify: false)
    // «$Q$-множество» is not split at its hyphen in a title.
    show "-": h => sym.wj + h + sym.wj
    block(
      width: 100%,
      above: 1.9em,
      below: 1.1em,
      sticky: true,
      align(center, text(size: 11pt, weight: "bold", {
        if it.numbering != none {
          let number = context str(counter(heading).at(it.location()).at(1))
          [#number.#h(0.4em)]
        }
        bold-math(it.body)
      })),
    )
    paragraph-resume
  }
  show: text-math-rules
  show math.equation.where(block: true): set block(above: 0.85em, below: 0.85em)
  show math.equation.where(block: true): it => {
    let children = if it.body.has("children") { it.body.children } else {
      (it.body,)
    }
    let fitted = children.any(child => (
      child.func() == metadata
        and child.value.at("kind", default: none) == "fitted-equation"
    ))
    if fitted { it } else if (
      it.has("label") and str(it.label).starts-with("eq:")
    ) {
      numbered-display(it)
    } else { unnumbered-display(it) }
  }
  set enum(indent: 1.5em, numbering: (..n) => text(
    style: "normal",
    numbering("1)", ..n),
  ))
  set list(indent: 1.5em)
  // Figures stand apart from their neighbours.
  show figure: set block(above: 1.6em, below: 1.6em)
  show figure.caption: set text(size: 0.9em)
  // Footnotes as printed: 9pt, the first line indented.
  show footnote.entry: set text(size: 8.5pt)
  set footnote.entry(
    indent: 0pt,
    separator: line(length: 25%, stroke: 0.5pt),
  )
  show: reference-rules
  // The contents as printed: chapters and the other openings with their page,
  // sections indented under them; leaders of dots.
  set outline(indent: 0pt)
  show outline.entry.where(level: 1): it => block(
    above: 0.9em,
    below: 0.5em,
    breakable: false,
    sticky: true,
    link(it.element.location(), par(
      first-line-indent: 0pt,
      justify: false,
      [#if it.prefix() != none [#it.prefix() ]#it.body()#sym.wj#box(
          width: 1fr,
          it.fill,
        )#sym.wj#it.page()],
    )),
  )
  show outline.entry.where(level: 2): it => {
    // «$Q$-множество» is not split at its hyphen, as in the title itself.
    show "-": h => sym.wj + h + sym.wj
    block(
      above: 0.45em,
      below: 0.45em,
      breakable: false,
      link(it.element.location(), pad(left: 1.3em, par(
        first-line-indent: 0pt,
        hanging-indent: 1.7em,
        justify: false,
        leading: 0.45em,
        [#box(width: 1.7em, it.prefix())#it.body()#sym.wj#box(
            width: 1fr,
            it.fill,
          )#sym.wj#it.page()],
      ))),
    )
  }
  body
}
