#import "numbering.typ": (
  exercise-numbers, exercise-parts, family-counter, formula-number,
  formula-primes, item-counter, object-number, record,
)
#import "main-defs.typ": reference-rules, restart-items, spaced
#let sequence = [].func()
#let join-pieces(pieces) = sequence(
  pieces
    .map(it => if it.func() == sequence and not it.has("label") {
      it.children
    } else { (it,) })
    .flatten(),
)
#let keep-label(original, rebuilt) = {
  if original.has("label") [#rebuilt#original.label] else { rebuilt }
}

#let paragraph-indent = 1.5em

// Put `head` at the start of the first paragraph of `body`.
#let prepend-heading(body, head) = {
  if (
    body.func() in (table, grid, figure, list, enum, terms)
      or (
        body.func() == math.equation and body.block
      )
  ) {
    (
      block(above: 0pt, below: 0.95em, sticky: true, {
        set par(first-line-indent: (amount: paragraph-indent, all: true))
        par(head)
      })
        + body
    )
  } else if body.func() == block {
    let fields = body.fields()
    let inner = fields.remove("body")
    block(prepend-heading(inner, head), ..fields)
  } else if body.func() == sequence and body.children.len() > 0 {
    let children = body.children
    let first = children.position(it => (
      it.func()
        not in (
          [ ].func(),
          parbreak,
        )
    ))
    if first == none { join-pieces((head, body)) } else {
      keep-label(body, join-pieces((
        ..children.slice(0, first),
        prepend-heading(children.at(first), head),
        ..children.slice(first + 1),
      )))
    }
  } else { head + body }
}

// A statement or a proof is a run of ordinary paragraphs, not a block of its
// own, so that Typst's paragraph indent works as in the book: its first
// paragraph and the paragraph after it are indented, and text that continues
// a sentence after a display stays flush left.
#let flush-first(body, indent: 0pt) = {
  let styled(it) = {
    set par(first-line-indent: (amount: indent, all: true))
    it
  }
  let breaks(it) = (
    it.func() in (parbreak, block, grid, table, figure, list, enum, terms)
      or (it.func() == math.equation and it.block)
  )
  if body.func() == sequence and body.children.len() > 0 {
    let end = body.children.position(breaks)
    if end == none { styled(body) } else {
      join-pieces((
        styled(join-pieces(body.children.slice(0, end))),
        ..body.children.slice(end),
      ))
    }
  } else { styled(body) }
}

// Whether `body` ends with a display formula.
#let ends-with-display(body) = {
  if body.func() == math.equation { return body.block }
  if body.func() == sequence {
    let rest = body.children.filter(it => (
      it.func()
        not in (
          [ ].func(),
          parbreak,
          metadata,
        )
    ))
    return rest.len() > 0 and ends-with-display(rest.last())
  }
  if body.has("child") { return ends-with-display(body.child) }
  false
}
// Typst does not indent a paragraph after a display; the book indents the
// paragraph after a statement or a proof that ends with one. An empty
// paragraph without spacing restores the chain.
#let paragraph-resume = {
  par(spacing: 0pt)[]
  context v(-par.spacing)
}

// The space around a statement is about half a line more than the space
// between paragraphs. It is weak and collapses with the space of a
// neighbouring statement, so two statements in a row are as far apart as a
// statement and a paragraph. A proof follows its statement at this distance,
// and the text after it stands at the same distance, as printed.
#let statement-space = v(1.17em, weak: true)
#let statement-run(body, after: true, wrap: it => it) = {
  statement-space
  wrap(flush-first(body, indent: paragraph-indent))
  parbreak()
  if ends-with-display(body) { paragraph-resume }
  if after { statement-space }
}

// An italic statement: also the words inside its formulas («где», «и») are
// italic, as printed; they take the text face, STIX Two Math has no Cyrillic
// italic. The marks of its parts, «(a)», «(i)», stay upright, as printed.
#let italic-body(body) = {
  show math.equation.where(block: false): it => {
    show regex("\p{Cyrillic}+"): t => text(
      font: "Libertinus Serif",
      style: "italic",
      t,
    )
    it
  }
  show regex("\((?:[a-z]|i{1,3}|iv)\)"): set text(style: "normal")
  text(style: "italic", body)
}

// «Т е о р е м а 17.»: the word letterspaced, the number and the title
// upright. Theorems and lemmas restart the items of their proofs.
#let statement(
  kind,
  family,
  body,
  numbered: true,
  title: none,
  italic: true,
) = {
  if numbered {
    family-counter(family).step()
    restart-items(keep: ("(i)",))
  }
  let head = context {
    let number = if numbered {
      record(family)
      str(family-counter(family).get().first())
    }
    text(style: "normal", if number == none { spaced(kind + ".") } else [
      #spaced(kind)~#number#if title != none [ (#title)].
    ])
    [ ]
  }
  // The italic goes around the paragraphs, so that flush-first sees them.
  statement-run(
    prepend-heading(body, head),
    wrap: if italic { italic-body } else { it => it },
  )
}
#let theorem(body, ..args) = statement("Теорема", "th", body, ..args)
#let lemma(body, ..args) = statement("Лемма", "lem", body, ..args)
// Definitions and remarks are unnumbered and upright, as printed; their terms
// are emphasised in the text.
#let definition(body, ..args) = statement(
  "Определение",
  "def",
  body,
  numbered: false,
  italic: false,
  ..args,
)
#let remark(body, ..args) = statement(
  "Замечание",
  "rem",
  body,
  numbered: false,
  italic: false,
  ..args,
)

// «Д о к а з а т е л ь с т в о.»; the book prints no end mark. A proof with
// its own head: `head: [Доказательство леммы.]`; a proof without a head is
// plain text. `continued: true`: the rest of a proof after an inserted lemma,
// an ordinary paragraph without the space of a statement.
#let proof-head = [Доказательство.]
#let proof(body, head: proof-head, continued: false) = {
  let opening = {
    // Only the word «Доказательство» is letterspaced («Доказательство
    // леммы.»), as printed.
    show regex("Доказательство\\.?"): it => spaced(it)
    head
  }
  statement-run(prepend-heading(body, opening + [ ]))
}

#let number-mark(body) = text(weight: "semibold", body)

// A paragraph set off by a little space, as printed; `head`: a letterspaced
// run-in head («Р а з м е р н о с т ь о д и н.»).
#let separated(body, head: none) = statement-run(
  if head == none { body } else { prepend-heading(body, spaced(head) + [ ]) },
)

// A paragraph that opens with a mark counted in its run: the examples of § 1
// («(a)», sub-items «(i)»), the steps of a proof, the cases of a list. Its
// first line is indented, the following lines start at the margin; the marks
// are upright also in italic text. `intro`: a run-in head before the mark
// («П р и м е р ы. (a) …»). `restart: true` starts a new run of this format
// inside a section or a statement.
#let marked-item(family, format, body, intro: none, restart: false) = {
  if restart { item-counter(format).update(0) }
  item-counter(format).step()
  if format == "(a)" { item-counter("(i)").update(0) }
  let head = context {
    let mark = numbering(format, item-counter(format).get().first())
    record(family, tag: mark)
    if intro != none { spaced(intro) + [ ] }
    // The numbered points of a survey (§ 11 of chapter II) are semibold.
    text(style: "normal", if family == "step" and format == "1." {
      number-mark(mark)
    } else { mark })
    [ ]
  }
  // A little space before the items «(a)» and «1.», as printed; «(i)», «(1)»,
  // «I.» follow the text. The text after an item goes on as a paragraph.
  if format in ("(a)", "1.") { v(1em, weak: true) }
  let indent = if family == "exm" and format == "(i)" {
    2 * paragraph-indent
  } else { paragraph-indent }
  flush-first(prepend-heading(body, head), indent: indent)
  parbreak()
  if ends-with-display(body) { paragraph-resume }
}
#let example(body, format: "(a)", ..args) = marked-item(
  "exm",
  format,
  body,
  ..args,
)
#let step(body, format: "(a)", ..args) = marked-item(
  "step",
  format,
  body,
  ..args,
)

// A new paragraph after a display formula, indented as the book prints it;
// plain text after a display continues the sentence at the margin.
#let new-par(body) = {
  par(first-line-indent: (amount: paragraph-indent, all: true), body)
  parbreak()
}

// Exercises close a section: «УПРАЖНЕНИЯ» and the numbered items in smaller
// type; the first line of an item is indented, the others start at the margin.
#let exercises(body, head: [УПРАЖНЕНИЯ]) = {
  if head != none {
    v(1.9em, weak: true)
    block(
      width: 100%,
      above: 1.9em,
      below: 1.1em,
      sticky: true,
      align(center, head),
    )
  }
  set text(size: 9.5pt)
  body
}
// `numbered: false`: the only exercise of a section, without a number.
#let exercise(body, numbered: true) = {
  if numbered { exercise-numbers.step() }
  exercise-parts.update(0)
  let head = context {
    record("exc")
    if numbered {
      number-mark[#exercise-numbers.get().first().]
      [ ]
    }
  }
  block(
    width: 100%,
    above: 1.05em,
    below: 1.05em,
    breakable: true,
    {
      flush-first(prepend-heading(body, head), indent: paragraph-indent)
      parbreak()
    },
  )
}
// A part of an exercise, «(a)», «(b)»: a paragraph of its own without a label
// (the exercises refer to them in plain text).
#let part(body) = {
  exercise-parts.step()
  let head = context {
    numbering("(a)", exercise-parts.get().first())
    [ ]
  }
  flush-first(prepend-heading(body, head), indent: paragraph-indent)
  parbreak()
}

// A figure with its caption «Рис. 1.» under it; the figures are numbered
// through the book, a reference prints the number. The book's figures have
// no caption; it is printed only if given.
#let book-figure(body, caption: none) = {
  family-counter("fig").step()
  figure(
    [#record("fig")#body],
    caption: caption,
    numbering: none,
    supplement: none,
    kind: "book-figure",
  )
}

#let bib-group(body) = heading(level: 2, numbering: none, outlined: false, body)
// "1. БЛОК (BLOCK R.), …": the number in a column of its own, the lines of the
// record after the first under its text.
#let bib-number-width = 1.7em
#let bib-entry(body) = {
  family-counter("bib").step()
  context block(width: 100%, above: 0.75em, below: 0.75em, par(
    first-line-indent: 0pt,
    hanging-indent: bib-number-width,
    [#record("bib")#box(
        width: bib-number-width,
        align(right)[#object-number("bib", here()).last().#h(0.35em)],
      )#body],
  ))
}

#let fit-display(body, numbered: false, prime: none) = layout(size => context {
  let tag = [(#formula-number(here(), prime: prime))]
  let reserve = if numbered { 2 * measure(tag).width + 10pt } else { 0pt }
  let available = size.width - reserve
  let formula = math.equation(block: false, math.display(body))
  let width = measure(reference-rules(formula, trace: false)).width
  metadata((kind: "equation-scale", factor: calc.min(1, available / width)))
  if width > available {
    scale(available / width * 100%, reflow: true, formula)
  } else { formula }
})

#let numbered-display(it) = {
  let prime = formula-primes.at(str(it.label), default: none)
  math.equation(
    block: true,
    number-align: left + top,
    numbering: _ => context [(#formula-number(here(), prime: prime))],
    [#metadata((kind: "fitted-equation"))#family-counter("eq").update(n => (
        n + (if prime != none { 0 } else { 1 })
      ))#record("eq", prime: prime)#if (
        it.body.has("children")
          and it.body.children.any(c => c.func() == linebreak)
      ) { it.body } else {
        fit-display(it.body, numbered: true, prime: prime)
      }],
  )
}

#let unnumbered-display(it) = {
  let parts = if it.body.has("children") { it.body.children } else {
    (it.body,)
  }
  let qed = parts.any(p => (
    p.func() == metadata and p.value.at("kind", default: none) == "qed-display"
  ))
  math.equation(
    block: true,
    [#metadata((kind: "fitted-equation"))#fit-display(
        it.body,
        numbered: qed,
      )],
  )
}
