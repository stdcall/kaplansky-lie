#import "numbering.typ": (
  numbered-record, place-key, printed-number, record-number,
)

// The page of the file is the printed page of the book.
#let printed-offset = 0

#let source(n, printed: none) = context {
  let printed = if printed == none { str(n - printed-offset) } else {
    printed
  }
  [#metadata((
    kind: "source",
    file-page: n,
    printed-page: printed,
    position: here().position(),
  ))]
}

// Numbers are semibold, but never lighter than a bold heading around them.
#let number-text(body) = context {
  let weight = text.weight
  let heavy = (
    weight in ("bold", "extrabold", "black")
      or (type(weight) == int and weight > 600)
  )
  text(weight: if heavy { weight } else { "semibold" }, style: "normal", body)
}

// Keep a reference's invisible position with its first visible word.
// Descriptive references may wrap over several lines.
#let caption-link(body, destination) = {
  if type(body) == str { body = text(body) }
  if body.func() in ([ ].func(), linebreak, parbreak, h, v, metadata) {
    return body
  }
  if body.func() == text and body.has("text") {
    let visible = body.text.match(regex("\\S(?:[\\s\\S]*\\S)?"))
    if visible == none { return body }
    return [#body.text.slice(0, visible.start)#link(
        destination,
        body.text.slice(visible.start, visible.end),
      )#body.text.slice(visible.end)]
  }
  if body.func() == [].func() {
    return body.children.map(it => caption-link(it, destination)).join()
  }
  if body.func() in (emph, strong) {
    let fields = body.fields()
    let inner = fields.remove("body")
    return body.func()(caption-link(inner, destination), ..fields)
  }
  if body.func() == link { body } else { link(destination, body) }
}
#let anchor-caption(body, marker, destination) = {
  if body.func() in ([ ].func(), linebreak, parbreak, h, v, metadata) {
    return (false, body)
  }
  if body.func() == text and body.has("text") {
    let word = body.text.match(regex("\\S+"))
    if word == none { return (false, body) }
    return (
      true,
      [#body.text.slice(0, word.start)#box[
          #marker#link(destination, body.text.slice(word.start, word.end))
        ]#caption-link(body.text.slice(word.end), destination)],
    )
  }
  if body.func() == [].func() {
    let done = false
    let parts = ()
    for child in body.children {
      if done { parts.push(caption-link(child, destination)) } else {
        let (found, content) = anchor-caption(child, marker, destination)
        done = found
        parts.push(content)
      }
    }
    return (done, parts.join())
  }
  if body.func() in (emph, strong, link) {
    let fields = body.fields()
    let (found, content) = anchor-caption(
      fields.remove("body"),
      marker,
      destination,
    )
    return (found, body.func()(content, ..fields))
  }
  (true, box[#marker#link(destination, body)])
}

#let reference-body(it, caption, trace: true) = context {
  let target = str(it.target)
  let prefix = target.split(":").first()
  let record = if it.element != none { numbered-record(it.target) }
  let number = if prefix in ("pg", "front") and it.element != none {
    (counter(page).at(it.element.location()).first(),)
  } else if record != none { record-number(record) }
  let pending = number == none
  // A chapter is cited by its Roman number (гл. II), a section by its number
  // in the chapter (§ 11 гл. II), everything else by its last part.
  let printed = if pending { "?" } else if prefix == "ch" {
    numbering("I", number.last())
  } else if prefix in ("exm", "step") {
    str(number.last()).trim(".", at: end)
  } else { str(number.last()) }
  let body = if caption { it.supplement } else if prefix == "eq" {
    text(style: "normal")[(#number-text(printed))]
  } else if prefix in ("exm", "step") {
    // The mark of an item: only its letter or number is semibold.
    let inner = printed.match(regex("^\((.*)\)$"))
    text(style: "normal", if inner == none { number-text(printed) } else [
      (#number-text(inner.captures.first()))
    ])
  } else { number-text(printed) }
  if not trace { return body }
  let destination = if pending { none } else if (
    prefix in ("pg", "front") or it.element.func() == math.equation
  ) { it.element.location() } else { record.location() }
  let marker = {
    metadata((
      kind: "cross-reference",
      target: target,
      resolved: not pending,
      printed: printed,
      target-position: if not pending { destination.position() },
    ))
    if prefix == "bib" {
      [#metadata((kind: "bibliography-mention", target: target))
        <bibliography-mention>]
    }
  }
  if caption and not pending {
    return anchor-caption(body, marker, destination).last()
  }
  let anchored = [#marker#body]
  if pending { anchored } else { link(destination, anchored) }
}

#let reference-rules(body, trace: true) = {
  show ref: it => {
    let caption = it.supplement not in (auto, none, [], [°], [′])
    let shown = reference-body(it, caption, trace: trace)
    // The mark of a part stays with its reference: «лемма 4(a)».
    if caption { shown } else { box(shown) + sym.wj }
  }
  body
}

#let idx(target: none, ..path) = {
  assert(path.named().len() == 0 and path.pos().len() > 0)
  [#metadata((
    kind: "index-mark",
    path: path.pos(),
    target: target,
  ))<index-mark>]
}

// The body of a note without the spaces around it, whatever the line breaks of
// the source.
#let trim-spaces(body) = {
  if not body.has("children") { return body }
  let space = [ ].func()
  let children = body.children
  while children.len() > 0 and children.first().func() == space {
    children = children.slice(1)
  }
  while children.len() > 0 and children.last().func() == space {
    children = children.slice(0, -1)
  }
  children.join()
}

#let editorial-note-counter = counter("editorial-note")
#let ed-note(body) = {
  editorial-note-counter.step()
  context {
    // «*1)» in the text and in the note, a space before the note's text.
    let mark = "*" + str(editorial-note-counter.get().first()) + ")"
    footnote(numbering: _ => mark)[#h(0.3em)#trim-spaces(body)~— _Прим. ред._]
    counter(footnote).update(n => n - 1)
  }
}
// The translator's notes of the book, «1)» restarting on each page.
#let tr-note(body) = {
  [#metadata("translator-note")<translator-note>]
  context {
    let page = here().page()
    let earlier = query(selector(<translator-note>).before(here()))
    let number = earlier.filter(it => it.location().page() == page).len()
    footnote(numbering: _ => str(number) + ")")[
      #h(0.3em)#trim-spaces(body)~— _Прим. перев._
    ]
    counter(footnote).update(n => n - 1)
  }
}


#import "numbering.typ": (
  exercise-numbers, exercise-parts, formulas, item-counter, item-formats,
  lemmas, theorems,
)
// Items restart with a chapter, a section and a statement; a statement leaves
// the run «(i)» going: the construction of § 4 of chapter II has lemmas inside.
#let restart-items(keep: ()) = {
  for format in item-formats {
    if format not in keep { item-counter(format).update(0) }
  }
}
// A chapter begins on a new page and restarts the formulas, the theorems and
// the lemmas; a section restarts the exercises.
#let chapter(title) = {
  pagebreak(weak: true)
  formulas.update(0)
  theorems.update(0)
  lemmas.update(0)
  exercise-numbers.update(0)
  restart-items()
  heading(level: 1, title)
}
// `short`: the title of the running head where the book shortens it («7.
// Геометрическое исследование (характеристика p)»).
#let section(title, short: none) = {
  exercise-numbers.update(0)
  restart-items()
  // Weak spacing, as after a statement, of which the larger one stands: the gap
  // of a block alone would give way to it.
  v(1.9em, weak: true)
  heading(level: 2, supplement: short, title)
}

// Preface, bibliography, lists: chapter-like openings without a number.
// `before`: what the book prints above the title on the same page (the
// dedication).
#let unnumbered-chapter(title, outlined: true, before: none) = {
  pagebreak(weak: true)
  before
  heading(level: 1, numbering: none, outlined: outlined, title)
}
#let editorial-bibliography = []

#let subject-index(body) = {
  set par(first-line-indent: 0pt, justify: false, leading: 0.45em)
  set text(size: 9pt)
  columns(2, gutter: 5mm, body)
}

// A citation range «[32]–[40]»: both ends are native references, and the
// records between them in the order of the list also count this place as
// a mention.
#let bib-order = {
  read("80-bibliography.typ")
    .matches(regex("<bib:([A-Za-z0-9]+)>"))
    .map(m => m.captures.first())
}
#let cite-range(first, last) = {
  let key(it) = str(it.target).slice(4)
  let a = bib-order.position(k => k == key(first))
  let b = bib-order.position(k => k == key(last))
  assert(a != none and b != none and a < b, message: "cite-range: ends")
  [\[#first\]–\[#last\]]
  for k in bib-order.slice(a + 1, b) {
    let mention = (kind: "bibliography-mention", target: "bib:" + k)
    [#metadata(mention)<bibliography-mention>]
  }
}

// The letters and operators of the book.
#let RR = $bold(upright(R))$
#let CC = $bold(upright(C))$
#let QQ = $bold(upright(Q))$
#let ZZ = $bold(upright(Z))$
#let Tr = math.op("Tr")
// Delimiters that grow with their contents, where the book prints them so
// (the style keeps delimiters at text size, as TeX does).
#let grow(body) = math.lr(body, size: 100%)

// The place of a preface on the left, the author on the right, in italics.
#let signature(where, name) = block(above: 2.2em, grid(
  columns: (1fr, auto),
  emph(where), emph(name),
))
// The dedication above the title of the preface, on the right.
#let dedication(body) = align(right, block(align(left, emph(body))))

// A letterspaced run-in head inside the text.
#let spaced(body) = {
  // A point in a run of its own: the run before it ends without tracking.
  show ".": it => it
  text(tracking: 0.22em, body)
}
