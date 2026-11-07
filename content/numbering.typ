// Chapters and sections are headings of levels 1 and 2: counter(heading)
// gives (chapter, section). As in the book, theorems and lemmas count
// separately through a chapter (Теорема 58, Лемма 12), the formulas count
// through a chapter ((14), with their primes (1′), (1″)), the exercises and
// the examples restart in each section, the steps of a proof in each
// statement. chapter() and section() of main-defs.typ reset them.
#let theorems = counter("book-theorem")
#let lemmas = counter("book-lemma")
#let formulas = counter("book-formula")
#let exercise-numbers = counter("book-exercise")
#let exercise-parts = counter("book-exercise-part")
// A run of marked paragraphs counts by its format: «(a)», «(i)», «(1)», «I.»,
// «1.». A chapter, a section and a statement restart them.
#let item-formats = ("(a)", "(i)", "(1)", "I.", "1.")
#let item-counter(format) = counter("book-item:" + format)
#let family-counter(family) = if family == "th" { theorems } else if (
  family == "lem"
) { lemmas } else if family == "eq" { formulas } else if family == "exc" {
  exercise-numbers
} else { counter("numbered:" + family) }
// (chapter, section) at a location; 0 before the first section.
#let place-key(location) = {
  let levels = counter(heading).at(location)
  (levels.at(0, default: 0), levels.at(1, default: 0))
}
// Primed formulas: the label of the primed formula maps to the label of its
// base formula, as a string, and to the prime printed after the base number.
#let formula-primes = (
  "eq:anticommutative": ("eq:square-zero", "′"),
  "eq:commutator-square": ("eq:square-zero", "″"),
  "eq:commutator-jacobi": ("eq:jacobi", "″"),
)
// A record keeps the chapter in every number; the printed number is the last
// part: the theorem, the formula, the exercise, the mark of an item.
#let object-number(family, location, tag: none, prime: none) = {
  let own = if tag != none { tag } else {
    family-counter(family).at(location).first()
  }
  if prime != none {
    let (base, mark) = prime
    let found = query(selector(<numbered>).within(label(base)))
    assert(
      found.len() == 1,
      message: "A primed formula needs its base formula: " + base,
    )
    own = str(found.first().value.number.last()) + mark
  }
  let (chapter, section) = place-key(location)
  if family in ("bib", "fig") { (own,) } else if family in ("eq", "th", "lem") {
    (chapter, own)
  } else { (chapter, section, own) }
}
// The number as the book prints it.
#let printed-number(family, number) = str(number.last())
// The number of a formula as printed, "14" (without the parentheses).
#let formula-number(location, prime: none) = {
  str(object-number("eq", location, prime: prime).last())
}
#let record-number(record) = record.value.number
#let numbered-record(target) = {
  let found = query(target)
  if found.len() != 1 { return none }
  query(selector(<numbered>).within(target)).at(0, default: none)
}
#let record(family, ..flags) = context [#metadata((
  kind: "numbered",
  family: family,
  number: object-number(family, here(), ..flags.named()),
))<numbered>]
