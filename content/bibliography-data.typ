// Strict reader for this edition's braced UTF-8 BibLaTeX records.
// Nested braces in the annotation templates are preserved.
#let read-bib(path) = {
  let records = (:)
  let entry = none
  let key = none
  let field = none
  let pending = ""
  let depth = 0
  for raw in read(path).split("\n") {
    let line = raw.trim()
    if field != none {
      pending += " " + line
      depth += line.matches("{").len() - line.matches("}").len()
      if depth == 0 {
        entry.insert(
          field,
          pending.trim().trim(",", at: end).trim().slice(1, -1),
        )
        field = none
        pending = ""
      }
      continue
    }
    if line == "" or line.starts-with("%") { continue }
    if entry == none {
      let head = line.match(regex("^@([A-Za-z]+)\\{([A-Za-z][A-Za-z0-9]*),$"))
      assert(head != none, message: "Invalid BibLaTeX entry header")
      key = head.captures.at(1)
      assert(key not in records, message: "Duplicate bibliography key: " + key)
      entry = (entrytype: lower(head.captures.first()))
      continue
    }
    if line == "}" {
      assert(
        "title" in entry,
        message: "A bibliography record requires a title",
      )
      records.insert(key, entry)
      entry = none
      key = none
      continue
    }
    let assignment = line.match(
      regex("^([A-Za-z][A-Za-z0-9_-]*)\\s*=\\s*(.*)$"),
    )
    assert(assignment != none, message: "Invalid BibLaTeX field")
    field = lower(assignment.captures.first())
    assert(field not in entry, message: "Duplicate field in " + key)
    pending = assignment.captures.at(1)
    assert(pending.starts-with("{"), message: "BibLaTeX values must be braced")
    depth = pending.matches("{").len() - pending.matches("}").len()
    if depth == 0 {
      entry.insert(field, pending.trim().trim(",", at: end).trim().slice(1, -1))
      field = none
      pending = ""
    }
  }
  assert(entry == none and field == none, message: "Unclosed BibLaTeX record")
  records
}
#let author-bibliography = read-bib("../references.bib")
#let editorial-bibliography = read-bib("../editorial.bib")
#assert(author-bibliography
  .keys()
  .all(key => key not in editorial-bibliography))
#let bibliography-data = author-bibliography + editorial-bibliography
