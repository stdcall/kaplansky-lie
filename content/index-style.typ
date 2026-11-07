#import "main-defs.typ": *
#import "main-defs.typ" as defs

// The subject index as the author prints it: a heading on its own line with
// its pages, its subentries «— внутреннее 12», a third level «— — в форме
// Джекобсона 25». The first letter of each letter group is bold. Pages and
// links are computed from the marks.

// Sorting: lower case, the parts of a path joined by a separator below any
// letter, so that a heading precedes its subentries.
#let sort-key(path) = {
  let key = lower(path.join("\u{1}"))
  key = key.replace(regex("\s*\([^)]*\)"), "")
  key = key.replace(regex("[,’'.$]"), "")
  key = key.replace("ё", "е")
  // «$C$-система», «$D$-система», «$V$-алгебра», «$Q$-множество» stand under
  // Ц, Д, В, К: the letters are read «це», «де», «ве», «ку», and close their
  // groups, as in the author's index.
  key = key.replace(regex("\\bc-"), "ц\u{4ff}-")
  key = key.replace(regex("\\bd-"), "д\u{4ff}-")
  key = key.replace(regex("\\bv-"), "в\u{4ff}-")
  key = key.replace(regex("\\bq-"), "к\u{4ff}-")
  key.replace(regex("[a-z]"), m => "\u{4ff}" + m.text)
}

#let locator(location) = box(context {
  metadata((
    kind: "cross-reference",
    target: "index-mark",
    resolved: true,
    position: here().position(),
    target-position: location.position(),
  ))
  link(location, str(counter(page).at(location).first()))
})

#let markup(term) = eval(term, mode: "markup", scope: dictionary(defs))

#let index-entries = context {
  let entries = (:)
  for mark in query(<index-mark>) {
    let path = mark.value.path
    // Headings without pages of their own still head their subentries.
    for depth in range(1, path.len()) {
      let parent = path.slice(0, depth)
      let key = parent.join("\u{1f}")
      if key not in entries { entries.insert(key, (path: parent, at: ())) }
    }
    let key = path.join("\u{1f}")
    let record = entries.at(key, default: (path: path, at: ()))
    let target = mark.value.at("target", default: none)
    let location = if target == none { mark.location() } else {
      let found = query(target)
      assert(found.len() == 1, message: "Index target must exist uniquely")
      found.first().location()
    }
    let number = counter(page).at(location).first()
    if record.at.all(l => counter(page).at(l).first() != number) {
      record.at.push(location)
    }
    entries.insert(key, record)
  }
  // Headings that differ only in the case of their first letter are one.
  let merged = (:)
  for entry in entries.values() {
    let key = sort-key(entry.path)
    if key in merged {
      let found = merged.at(key)
      found.at += entry.at
      merged.insert(key, found)
    } else { merged.insert(key, entry) }
  }
  let sorted = merged.values().sorted(key: e => sort-key(e.path))
  // A heading without pages of its own takes its first subentry into its
  // line, as the author prints «теорема Кюннета 245» / «—сравнения 76».
  let joined = ()
  let skip = false
  for (i, entry) in sorted.enumerate() {
    if skip {
      skip = false
      continue
    }
    let next = sorted.at(i + 1, default: none)
    if (
      entry.path.len() == 1
        and entry.at.len() == 0
        and next != none
        and next.path.len() == 2
        and sort-key(next.path.slice(0, 1)) == sort-key(entry.path)
    ) {
      joined.push((
        path: (entry.path.first() + " " + next.path.last(),),
        at: next.at,
        children-of: entry.path.first(),
      ))
      skip = true
    } else { joined.push(entry) }
  }
  let sorted = joined
  let initial = none
  for entry in sorted {
    let depth = entry.path.len()
    let letter = upper(sort-key(entry.path).clusters().first())
    let first = letter != initial
    if first {
      if initial != none { v(0.6em, weak: true) }
      initial = letter
    }
    let term = entry.path.last()
    let pages = entry
      .at
      .sorted(key: l => counter(page).at(l).first())
      .map(locator)
      .join([, ])
    let head = term.clusters().first()
    let opening = if (
      depth == 1 and head.match(regex("^\p{Cyrillic}$")) != none
    ) {
      let capital = upper(head)
      [#if first { strong(capital) } else { capital }#markup(
          term.slice(head.len()),
        )]
    } else { markup(term) }
    let line = if depth == 1 [#opening #pages] else if depth == 2 [
      —~#markup(term) #pages
    ] else [—~—~#markup(term) #pages]
    block(width: 100%, above: 0pt, below: 0.45em, par(
      hanging-indent: 1.5em,
      line,
    ))
  }
}
