#set document(
  title: "Алгебры Ли и локально компактные группы",
  author: "И. Капланский",
  date: none,
)
#import "book-style.typ": book-style
#import "main-defs.typ": unnumbered-chapter
#import "frontmatter/cover.typ": cover
#cover()
#show: book-style
// The cover stands outside the pagination, in the place of the first leaf's
// page 1 of the book: the English title is page 2.
#counter(page).update(2)
#import "frontmatter/title.typ": (
  annotation-page, english-title-page, russian-title-page,
)
#english-title-page()
#russian-title-page()
#annotation-page()
#include "00-translator.typ"
#include "00-preface.typ"
#include "01-00-lie-algebras.typ"
#include "01-01-definitions-examples.typ"
#include "01-02-solvable-nilpotent.typ"
#include "01-03-semisimple.typ"
#include "01-04-cartan-subalgebras.typ"
#include "01-05-geometric-char-zero.typ"
#include "01-06-geometric-classification.typ"
#include "01-07-geometric-char-p.typ"
#include "01-08-geometric-continued.typ"
#include "02-00-locally-compact.typ"
#include "02-01-nss-groups.typ"
#include "02-02-one-parameter-existence.typ"
#include "02-03-differentiable-functions.typ"
#include "02-04-functions-q-set.typ"
#include "02-05-functions-q-sequence.typ"
#include "02-06-ratio-bound.typ"
#include "02-07-proper-differentiable.typ"
#include "02-08-vector-space.typ"
#include "02-09-k-neighbourhood.typ"
#include "02-10-nss-approximation.typ"
#include "02-11-further-development.typ"
#include "80-bibliography.typ"
#include "90-index.typ"
// The contents, the address to the reader, the imprint and the publisher's
// notices close the book, as printed.
#unnumbered-chapter(outlined: false)[Оглавление]
#outline(title: none, depth: 2)
#import "frontmatter/backmatter.typ": (
  colophon-page, notice-lie-groups, notice-manifolds, reader-page,
)
#reader-page()
#colophon-page()
#notice-manifolds()
#notice-lie-groups()
