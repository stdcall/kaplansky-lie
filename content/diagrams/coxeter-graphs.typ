#import "@preview/cetz:0.5.2"

// The Coxeter graphs of § 6 of chapter I. A graph is its list of vertices and
// edges; a chain with an unspecified number of vertices has a gap of three
// dots. A double edge is the book's lens of two arcs, an arrow on one arc runs
// from the shorter root to the longer; a triple edge is the lens with a
// straight line between. All lengths are in millimetres.
#let unit = 8
#let lens-height = 4.4
#let vertex-radius = 0.55

#let vertex(at) = cetz.draw.circle(
  at,
  radius: vertex-radius,
  fill: black,
  stroke: none,
)
#let segment(from, to) = cetz.draw.line(from, to, stroke: 0.6pt)
// The arcs of a lens from `from` to `to`. `arrow`: 1 on the upper arc, -1 on
// the lower one; the head stands at the middle of the arc, where the arc runs
// along the line of the lens, and points towards `to`.
#let lens(from, to, arrow: none) = {
  import cetz.draw: *
  let (x0, y0) = from
  let (x1, y1) = to
  let control(side) = ((x0 + x1) / 2, y0 + side * lens-height)
  for side in (1, -1) {
    bezier(from, to, control(side), stroke: 0.6pt)
  }
  if arrow != none {
    let direction = if x1 > x0 { 1 } else { -1 }
    let y = y0 + arrow * lens-height / 2
    let middle = (x0 + x1) / 2
    line(
      (middle - direction * 0.9, y),
      (middle + direction * 0.9, y),
      stroke: 0.6pt,
      mark: (end: ">", fill: black, scale: 0.55),
    )
  }
}

// A chain of `head` vertices from `x` along the axis, a gap of `gap` free dots
// and `tail` more vertices; all stand on the grid of the table, and what
// comes before the chain joins its first vertex.
#let open-chain(x, head: 3, gap: 2, tail: 2) = {
  for i in range(head + gap + tail) {
    vertex((x + i * unit, 0))
    let edge-inside = (
      i < head - 1 or (i >= head + gap and i < head + gap + tail - 1)
    )
    if edge-inside { segment((x + i * unit, 0), (x + (i + 1) * unit, 0)) }
  }
}

// A closed chain of `count` vertices.
#let closed-chain(count) = {
  for i in range(count) { vertex((i * unit, 0)) }
  for i in range(count - 1) {
    segment((i * unit, 0), ((i + 1) * unit, 0))
  }
}

// E_n: a chain of n - 1 vertices with one more below the third.
#let e-graph(n) = {
  closed-chain(n - 1)
  vertex((2 * unit, -unit))
  segment((2 * unit, 0), (2 * unit, -unit))
}

#let canvas(body) = cetz.canvas(length: 1mm, body)

// The name of a graph whose chain is the top of the drawing, centred on the
// axis of the chain, one vertex high.
#let chain-name(name) = block(
  height: 2 * vertex-radius * 1mm,
  align(left + horizon, name),
)

// The table stands apart from the text and is not split between pages.
#let coxeter-graphs() = block(
  width: 100%,
  above: 1.3em,
  below: 1.3em,
  breakable: false,
  align(center, grid(
    columns: (auto, auto),
    column-gutter: 5mm,
    row-gutter: 3.4mm,
    align: (x, y) => left + (if y >= 6 { top } else { horizon }),
    $A_n$, canvas(open-chain(0, gap: 3)),
    $B_n thin (n >= 2)$,
    canvas({
      vertex((0, 0))
      lens((0, 0), (unit, 0), arrow: 1)
      open-chain(unit)
    }),

    $C_n thin (n >= 3)$,
    canvas({
      vertex((0, 0))
      lens((unit, 0), (0, 0), arrow: -1)
      open-chain(unit)
    }),

    $D_n thin (n >= 4)$,
    canvas({
      for side in (1, -1) {
        vertex((0, side * unit * 0.55))
        segment((0, side * unit * 0.55), (unit, 0))
      }
      open-chain(unit)
    }),

    $G_2$,
    canvas({
      closed-chain(2)
      lens((0, 0), (unit, 0))
    }),

    $F_4$,
    canvas({
      vertex((0, 0))
      segment((0, 0), (unit, 0))
      vertex((unit, 0))
      lens((unit, 0), (2 * unit, 0))
      vertex((2 * unit, 0))
      segment((2 * unit, 0), (3 * unit, 0))
      vertex((3 * unit, 0))
    }),

    chain-name($E_6$), canvas(e-graph(6)),
    chain-name($E_7$), canvas(e-graph(7)),
    chain-name($E_8$), canvas(e-graph(8)),
  )),
)

// The arrow on a double edge: alpha and beta, the arrow from alpha to beta.
#let arrow-edge() = block(width: 100%, above: 1.3em, below: 1.3em, align(
  center,
  canvas({
    vertex((0, 0))
    vertex((2 * unit, 0))
    lens((0, 0), (2 * unit, 0), arrow: 1)
    cetz.draw.content((-3, 0), $alpha$, anchor: "mid")
    cetz.draw.content((2 * unit + 3, 0), $beta$, anchor: "mid")
  }),
))
