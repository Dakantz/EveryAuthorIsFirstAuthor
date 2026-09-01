// Compile from the repo root: typst compile --root . demo/<file>.typ
// Self-check: every rendered name must have the common width W*.
#import "../lib/equalauthors.typ": *
#set page(width: 20cm, height: auto)
#let names = (
  "Peter Waldert", "Benedikt Kantz", "Thomas Köhler",
  "Erik D. Demaine", "Martin L. Demaine",
)
#context {
  let W = optimal-width(names)
  for n in names {
    let m = measure(render(n, W)).width
    assert(calc.abs(m.pt() - W.pt()) < 0.01, message: n + ": " + repr(m) + " != " + repr(W))
    [#n: #m (target #W) \ ]
  }
  [OK]
}
