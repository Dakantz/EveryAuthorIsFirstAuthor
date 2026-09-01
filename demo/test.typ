// Compile from the repo root: typst compile --root . demo/<file>.typ
#import "../lib/equalauthors.typ": *
#set page(width: 12cm, height: auto, margin: 1cm)
#set text(14pt)
#let names = (
  "Peter Waldert", "Benedikt Kantz", "Thomas Köhler",
  "Erik D. Demaine", "Martin L. Demaine",
)
*Stacked (all should be equal width):*
#eqa-authors-stacked(names)
#v(1em)
*Superimposed:*
#eqa-authors(names)
#v(1em)
#context [W\* = #optimal-width(names)]
#v(1em)
*From a BibTeX-style name list:*
#eqa-list("Erik D. Demaine and Martin L. Demaine")
