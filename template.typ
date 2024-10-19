#import "@preview/ctheorems:1.1.2": *

#include "symbols.typ"

#let showrules(body) = {
  show: thmrules.with(qed-symbol: $square$)
  set par(justify: true)
  set heading(numbering: "1.1 ")
  set text(font: "New Computer Modern", lang: "en")
  set page(numbering: "1")
  set align(left)
  body
}

#let _thmargs = (inset:0pt,padding:(top:0pt,bottom:0pt),base:"heading")
#let _thmbox(str) = thmbox("theorem",str,.._thmargs)
#let theorem = _thmbox("Theorem")
#let definition = _thmbox("Definition")
#let exercise = _thmbox("Exercise")
#let lemma = _thmbox("Lemma")
#let remark = _thmbox("Remark")
#let example = _thmbox("Example")
#let corollary = _thmbox("Corollary")
#let conjecture = _thmbox("Conjecture")
#let observation = _thmbox("Observation")

#let proof = thmproof("proof","Proof",.._thmargs)


