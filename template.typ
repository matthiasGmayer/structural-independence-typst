#import "@preview/ctheorems:1.1.2": *

#import "symbols.typ": *

#let showrules(body) = {
  show: thmrules.with(qed-symbol: $square$)
  set par(justify: true)
  set heading(numbering: "1.1 ")
  set text(font: "New Computer Modern", lang: "en")
  set page(numbering: "1")
  set align(left)
  
  show ref: it => {
    let eq = math.equation
    let el = it.element
    if el != none and el.func() == eq {
      // Override equation references.
      link(el.location(),numbering(
        el.numbering,
        ..counter(eq).at(el.location())
      ))
    } else {
      // Other references as usual.
      it
    }
  }
  
  body
  
}

#let _thmargs = (inset:(left:0.25em,bottom:0em),padding:(top:0pt,bottom:0pt),base:"heading",
// fill:rgb(0,0,0,000),
)
#let _thmbox(str) = thmbox("theorem",str,.._thmargs)
#let theorem = _thmbox("Theorem")
#let definition = _thmbox("Definition")
#let exercise = _thmbox("Exercise")
#let lemma = _thmbox("Lemma")
#let remark = _thmbox("Remark")
#let example = _thmbox("Example")
#let corollary = _thmbox("Corollary")
#let conjecture = _thmbox("Conjecture")
#let notation = _thmbox("Notation")
#let observation = _thmbox("Observation")
#let custombox(str) = _thmbox(str)

// #let _proofargs = (inset:(left:0.25em),padding:(top:0pt,bottom:0pt),base:"heading")
#let _proofargs = _thmargs
#let proof = thmproof("proof","Proof",.._proofargs)


