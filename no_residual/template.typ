#import "@preview/ctheorems:1.1.3": *

#import "symbols.typ": *

#let showrules(body) = {
  set page(numbering: "1")
  set par(justify: true)
  set heading(numbering: "1.1 ")
  set text(font: "New Computer Modern", lang: "en")
  set align(left)
  // set par.line(numbering:"1")
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
  show: thmrules.with(qed-symbol: $square$)
  
  body
  
}
#let lb = linebreak(justify: true)

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



#let arkheion(
  title: "",
  abstract: [],
  keywords: (),
  authors: (),
  date: none,
  MSC: none,
  body,
) = {
  // Set the document's basic properties.
  set document(author: authors.map(a => a.name), title: title)
  set page(
    margin: (left: 25mm, right: 25mm, top: 25mm, bottom: 30mm),
    numbering: "1",
    number-align: center,
  )
  set text(font: "New Computer Modern", lang: "en")
  show math.equation: set text(weight: 400)
  show math.equation: set block(spacing: 0.65em)
  set math.equation(numbering: "(1)")
  set heading(numbering: "1.1")

  // Set run-in subheadings, starting at level 4.
  show heading: it => {
    // H1 and H2
    if it.level == 1 {
      pad(
        bottom: 10pt,
        it
      )
    }
    else if it.level == 2 {
      pad(
        bottom: 8pt,
        it
      )
    }
    else if it.level > 3 {
      text(11pt, weight: "bold", it.body + " ")
    } else {
      it
    }
  }

  line(length: 100%, stroke: 2pt)
  // Title row.
  pad(
    bottom: 4pt,
    top: 4pt,
    align(center)[
      #block(text(weight: 500, 1.75em, title))
      #v(1em, weak: true)
    ]
  )
  line(length: 100%, stroke: 2pt)

  // Author information.
  pad(
    top: 0.5em,
    x: 2em,
    grid(
      columns: (1fr,) * calc.min(3, authors.len()),
      gutter: 1em,
      ..authors.map(author => align(center)[
        #if author.keys().contains("orcid") {
          link("http://orcid.org/" + author.orcid)[
            #pad(bottom: -8pt,
              grid(
                columns: (8pt, auto, 8pt),
                rows: 10pt,
                [],
                [*#author.name*],
                [
                  #pad(left: 4pt, top: -4pt, image("orcid.svg", width: 8pt))
                ]
              )
            )
          ]
        } else {
          grid(
            columns: (auto),
            rows: 2pt,
            [*#author.name*],
          )
        }
        #author.email \
        #author.affiliation
      ]),
    ),
  )

  align(center)[#date]

  // Abstract.
  pad(
    x: 3em,
    top: 1em,
    bottom: 0.4em,
    align(center)[
      #heading(
        outlined: false,
        numbering: none,
        text(0.85em, smallcaps[Abstract]),
      )
      #set par(justify: true)
      #set text(hyphenate: false)

      #align(left)[
      #abstract
      
      #{
  // Keywords
  if keywords.len() > 0 {
      [*Keywords:* ] + keywords.map(str).join("; ")
  }
  if MSC != none {
      [\ *MSC Subject Classification:* #MSC] 
  }
}
]
    ],
  )

  // Main body.
  set par(justify: true)
  set text(hyphenate: false)

  body
}

#let arkheion-appendices(body) = {
  counter(heading).update(0)
  counter("appendices").update(1)

  set heading(
    numbering: (..nums) => {
      let vals = nums.pos()
      let value = "ABCDEFGHIJ".at(vals.at(0) - 1)
      if vals.len() == 1 {
        return "APPENDIX " + value
      }
      else {
        return value + "." + nums.pos().slice(1).map(str).join(".")
      }
    }
  );
  [#pagebreak() #body]
}