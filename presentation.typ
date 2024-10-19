#import "symbols.typ": *
#import "@preview/touying:0.5.2": *
#import themes.university: *
#import "@preview/cetz:0.2.2"
#import "@preview/fletcher:0.5.1" as fletcher: node, edge
#import "@preview/ctheorems:1.1.2": *
#import "@preview/numbly:0.1.0": numbly



#let disintegrates = "disintegrates"
#let generates = "generates"
#let given = "given"

// cetz and fletcher bindings for touying
#let cetz-canvas = touying-reducer.with(reduce: cetz.canvas, cover: cetz.draw.hide.with(bounds: true))
#let fletcher-diagram = touying-reducer.with(reduce: fletcher.diagram, cover: fletcher.hide)

// Theorems configuration by ctheorems
#show: thmrules.with(qed-symbol: $square$)

#let _thmargs = (inset:0pt,padding:(top:0pt,bottom:0pt))
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


// #let theorem = thmbox("theorem", "Theorem", inset:(x:0pt, top:0pt),padding:(top:0pt,bottom:0pt),base:none)
// #let lemma = thmbox("theorem", "Lemma", inset:(x:0pt, top:0pt),padding:(top:0pt,bottom:0pt), base:none)
// #let corollary = thmbox(
//   "theorem",
//   "Corollary",
//   base: none,
//   inset : 0pt,
//   padding:(top:0pt,bottom:0pt)
// )
// #let definition = thmbox("theorem", "Definition", inset: (x: 0em, top: 0em),padding:(top:0pt,bottom:0pt), base:none)
// #let conjecture = thmbox("theorem", "Conjecture", inset: (x: 0em, top: 0em),padding:(top:0pt,bottom:0pt), base:none)
// #let example = thmplain("example", "Example").with(numbering: none)
// #let proof = thmproof("proof", "Proof")

#let animations = true
// Animations On/Off
// #let animations = false
#show: university-theme.with(
  aspect-ratio: "16-9",
  // config-common(handout: true),
  config-info(
    title: [A Theory of Structural Independence],
    author: [Matthias G. Mayer],
    date: [2024-10-25],
    // institution: [],
    logo: none,
  ),
)




#set heading(numbering: numbly("{1}.", default: "1.1"))

#title-slide()

// == Outline <touying:hidden>

// #components.adaptive-columns(outline(title: none, indent: 1em))


#align(center)[#text(size:1.4em)[*A Theory of Structural Independence*]]
#align(center)[Matthias G. Mayer]
#text(size:0.9em)[_Abstract:
We will review the usage of Bayesian networks, $d$-separation
and causal discovery, and their limitations for making sense of structure in observed data distributions. We will highlight d-separation as the central object in classical causal discovery and present its generalization, "structural independence" as a combinatorial property of random variables on a product space.
The main theorem justifies this definition by showing the equivalence to
independence in all product probability distributions on the product space, generalizing soundness and completeness of $d$-separation._]

= Background

== Structure
Let $V$ be a set of variables and $PP$ a distributions over those.
What can we tell about the structure that the variables $V$ have?
(Assume finiteness for now)

// #set node(radius: 1em)
#pause


#table(columns: 2, stroke: none, column-gutter: 1em)[
#fletcher-diagram(
  node-stroke: .1em,
  node-fill: gradient.radial(white, blue.lighten(80%), center: (30%, 20%), radius: 80%),
  spacing: 2em,
  node((0,0), $V_1$, radius: 1em, name:<N1>),
  edge("-|>"),
  node((-1/2,1), $V_2$, radius: 1em, name:<N2>),
  edge("-|>"),
  node((0,2), $V_4$, radius: 1em, name:<N4>),
  node((1/2,1), $V_3$, radius: 1em, name:<N3>),
  edge(<N1>,<N3>,"-|>"),
  edge(<N3>,<N4>,"-|>"),
)
#pause
][
  #v(-15pt)
  #definition[
    Let $G=(V,E)$ be a directed acyclyc graph (DAG).
    #pause
    $PP$ is compatible with $G$ if the following holds:
    #pause
    // A bayesian network is a directed graph $G=(V,E)$
    // with a probability distribution $PP$ over $V$, s.t.
    for all $X,Y in V$, s.t. there is no path from $X$ to $Y$, we have $X indep_PP Y | PA(X)$.
    #pause
    // \
    Let $distributions(G)$ be the set of all $PP$ compatible with $G$.


    #only("6-7")[
    In this example: \
    $V_2 indep_PP V_3 | V_1$
    ]
    #only("7")[
    $quad quad quad V_4 indep_PP V_1 | V_2, V_3$
    ]

    #only("8")[
    Equivalently, for all $v = (v_X)_(X in V) in Val(V)$,
    $ PP(V=v) = product_(X in V) PP(X=v_X|PA(X)=v_PA(X)) $
    ]
  ]

  // #pause
  // Such a pair $(G,PP)$ is called bayesian network.

  // A directed graph without $PP$ is a qualitative bayesian network.  It characterizes admissible distributions.
]

#slide[

That means all $PP in distributions(G)$ arise as follows:
  
#figure[#fletcher-diagram(
  node-stroke: .1em,
  node-fill: gradient.radial(white, blue.lighten(80%), center: (30%, 20%), radius: 80%),
  spacing: 3em,
  node((0,0), $V_1$, radius: 1em, name:<N1>),
  edge("-|>"),
  node((-1/2,1), $V_2$, radius: 1em, name:<N2>),
  edge("-|>"),
  node((0,2), $V_4$, radius: 1em, name:<N4>),
  node((1/2,1), $V_3$, radius: 1em, name:<N3>),
  edge(<N1>,<N3>,"-|>"),
  edge(<N3>,<N4>,"-|>"),

  node((0.75,0), $PP(V_1 in dot| nothing)$, stroke: 0em, fill: white, name:<T1>),
  node((-1.30,1), $PP(V_2 in dot| V_1)$, stroke: 0em, fill: white, name:<T2>),
  node((1.30,1), $PP(V_3 in dot| V_1)$, stroke: 0em, fill: white, name:<T3>),
  node((0.75,2), $PP(V_4 in dot| V_2, V_3)$, stroke: 0em, fill: white, name:<T4>),
  
  edge(<T1>, <N1>, "-->"),
  edge(<T2>, <N2>, "-->"),
  edge(<T3>, <N3>, "-->"),
  edge(<T4>, <N4>, "-->"),
)
]
]



== $d$-separation

Given a DAG can we characterize all independencies which are implied by the assumptions on $PP in distributions(G)$?
#pause
There is a nice graphical criterion:
#pause

#definition[
  Given a directed graph $G$ and sets of nodes $X$,$Y$ and $Z$.
  $X$ and $Y$ are 
  #box(stroke: (bottom: 1pt), outset: (bottom: 2pt))[$d$-connected]
  given $Z$ if 
  there is a walk $W$ from a node in $X$ to a node in $Y$ s.t.
  $w in W$ is a collider w.r.t. $W$ if and only if $w in Z$.

  #pause
#fletcher-diagram(
  node-stroke: .1em,
  node-fill: gradient.radial(white, blue.lighten(80%), center: (30%, 20%), radius: 80%),
  spacing: 1em,
  edge((-3,0),<N1>,"--", label:$W_i$),
  node((0,0),radius:1em, name:<N1>),
  edge("-|>", label:$W_(i+1)$),
  node((3,0),radius:1em,name:<N2>),
  node((6,0),radius:1em, name:<N3>),
  edge(<N2>,"-|>",label:$W_(i+2)$),
  edge((9,0),<N3>,"--", label:$W_(i+3)$),
  node((3,0.8),[Collider], fill:none, stroke:none),
  (pause,),
  node((6,0.8),[#h(-90pt)$arrow.l$ iff in $Z$], fill:none, stroke:none),
)
#pause
 
  $X$ and $Y$ given $Z$ are 
  #box(stroke: (bottom: 1pt), outset: (bottom: 2pt))[$d$-separated]
  if they are not $d$-connected given $Z$.
]




#let diagram1(fill1,fill2,fill3,fill4,fill5,fill6,fill7, caption:[Blue nodes are $d$-connected given yellow node.]) = figure(supplement:none, caption:caption )[#fletcher-diagram(
  node-stroke: .1em,
  node-fill: gradient.radial(white, blue.lighten(80%), center: (30%, 20%), radius: 80%),
  spacing: 1em,
  node((-2,0), $V_1$, radius: 1em, name:<N1>,fill:fill1),
  edge("-|>"),
  node((-1,1), $V_2$, radius: 1em, name:<N2>,fill:fill2),
  node((2,0), $V_3$, radius: 1em, name:<N3>,fill:fill3),
  edge("-|>"),
  node((1,1), $V_4$, radius: 1em, name:<N4>,fill:fill4),
  edge("-|>"),
  node((0,2), $V_5$, radius: 1em, name:<N5>, fill:fill5),
  edge("-|>"),
  node((0,4), $V_6$, radius: 1em, name:<N6>, fill:fill6),
  edge(<N2>,<N5>,"-|>"),
  node((3,1), $V_7$, radius: 1em, name:<N7>, fill:fill7),
  edge(<N3>,<N7>,"-|>"),
)
]

// #[
#let nf = gradient.radial(white, blue.lighten(80%), center: (30%, 20%), radius: 80%)
#let cf = gradient.radial(yellow.lighten(80%),yellow, center: (30%, 20%), radius: 80%)
#let sf = gradient.radial(blue.lighten(80%), blue, center: (30%, 20%), radius: 80%)


#let nrepeat = 10
#if animations==false {
  nrepeat = 1
}

#slide(repeat: nrepeat, self => [
  #let (uncover, only, alternatives) = utils.methods(self)
  #let diaglist = (
    diagram1(nf,nf,nf,nf,nf,nf,nf,caption:[#h(-60pt) Example Graph]),
    // diagram1(nf,nf,nf,nf,nf,nf,nf,caption:[#h(-60pt) Example Graph]),
    diagram1(nf,sf,nf,sf,cf,nf,nf),
    diagram1(sf,nf,nf,sf,cf,nf,nf),
    diagram1(sf,nf,sf,nf,cf,nf,nf),
    diagram1(sf,nf,nf,nf,cf,nf,sf),
    diagram1(sf,nf,nf,nf,nf,cf,sf),
    diagram1(sf,cf,nf,nf,nf,cf,sf, caption:[Blue nodes are #text(red)[#underline[not]] $d$-connected given the yellow nodes, \ i.e. $d$-separated.]),
    diagram1(sf,cf,nf,nf,nf,nf,sf, caption:[Blue nodes are #text(red)[#underline[not]] $d$-connected given the yellow nodes, \ i.e. $d$-separated.]),
    diagram1(sf,nf,nf,nf,cf,nf,sf, caption:[Blue nodes are #text(red)[#underline[not]] $d$-connected given the yellow nodes, \ i.e. $d$-separated.]),
    diagram1(sf,nf,nf,cf,nf,nf,sf, caption:[Blue nodes are #text(red)[#underline[not]] $d$-connected given the yellow nodes, \ i.e. $d$-separated.]),
    diagram1(sf,nf,cf,nf,nf,nf,sf, caption:[Blue nodes are #text(red)[#underline[not]] $d$-connected given the yellow nodes, \ i.e. $d$-separated.]),
  )
  #diaglist.at(self.subslide, default:none)
  ])

#slide[
  We write $orth_d$ for the $d$-separation relation.
  #theorem[
    Let $X,Y,Z$ be set of nodes.
    
    $ X orth_d Y | Z <=>forall P in distributions(G) : X indep_P Y | Z. $
  ]

  This reveals that $d$-separation is a type of 'structural independence'.
  #pause

  #figure[
#fletcher-diagram(
  spacing:1em,
  node-outset:4pt,
  node((0,0),$G$,name:<G>),
  edge("->",label:$PP in distributions(G)$),
  node((3,0), $(G,PP)$,name:<GP>, outset:8pt),
  pause,

  node((0,1),$X orth_d Y | Z$,name:<d>),
  edge("->"),
  node((3,1),$X indep_PP Y | Z$,name:<p>),

  edge(<G>,<d>,"-->", label:""),
  edge(<GP>,<p>,"-->", label:""),
  
)
]
  

]


  
// #table(columns: 2, stroke: none, column-gutter: 1em)[
// ][
//   #definition[
//     $PP$ is compatible with a directed graph $G=(V,E)$ if
//     // A bayesian network is a directed graph $G=(V,E)$
//     // with a probability distribution $PP$ over $V$, s.t.
//     $X indep_PP Y | PA(X)$ for all $X,Y in V$, s.t. $X cancel(-->,stroke:#1.5pt) Y$.
//     Let $distributions(G)$ be the set of such $PP$.

//     Then it holds that
//     $ PP(V=v) = product_(X in V) PP(X=v_X|PA(X)=v_PA(X)) $
//   ]

//   Such a pair $(G,PP)$ is called bayesian network.

//   // A directed graph without $PP$ is a qualitative bayesian network.  It characterizes admissible distributions.
// ]

== Causal Discovery

We want to infer the structure of the graph given $PP$. \
#pause
Realizability assumption: $PP$ is compatible with a graph and
all inde-pendencies are characterized by $d$-separation. We say $PP$ is a perfect map.
// #pause
// #theorem[
// $X orth_d Y | Z <=> {P in distributions(G): X indep_P Y | Z}$ has interior.
// ]

#table(columns: 2, stroke: none, column-gutter: 1em)[
#fletcher-diagram(
  node-stroke: .1em,  
  node-fill: gradient.radial(white, blue.lighten(80%), center: (30%, 20%), radius: 80%),
  spacing: 2em,
  node((0,0), $V_1$, radius: 1em, name:<N1>),
  node((-1/2,1), $V_2$, radius: 1em, name:<N2>),
  node((0,2), $V_4$, radius: 1em, name:<N4>),
  node((1/2,1), $V_3$, radius: 1em, name:<N3>),
  edge(<N1>,<N3>,[?],"-|>"),
  edge(<N2>,<N3>,[?],"-|>"),
)
][
  #pause
  In a sense, we can see that this is not too strong an assumption.
  #pause
  #theorem[
  $X orth_d Y | Z <=> {P in distributions(G): X indep_P Y | Z}$ has interior.
  ]

  // In a graph, the set of $P$ where \
  // $X indep_P Y | Z$ holds contrary to $d$-separation is nowhere dense and closed.

  #pause
  It is known that it is impossible to infer the whole graph in general.
  The equivalence classes that you can infer are called _markov equivalence classes_.
  // #definition[
  //   A bayesian network is a directed graph $G=(V,E)$
  //   with a probability distribution $PP$ over $V$, s.t.
  //   $X indep Y | PA(X)$ for all $X,Y in V$, s.t. $X cancel(arrow,stroke:#1.5pt) Y$.
    
  //   It holds that
  //   $ PP(V=v) = product_(X in V) PP(X=v_X|PA(X)=v_PA(X)) $
  // ]

  // A directed graph without $PP$ is a qualitative bayesian network.  It characterizes admissible distributions.
]

#slide[
  For example, the following graphs have the same independencies:

  #figure[#table(columns:2,column-gutter: 2em,stroke:none)[
    #fletcher-diagram(
    node-stroke: .1em,  
    node-fill: gradient.radial(white, blue.lighten(80%), center: (30%, 20%), radius: 80%),
    spacing: 2em,
    node((0,0),$V_1$, radius:1em),
    edge("-|>"),
    node((1,0),$V_2$, radius:1em),
    edge("-|>"),
    node((2,0),$V_3$, radius:1em),
    )
  ][
    #fletcher-diagram(
    node-stroke: .1em,  
    node-fill: gradient.radial(white, blue.lighten(80%), center: (30%, 20%), radius: 80%),
    spacing: 2em,
    node((2,0),$V_3$, radius:1em),
    edge("-|>"),
    node((1,0),$V_2$, radius:1em),
    edge("-|>"),
    node((0,0),$V_1$, radius:1em),
    )
    ]
  ]

  namely, $V_1 orth_d V_3 | V_2$.

  #pause
  Or even simpler,
  #figure[#table(columns:2,column-gutter: 5em,stroke:none)[
    #fletcher-diagram(
    node-stroke: .1em,  
    node-fill: gradient.radial(white, blue.lighten(80%), center: (30%, 20%), radius: 80%),
    spacing: 2em,
    node((0,0),$V_1$, radius:1em),
    edge("-|>"),
    node((1,0),$V_2$, radius:1em),
    )
  ][
    #fletcher-diagram(
    node-stroke: .1em,  
    node-fill: gradient.radial(white, blue.lighten(80%), center: (30%, 20%), radius: 80%),
    spacing: 2em,
    node((1,0),$V_2$, radius:1em),
    edge("-|>"),
    node((0,0),$V_1$, radius:1em),
    )
    ]
  ]
  with no structural independencies.
]



#slide(repeat:8, self => [

But we only used the independencies between nodes!
#pause
There are many more potential independencies like
$V_1 indep (V_1+V_2)$.
#pause

We want to extend '$d$-separation' to arbitrary random variables on the graph,
so that we can infer more structure.

#pause


#if self.subslide <= 5 {
  figure[
  #fletcher-diagram(
      node-stroke: .1em,  
      node-fill: gradient.radial(white, blue.lighten(80%), center: (30%, 20%), radius: 80%),
      spacing: 1em,
      node((0,0),$V_1$, radius:1em),
      edge("-|>",shift:5pt, label:"?"),
      edge("<|-",shift:-5pt),
      node((2,0), $V_2$,radius:1em),
      node((4,0), $V_1 cancel(indep,stroke:#1.5pt) V_2$, stroke:none,fill:none),
      pause,
      node((1,1), $V_1 + V_2$,shape:fletcher.shapes.ellipse,extrude:10pt),
  
      node((4.3,1), $V_1 indep V_1 + V_2$, stroke:none,fill:none),
  )
  ]
} else if self.subslide == 6 {
  figure[
  #fletcher-diagram(
      node-stroke: .1em,  
      node-fill: gradient.radial(white, blue.lighten(80%), center: (30%, 20%), radius: 80%),
      spacing: 1em,
      node((0,0),$V_1$, radius:1em),
      edge("-|>"),
      node((2,0), $V_2$,radius:1em),
      node((4,0), $V_1 cancel(indep,stroke:#1.5pt) V_2$, stroke:none,fill:none),
      
      node((1,1), $V_1 + V_2$,shape:fletcher.shapes.ellipse,extrude:10pt),
      edge((2,0),"-|>"),
  
      node((4.3,1), $V_1 indep V_1 + V_2$, stroke:none,fill:none),
  )
  ]
} else {
  figure[
  #fletcher-diagram(
      node-stroke: .1em,  
      node-fill: gradient.radial(white, blue.lighten(80%), center: (30%, 20%), radius: 80%),
      spacing: 1em,
      node((0,0),$V_1$, radius:1em),
      edge("-|>"),
      node((2,0), $V_2$,radius:1em),
      node((4,0), $V_1 cancel(indep,stroke:#1.5pt) V_2$, stroke:none,fill:none),
      
      node((1,1), $V_1 + V_2$,shape:fletcher.shapes.ellipse,extrude:10pt,outset:10pt, fill:none, stroke:(dash:"dashed")),
      edge((2,0),"--|>"),
  
      node((4.3,1), $V_1 indep V_1 + V_2$, stroke:none,fill:none),
  )
  ]

  [
    #pause
    #pause
    #pause
    #pause
    Therefore there is value to be gained from a general account of structural independence.
    
  ]
}


])


// #pause
// 
// The product  $PP(V=v) = product_(X in V) PP(X=v_X|PA(X)=v_PA(X))$
// reveals a product space structure.
// One factor corresponding to $PP(X=x| PA(X)="pa")$ with fixed 'pa'.







// #[
= Structural Independence #h(-13pt)
// ]

== Setting

Let $I$ be an arbitrary index set.

#pause

$(Omega, AS) := Times.circle_(i in I) (Omega_i, AS_i)$

#pause
Reference measure: $PP = times.big_(i in I) PP_i$, where $PP_i in distributions (Omega_i)$

#pause
$distributionstimes (Omega) := {Times_(i in I) P_i << PP | forall i in I: P_i in distributions(Omega_i)}$.


#pause
Question: Can we characterize
$forall P in distributionstimes (Omega) : X indep_P Y | Z?
$
Independence is defined in the usual way as
$forall A in sigma(X), B in sigma(Y)  : P(A|Z)P(B|Z) = P(A,B|Z) "a.s."$

#pause
Technicalities: We assume that all $sigma$-algebras are complete.



== Definitions



#definition[Index-set function][We call a measurable mapping $J : Omega -> 2^I$ an index-set function.]

#pause

#definition[Generalized projection][
  #v(-12pt)
$ pi_J : Omega -> Union_(I_0 subset.eq I) Omega_(I_0); omega  |-> pi_J(omega)(omega) $
]


#let x-max = 5
#let y-max = 5

#let start = (
  cetz.draw.translate(x:0, y:-100),
  cetz.draw.scale(1.4),
)

#let basic = (
  cetz.draw.rect((-1,7.25),(6,5),fill:white,stroke:none),
  cetz.draw.rect((-1,-2.25),(6,0),fill:white,stroke:none),
  cetz.draw.rect((-1,-1),(0,6),fill:white,stroke:none),
  cetz.draw.rect((6.5,-1),(5,6),fill:white,stroke:none),
  cetz.draw.line((0, 0), (x-max+0.4, 0), mark: (end: ">")),
  cetz.draw.line((0, 0), (0, y-max+0.4), mark: (end: ">")),
  // Origin label
  cetz.draw.content((0, -0.5), [0]),
  cetz.draw.content((-0.5, 0), [0]),
  cetz.draw.content((-0.5, y-max), [1]),
  cetz.draw.content((x-max,-0.5), [1]),
  cetz.draw.line((0,y-max),(x-max,y-max)),
  cetz.draw.line((x-max,0),(x-max,y-max))
  
)

#let colors = (
rgb(173, 216, 230),  // Light Blue
rgb(135, 206, 235),  // Sky Blue
rgb(176, 224, 230),  // Powder Blue
rgb(175, 238, 238),  // Pale Turquoise
rgb(202, 225, 255),  // Light Steel Blue
)

// #let grid(n) = (
//   if n == 0 {
//     none
//   } else if n == 1 {
//     cetz.draw.grid((0,0),(1,1),grid:(x:0.1,y:1))
//   } else if n == 2 {
//     cetz.draw.grid((0,0),(1,1),grid:(x:1,y:0.1))
//   } else if n == 3 {
//     cetz.draw.grid((0,0),(1,1),grid:(x:0.1,y:0.1))
//   }
// )

#let covering = (
  cetz.draw.scale(x-max),
  cetz.draw.hobby(
    (0, 0),
    (0.4, 0.3),
    (0.7, 0.5),
    (1, 0.4),
    (1, 0),
    close: true,
    fill: colors.at(0)
  ),
  cetz.draw.hobby(
    (0, 0),
    (0.5, 0.3),
    (0.1, 0.7),
    (0, 0.6),
    close: true,
    fill: colors.at(1)
  ),
  cetz.draw.hobby(
    (0.3, 0.5),
    (1, 0.4),
    (1, 1),
    (0.2, 0.9),
    (0.2, 0.8),
    close: true,
    fill: colors.at(3)
  ),
  cetz.draw.hobby(
    (0, 0.6),
    (0.3, 0.7),
    (0.6, 0.8),
    (0.8, 0.9),
    (1, 1),
    (0, 1),
    close: true,
    fill: colors.at(4)
  ),
  cetz.draw.scale(1/x-max),
)
#slide(repeat: 4, self => [
#v(-30pt)
#if self.subslide==1 {
figure[
#cetz-canvas({
    start
    basic
    cetz.draw.content((2.5,-1.5),[$Omega = [0,1] times [0,1]$])
})]
} else if self.subslide == 2 {
figure[#cetz-canvas({
  start
  covering
  basic
  cetz.draw.content((2.5,-1.5),[$Omega = [0,1] times [0,1]$])
})]
} else if self.subslide == 3 {
figure[#cetz-canvas({
  start
  covering
  basic
  cetz.draw.content((2.5,-1.5),[$J:Omega->2^I$])
  cetz.draw.content((1.2,4.2),[$nothing$])
  cetz.draw.content((0.8,1.2),[${1}$])
  cetz.draw.content((3.8,0.8),[${2}$])
  cetz.draw.content((3.3,2.8),[${1,2}$])
})]
  
} else {
figure[#cetz-canvas({
  start
  covering
  basic
  cetz.draw.content((2.5,-1.5),[$sigma(pi_J)$])
  let step = 0.5
  let y1 = (0,0,0,0,0.4,1.5,1.47,1.4,1.45,1.63)
  let y2 = (0,2.97,3.2,3.5,3.71,3.84,4,4.27,4.5,4.68)
  for i in range(calc.min(y1.len(),y2.len())) {
  cetz.draw.line((step*i,y1.at(i)),(step*i,y2.at(i)))
  }
  
  let x1 = (0,2.08,2.37,2.5,1.94,1.5,1.25,1.5,3,4)
  let x2 = (0,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5)
  for i in range(calc.min(x1.len(),x2.len())) {
  cetz.draw.line((x1.at(i),step*i),(x2.at(i),step*i))
  }
  
  // cetz.draw.content((1.2,4.2),[$nothing$])
  // cetz.draw.content((0.8,1.2),[${1}$])
  // cetz.draw.content((3.8,0.8),[${2}$])
  // cetz.draw.content((3.3,2.8),[${1,2}$])
})]
}
])





#slide[
#definition[Disintegration][$J disintegrates Z$ iff
$ forall P in distributionstimes(Omega): pi_J indep_P pi_comp(J) | Z. $]

#pause
#definition[Generation][Let $J$ be a $Z ms$ index-set function.
$J$ generates $X$ given $Z$ if
$X$ is $pi_J ms$ and $J$ disintegrates $Z$#v(-100pt)
]
]


== Results


#hide("hello")#v(-46.5pt)
#lemma[
  There exists a minimal generating index-set function for $X$ given $Z$.
  Denote this minimal element by $history (X|Z)$. I.e.
  for any generating $J$, we have
  $history(X|Z) subset.eq J "a.s."$
]

#pause 
#definition[Structural independence][
  $ X orth Y | Z :<=> history(X|Z) sect history(Y|Z) = nothing "a.s." $ 
]
#pause

#theorem[
  $X orth Y | Z <=> forall P in distributionstimes (Omega) : X indep_P Y | Z
  $
]

#pause
#corollary[
  If $forall P in distributionstimes(Omega): X indep_P Y | Z$ then \
  $forall P  in distributionstimes (Omega) : pi_(history(X|Z)) indep_P
  pi_(history(Y|Z)) | Z$.
]

// #pause
// #lemma[If ${P in distributionstimes(Omega):X indep_P Y | Z}$ has interior, it equals $distributionstimes(Omega)$ ]

#v(-100pt)
#hide("hello")

== Compositional Semigraphoid

#counter("theorem").update(12)

#theorem[compositional semigraphoid axioms][
  #pause
  #let given = math.bar
  $
  &"1." quad&& X perp Y given Z <=> Y perp X given Z &"(symmetry)" \
  &"2."&& X perp (Y,W) given Z => X perp Y given Z  &#h(-100pt)"(decomposition)"\
  &"3."&& X perp (Y,W) given Z => X perp Y given (Z,W) &"(weak union)"\
  &"4."&& X perp Y given Z and X perp W given (Z,Y) =>
  X perp (Y,W) given Z & "(contraction)" \
  &&&"(Semigraphoid Axioms)"#pause \
  &"5."&& X perp Y given Z and X perp W given Z =>
  X perp (Y,W) given Z &"(composition)"\
  $
]

By composition, pairwise structural independence and structural independence are equivalent.


== Disintegration

The definition of disintegration is not satisfactory.
Can we characterize
$forall P in distributionstimes(Omega) : pi_J indep_P pi_comp(J) | Z$ without
a quantifier?

#pause

#lemma[
  $J$ disintegrates $Z$ iff $pi_J indep_PP pi_comp(J) | Z$.
]
#pause

#lemma[
  If $Omega$ is finite, then $J disintegrates Z$, if
  any atom $C in sigma(Z)$ fulfills.
  $C= pi_J (C) times pi_comp(J) (C)$. This is not true with $Omega$ infinite.
]

#pause

#lemma[
  If $J disintegrates Z$, then for $A in sigma(pi_J, Z), B in sigma(pi_comp(J),Z)$, with $A sect B = nothing$ there is $C in sigma(Z)$ s.t.
  $A subset.eq C$, $B subset.eq C^c$.
]
#pause

Interaction between ($pi_J,Z$) and $(pi_comp(J),Z)$ happens only through $Z$.


== Convergence

We can put a metric on sets modulo nullsets by
$d(A,B) = PP(A triangle.t B)$.

#pause

#lemma[
  $A_n -> nothing $ if and only if every subsequence has a subsequence s.t.
  $lim sup A_n = nothing "a.s."$
]

#pause



#conjecture[
  There is a sense of convergence of $sigma$-algebras that only depends on nullsets, s.t.
  $J$ disintegrates $Z$ iff there is a sequence of
  partitions $BS_n$ with rectangular parts, s.t.
  $sigma(BS_n) -> sigma(Z)$.
]












