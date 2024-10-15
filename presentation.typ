#import "symbols.typ": *
#import "@preview/touying:0.5.2": *
#import themes.university: *
#import "@preview/cetz:0.2.2"
#import "@preview/fletcher:0.5.1" as fletcher: node, edge
#import "@preview/ctheorems:1.1.2": *
#import "@preview/numbly:0.1.0": numbly

// Animations On/Off
#let pause=[]


#let disintegrates = "disintegrates"
#let generates = "generates"
#let given = "given"

// cetz and fletcher bindings for touying
#let cetz-canvas = touying-reducer.with(reduce: cetz.canvas, cover: cetz.draw.hide.with(bounds: true))
#let fletcher-diagram = touying-reducer.with(reduce: fletcher.diagram, cover: fletcher.hide)

// Theorems configuration by ctheorems
#show: thmrules.with(qed-symbol: $square$)
#let theorem = thmbox("theorem", "Theorem", inset:(x:0pt, top:0pt),padding:(top:0pt,bottom:0pt), base:none)
#let lemma = thmbox("theorem", "Lemma", inset:(x:0pt, top:0pt),padding:(top:0pt,bottom:0pt), base:none)
#let corollary = thmbox(
  "theorem",
  "Corollary",
  base: none,
  inset : 0pt,
  padding:(top:0pt,bottom:0pt)
)
#let definition = thmbox("theorem", "Definition", inset: (x: 0em, top: 0em),padding:(top:0pt,bottom:0pt), base:none)
#let conjecture = thmbox("theorem", "Conjecture", inset: (x: 0em, top: 0em),padding:(top:0pt,bottom:0pt), base:none)
#let example = thmplain("example", "Example").with(numbering: none)
#let proof = thmproof("proof", "Proof")

#show: university-theme.with(
  aspect-ratio: "16-9",
  // config-common(handout: true),
  config-info(
    title: [A Theory of Structural Independence],
    subtitle: [#hide[h]],
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


_
Abstract:
I present a quick review of the usage of Bayesian networks, d-separation
and causal discovery, and their limitations for making sense of structure in observed data distributions. I highlight d-separation as the central object in classical causal discovery and present its generalization, 'structural independence' as a combinatorial property on product spaces.
The main theorem states that its definition is justified. More precisely, 
this combinatorial property is characterized as independence in all product probability distributions on the product space, generalizing soundness and completeness of $d$-separation.
_


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
  #definition[
    $PP$ is compatible with a directed graph $G=(V,E)$ if
    // A bayesian network is a directed graph $G=(V,E)$
    // with a probability distribution $PP$ over $V$, s.t.
    $X indep_PP Y | PA(X)$ for all $X,Y in V$, s.t. $X cancel(-->,stroke:#1.5pt) Y$.
    Let $distributions(G)$ be the set of such $PP$.

    Then it holds that
    $ PP(V=v) = product_(X in V) PP(X=v_X|PA(X)=v_PA(X)) $
  ]

  Such a pair $(G,PP)$ is called bayesian network.

  // A directed graph without $PP$ is a qualitative bayesian network.  It characterizes admissible distributions.
]

== $d$-separation

#definition[
  Given a directed graph $G$ and sets of nodes $X$,$Y$ and $Z$.
  $X$ and $Y$ are $d$-connected given $Z$ if 
  there is a walk $W$ from a node in $X$ to a node in $Y$ s.t.
  $w in W$ is a collider if and only if $w in Z$.

  #pause
#fletcher-diagram(
  node-stroke: .1em,
  node-fill: gradient.radial(white, blue.lighten(80%), center: (30%, 20%), radius: 80%),
  spacing: 1em,
  node((0,0),radius:1em),
  edge("-|>"),
  node((2,0),[\ \  \ Collider],radius:1em),
  node((4,0),radius:1em),
  edge((2,0),"-|>")
)
#pause
 \
 \
 
  $X$ and $Y$ given $Z$ are $d$-separated if they are not $d$-connected given $Z$.
]




#let diagram1(fill1,fill2,fill3,fill4,fill5,fill6,fill7, caption:[Blue nodes are $d$-connected given yellow node]) = figure(supplement:none, caption:caption )[#fletcher-diagram(
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

#[
#let nf = gradient.radial(white, blue.lighten(80%), center: (30%, 20%), radius: 80%)
#let cf = gradient.radial(yellow.lighten(80%),yellow, center: (30%, 20%), radius: 80%)
#let sf = gradient.radial(blue.lighten(80%), blue, center: (30%, 20%), radius: 80%)

#slide(repeat: 6, self => [
  #let (uncover, only, alternatives) = utils.methods(self)
  #let diaglist = (
    diagram1(nf,nf,nf,nf,nf,nf,nf,caption:[#h(-60pt) Example Graph]),
    diagram1(nf,sf,nf,sf,cf,nf,nf),
    diagram1(sf,nf,nf,sf,cf,nf,nf),
    diagram1(sf,nf,sf,nf,nf,cf,nf),
    diagram1(sf,nf,nf,nf,cf,nf,sf),
    diagram1(sf,nf,nf,nf,nf,cf,sf),
    diagram1(sf,cf,nf,nf,nf,cf,sf, caption:[Blue nodes are #text(red)[#underline[not]] $d$-connected given the yellow nodes. \ I.e. $d$-separated.]),
  )
  #diaglist.at(self.subslide)
  ])
]

#slide[
  #theorem[
    Let $X,Y,Z$ be set of nodes. Then
    $X$ and $Y$ are $d$-separated given $Z$ if and only if
    $forall P in distributions(G) : X indep_P Y | Z$.

    Furthermore, we have this if and only if ${P in distributions(G): X indep_P Y | Z}$ has interior.
  ]


  $d$-separation is a criterion based solely the graph that tells us the independencies in all compatible distribution.
  
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

== Inference

We want to infer the structure of the graph given $PP$. \
#pause
Realizability assumption: $PP$ is compatible with a graph and
all inde-pendencies are characterized by $d$-separation. We say $PP$ is a perfect map.
#pause

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
  In a graph, the set of $P$ where \
  $X indep_P Y | Z$ holds contrary to $d$-separation is nowhere dense and closed.

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



== Towards Structural Independence

But we only used the independencies between nodes!
#pause
There are many more independencies like
$X indep (X+Y)$.
#pause

We want to extend '$d$-separation' to arbitrary random variables on the graph,
so that we can infer more structure.

Via the product  $PP(V=v) = product_(X in V) PP(X=v_X|PA(X)=v_PA(X))$,
we can reduce to a simple product probability space.
One factor corresponding to $PP(X=x| PA(X)="pa")$ with fixed 'pa'.







#[
= Structural Independence
]

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

Technicalities: We assume that all $sigma$-algebras are complete.



==  Definitions



#definition[Index-set function][We call a measurable mapping $J : Omega -> 2^I$ an index-set function.]

#pause

#definition[Generalized projection][ \
$ pi_J : Omega -> Union_(I_0 subset.eq I) Omega_(I_0); omega  |-> pi_J(omega)(omega) $
]

#pause
#definition[Disintegration][$J disintegrates Z$ iff \
$ forall P in distributionstimes(Omega): pi_J indep_P pi_comp(J) | Z. $]

// ==
#definition[Generation][Let $J$ be a $Z ms$ index-set function.
$J$ generates $X$ given $Z$ if
$X$ is $pi_J ms$ and $J$ disintegrates $Z$
]


== Results
#lemma[
  There exists a minimal generating index-set function for $X$ given $Z$.
  Denote this minimal element by $history (X|Z)$. I.e.
  for any generating $J$, we have
  $history(X|Z) subset.eq J "a.s."$
]

#definition[Structural independence][
  $ X orth Y | Z :<=> history(X|Z) sect history(Y|Z) = nothing "a.s." $ 
]
#pause

#theorem[
  $X orth Y | Z <=> forall P in distributionstimes (Omega) : X indep_P Y | Z
  $
]

#corollary[
  If $forall P in distributionstimes(Omega): X indep_P Y | Z$ then \
  $forall P  in distributionstimes (Omega) : pi_(history(X|Z)) indep_P
  pi_(history(Y|Z)) | Z$.
]
#pause
#lemma[If ${P in distributionstimes(Omega):X indep_P Y | Z}$ has interior, it equals $distributionstimes(Omega)$ ]


== Compositional Semigraphoid


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












