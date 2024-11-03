#let AS = math.cal("A")
#let BS = math.cal("B")
#let CS = math.cal("C")
#let DS = math.cal("D")
#let NS = math.cal("N")
#let ms = [#h(0pt)-measurable]
#let Lip = "Lip"
#let loc = "loc"
#let Val = "Val"
#let PA = "PA"
#let angles(a,b) = $angle.l #a, #b angle.r$
#let duality = angles
#let supp = "supp"
#let comp = math.overline
#let distributions=[$triangle.t$#h(0pt)]
#let distributionstimes=[$triangle.t^(#h(-0.25em)times)$#h(-0.0em)]
#let distributionstimes2(i)=[$triangle.t^(#h(-0.25em)times 2)_#i$#h(-0.0em)]
#let indep = math.scripts(math.class("relation")[
  #move(dy:0.045em)[#scale(origin: bottom, y:140%)[#sym.tack.t.double]]
])
#let orth = math.scripts(math.perp)

#let history = math.cal("H")
#let irrel = math.cal("I")
#let disintegrates = math.times.div
#let generates = math.tack

#let Union = math.union.big
#let Sect = math.sect.big
#let Times = math.times.big
#let And = math.and.big
#let Or = math.or.big

#let powerset = math.frak("P")

#let astext = text(size:0.7em,baseline: 0.00em)[a.s.]
#let _astext = text(size:0.7em,baseline: 0.20em)[a.s.#h(-0.1em)]
#let __astext = text(size:0.7em,baseline: 0.90em)[#h(0.0em)a.s.#h(-0.1em)]
#let subsetaseq = $subset.eq^#_astext$
#let supsetaseq = $supset.eq^#_astext$
#let aseq = $=^#_astext$
#let asneq = $!=^#__astext$
#let asgt = $>^#_astext$
#let asge = $>=^#_astext$
#let aslt = $<^#_astext$
#let asle = $<=^#_astext$
// #let Sectas = math.class("unary",[#h(0.1em)#text(size:0.4em)[a.s.]#h(-0.75em)#math.sect.big])
// #let Sectas = math.accent(Sect,[a.s.])
