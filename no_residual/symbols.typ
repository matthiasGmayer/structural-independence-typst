#let AS = math.cal("A")
#let BS = math.cal("B")
#let CS = math.cal("C")
#let DS = math.cal("D")
#let NS = math.cal("N")
#let ms = text(weight:"regular")[#h(0pt)-measurable]
#let Lip = "Lip"
#let loc = "loc"
#let Val = "Val"
#let PA = "PA"
#let radiv(P,Q) = $(dif #P)/(dif #Q)$
#let angles(a,b) = $angle.l #a, #b angle.r$
#let duality = angles
#let supp = "supp"
#let comp = math.overline
#let distributions=[$triangle.t$#h(0pt)]
#let distributionstimes=[$triangle.t^(#h(-0.25em)times)$]
#let distributionstimes2(..args)=[$triangle.t^(#h(-0.25em)times 2)_(#args.pos().join(","))$]
#let indep = math.scripts(math.class("relation")[
  #move(dy:0.045em)[#scale(origin: bottom, y:140%)[#sym.tack.t.double]]
])
#let orth = math.scripts(math.perp)
#let Orth = scale(110%)[#math.scripts(math.perp)]

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
#let __placeastext = text(size:0.5em)[a.s.]
// #let Asunion = math.class("large",$Union#place(dx:-0.9em,dy:-0.8em)[#__placeastext]$)
// #let Assect = math.class("large",$Sect#place(dx:0pt)[#__placeastext]$)
#let subsetaseq = math.class("relation",$subset.eq#place(dx:-0.7em,dy:-0.8em)[#__placeastext]$)
#let supsetaseq = math.class("relation",$supset.eq#place(dx:-0.7em,dy:-0.8em)[#__placeastext]$)
#let aseq = math.class("relation",$=#place(dx:-0.7em,dy:-0.6em)[#__placeastext]$)
#let asneq = math.class("relation",$!=#place(dx:-0.7em,dy:-0.6em)[#__placeastext]$)
#let asgt = math.class("relation",$>#place(dx:-0.7em,dy:-0.7em)[#__placeastext]$)
#let asge = math.class("relation",$>=#place(dx:-0.7em,dy:-0.8em)[#__placeastext]$)
#let aslt = math.class("relation",$<#place(dx:-0.7em,dy:-0.7em)[#__placeastext]$)
#let asle = math.class("relation",$<=#place(dx:-0.7em,dy:-0.8em)[#__placeastext]$)

#let res = $*$
// #let Sectas = math.class("unary",[#h(0.1em)#text(size:0.4em)[a.s.]#h(-0.75em)#math.sect.big])
// #let Sectas = math.accent(Sect,[a.s.])
