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
#let distributionstimes=[$triangle.t^(#h(-0.25em)times)$#h(-4pt)]
#let indep = math.scripts(math.class("relation")[
  #move(dy:0.045em)[#scale(origin: bottom, y:140%)[#sym.tack.t.double]]
])
#let orth = math.scripts(math.perp)

#let history = math.cal("H")
#let disintegrates = math.times.div
#let generates = math.tack

#let Union = math.union.big
#let Sect = math.sect.big
#let Times = math.times.big
#let And = math.and.big
#let Or = math.or.big
