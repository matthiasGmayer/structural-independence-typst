#import "template.typ": *
#show: showrules 

#show "sigma algebra": it => [$sigma$-algebra]
#show "sect stable": it => [$sect$-stable]

#let radiv(P,Q) = $(dif #P)/(dif #Q)$


#align(center)[
  #text(size:2em)[A Theory of Structural Independence] \
  \
  Matthias Georg Mayer
]

\

#emph[
  #lorem(100)
]


= Introduction

#let ground = $Omega$
#let groundalg = $AS$
#let groundprob = $PP$

// #let factor = $Omega$
// #let factoralg = $AS$
// #let factorprob = $PP$

// 
We first review these basic definitions.
#definition[random element][
  Let $(Omega,AS)$.
  A random element on $Omega$ is any measurable mapping
  $X : Omega -> Omega'$, where $(Omega',AS')$ is any measurable space.
  We let $Val(X) = (Omega',AS')$ denote the codomain of $X$.
]

#definition[conditional expectation, conditional probability][
  Let $X : Omega -> RR$ be a random variable on a probability space $(Omega, AS, PP)$
  and $CS$ be a sub-sigma algebra of $AS$.
  A conditional expectation $EE(X|CS) : Omega -> RR$ is a $CS$-measurable random variable
  that fulfills
  $integral_C EE(X|CS) dif PP = integral_C X dif PP$ for all $C in CS$.
  Conditional expectations exist and coincide $PP$ almost surely, so we can talk about the conditional expectation $EE(X|CS)$.
  The conditional probability of $A in AS$ given $CS$ is given by
  $PP(A|CS) := EE(1_A|CS)$.
  Let $Z$ be a random element on $Omega$, then we write
  $EE(X|Z) := EE(X|sigma(Z))$ and $PP(A|Z) := PP(A|sigma(Z))$.
]

#definition[conditional independence][
  Let $PP$ be a probability measure on a measurable space $(Omega,AS)$.
  Let $A,B in AS$ and $CS$ a sub sigma algebra of $AS$.
  We say that $A$ is independent of $B$ given $CS$ w.r.t. $PP$, if
  $PP(A|CS)PP(B|CS) aseq PP(A,B|CS)$.
  We write $A indep_PP B | CS$.
  We extend conditional independence to set systems.
  Let $AS_1,AS_2 subset.eq AS$.
  Then $AS_1 indep_PP AS_2 | CS :<=> forall A in AS_1, B in AS_2 : A indep_PP B | CS$.
  We also allow the use of random elements.
  Let $X,Y,Z$ be random elements on $Omega$.
  Then $X indep_PP Y | Z :<=> sigma(X) indep_PP sigma(Y) | sigma(Z)$.
  Unconditional independence is written as
  $X indep_PP Y :<=> X indep_PP Y | nothing$.
  We use the word 'independence' to refer to both conditional and unconditional independence depending on the context.
  // We say that $X$ is independent of $Y$ given $Z$ w.r.t. $P$, if for all
  // $A in sigma(X)$ and $B in sigma(Y)$, we have
  // $P(A|Z) P(B|Z) aseq P(A,B|Z)$.
  // We write
  // $
  // X indep_P Y | Z.
  // $
]

Let $I$ be an arbitrary index set.
Let $(ground,groundalg, groundprob)$ be a probability space.
// For $i in I$, let $(factor_i, factoralg_i)$ be measurable space and $U_i : ground -> factor_i$ a random element, s.t.
// $(U_i)_(i in I)$ is an independent family of random elements.
Let $(U_i)_(i in I)$ be an independent family of random elements.

*In the following* $X,Y$ and $Z$ will always refer to random elements on $ground$.


We ask and answer the question: "Which independencies in $PP$ are implied by $U_i$ being independent?"
To formalize this, we let
$
distributionstimes := {P : AS' -> RR |& P "is a probability measure,"\
&(U_i)_(i in I) "is an independent family w.r.t." P \
&"and" P "is absolutely continuous w.r.t." PP " and vice versa"}
$

and ask when it is the case that
$forall P in distributionstimes: X indep_P Y | Z$.
More specifically, we want to characterize this statement uniformly over all choices of $X,Y$ and $Z$ without quantifying over $distributionstimes$.
We want to provide a testable criterion.

From standard probability we can immediately conclude a collection of unconditional independencies.
For $J subset.eq I$, let $U_J$ denote the family $(U_i)_(i in J)$.
#lemma[
  Let $J,K subset.eq I$ be disjoint.
  Let $sigma(X) subset.eq sigma(U_J)$ and
  $sigma(Y) subset.eq sigma(U_K)$.
  Then $X indep_P Y$ for all $P in distributionstimes$.
] <lem:independence_trivial>
#proof[
  Let $A in sigma(X)$ and $B in sigma(Y)$.
  By assumption $A in sigma(U_J)$ and $B in sigma(U_K)$.
  $A indep_P B$ follows immediately because $sigma(U_J) indep_P sigma(U_K)$,
  since $U$ is an independent family w.r.t. $P$.
]
However, it is apriori not clear, that these are the only independencies that follow.
We want to see, whether $X indep_P Y$ for all $P in distributionstimes$ implies that
there are $J, K subset.eq I$ disjoint, s.t.
$sigma(X) subset.eq sigma(U_J)$ and
$sigma(Y) subset.eq sigma(U_K)$.
We will later see that this is indeed the case, whenever $X$ and $Y$ are not constant (since then the independence is trivial).

The interesting theory begins once we condition on a random element $Z$.
When do we have the conditional independence $X indep_P Y | Z$ for all $P in distributionstimes$?
To answer this question, we want to generalize from @lem:independence_trivial,
where we began to characterize this with dependence on disjoint background variables.
Conditional on $Z$, we want to carry over this idea and allow this dependence to vary with $Z$.
Suppose that ${Z=z}$ is not a $P$-nullset.
For each $z in Val(Z)$, we want to assign $J_z,K_z subset.eq I$, s.t.
$sigma(X|_{Z=z}) subset.eq sigma(U_J_z|_{Z=z})$
and
$sigma(Y|_{Z=z}) subset.eq sigma(U_K_z|_{Z=z})$.
However, even if $J_z$ and $K_z$ are disjoint, we cannot conclude independence.
We require a niceness condition on the selection of $J_z$.
More specifically, we need the condition $U_J_z|_{Z=z} indep_P U_comp(J_z)|_{Z=z} | {Z=z}$.
Clearly, using this condition and the same argumentation as in @lem:independence_trivial, we can then conclude that $X|_{Z=z} indep_P Y|_{Z=z} | {Z=z}$.

@sec:finite_theory gives a brief overview of the finite theory,
where these ideas are given a formal form.
Once we start developing the general theory, conditioning on sets is no longer possible.
We need to choose $J_z$ over all $z$ almost surely simulatenously. To do this we introduce random index sets and random families in @sec:random_index_sets.
With these tools in hand, we can give a precursory statement of the fundamental theorem of structural independence at the start of @sec:construction.
The fundamental theorem characterizes all independencies that are implied by an independent family
through the $Z$ dependant random index sets.
In this section we continue to construct these random index sets, called (conditional) history of $X$ given $Z$ and written $history(X|Z) : Omega -> powerset(I)$.
In @sec:fundamental_theorem, we examine the properties of the history to prove the
fundamental theorem of structural independence.


= Overview of the finite theory
<sec:finite_theory>

We follow the exposition of @FFS closely.

The following definitions are valid throughout this section.

Let $I$ be a finite index set.
Let $(Omega,AS)$ be a measurable space.
Let $(U_i)_(i in I)$ be a family of random elements on $Omega$ with finite codomain.
let
$
distributionstimes := {P : AS -> RR |& P "is a probability measure" \
& "and" (U_i)_(i in I) "is an independent family w.r.t." P}
$

Note that here, in the finite case, it is not necessary to have a reference measure $PP$ s.t.
$P$ is absolutely continuous w.r.t. $PP$. This is because we can choose a
distribution $PP$ s.t. the pushforward $PP_U$ is the uniform distribution, s.t. all distributions on $Val(U)$ are absolutely continuous w.r.t. $PP_U$.

We will now introduce the history and state the fundamental theorem without proofs.
Proofs follow immediately from the general theory. Direct proofs can be read in @FFS,
where everything is stated in the canonical space w.r.t. $U$ and without measure theory.


First, we introduce generation, a sufficient condition for $X$ to be determined by $pi_J$
given a set $C$.
#definition[generation, history][
  Let $X$ be a random element and $C in AS$.
  We say that $J subset.eq I$ generates $X$ given $C$, if
  $sigma(X|_C) subset.eq sigma(U_J|_C)$ and
  $U(C) = U_J (C) times U_comp(J) (C)$.
  \
  The history of $X$ given $C$, is the subset-wise smallest $J subset.eq I$ that generates $X$ given $C$.
  The history of $X$ given $C$ is written $history(X|C)$ and exists.
  For $A in AS$, we also write $history(A|C):=history(1_A|C)$.
] <def:finite_generation>

The rectangle condition $U(C) = U_J (C) times U_comp(J) (C)$ is essential
for the existence of the history and the correctness of the fundamental theorem.
This condition reflects the requirement of independence of $U_J$ and $U_comp(J)$ given $C$.
Indeed, if this is the cases, the pushforward of U under $P$ disintegrates into a product
$P(U in dot|C) = P(U_J in dot | C) times P(U_comp(J) in dot | C)$.
If $P$ is chosen s.t. $P_U$ has no nontrivial nullsets, the support of
$PP(U in dot|C)$ is $U(C)$, while similarly,
$supp PP(U_J in dot|C) = U_J (C)$ and $supp PP(U_J in dot|C) = U_comp(J) (C)$.
Now the product structure of $PP(U in dot|C)$ implies that the supports have to form a cartesian product. This is exactly $U(C) = U_J (C) times U_comp(J) (C)$.

#theorem[Fundamental Theorem][
  Let $X,Y$ and $Z$ be random elements with finite codomain.
  Then 
  $
  forall P in distributionstimes: X indep_P Y | Z
  <=>
  forall z in Val(Z): history(X|{Z=z}) sect history(Y|{Z=z}) = nothing.
  $
] <thm:finite_fundamental_theorem>

We can therefore define structural independence.
#definition[structural independence][
  Let $X,Y$ and $Z$ be random elements with finite codomain.
  Then $X$ and $Y$ are structurally independent given $Z$, 
  if their conditional histories are disjoint.
  More precisely, we set
  $
  X orth Y | Z :<=> forall z in Val(Z): history(X|{Z=z}) sect history(X|{Z=z}) = nothing.
  $
]












// when $I$ is finite and all random elements take values in a finite space,

// Intuitively, it seems likely that these are the only independencies we can conclude,
// since we used the independence of $U$ in the standard.



= Random index sets and random families
<sec:random_index_sets>

In this section let $I$ be an index set.
Let $powerset(I)$ denote the powerset of $I$.

#definition[random index set][
  A random index set in $I$ on a measurable space $(Omega,AS)$ is a measurable mapping
  $Omega -> powerset(I)$. Here, the powerset of $I$ is a measurable space endowed with the smallest sigma algebra that contains ${K subset.eq I: i in K}$ for all $i in I$.
  This corresponds to the sigma algebra induced by the canonical bijection between $powerset(I)$ and the product measurable space ${0,1}^I$.
] <def:random_index_set>
#lemma[
  Let $J : Omega -> powerset(I)$.
  Then $J$ is measurable, i.e. a random index set, if and only if
  ${i in J} := {omega in Omega: i in J(omega)}$ is measurable for all $i in I$.
] <lem:random_index_set_measurability>
#proof[
  Note that $J^(-1){K subset.eq I : i in K} = {omega in Omega: i in J(omega)}$.
  The statement now follows directly from the definition of a random index set (@def:random_index_set).
]

#definition[
  Let $X=(X_i)_(i in I)$ be a family of random elements.
  Let $J subset.eq I$. Then we denote by
  $X_J := (X_i)_(i in J)$, the restriction of this family to $J$.
  Canonically, $X_J$ is a random element by 
  $(X_i)_(i in J) (omega) = (X_i (omega))_(i in J)$.
]


#definition[random family][
  Let $(X_i)_(i in I)$ be a family of random elements on $Omega$.
  Let $J : Omega -> powerset (I)$ be a random index set.
  Then we define the random family $X_J$ by the evaluation
  $X_J (omega) = (X_J(omega)) (omega)$.
  The type signature of $X_J$ is given by
  $
  X_J : Omega -> union.big_(K subset.eq I) Val(X_K).
  $
  where $Union_(K subset.eq I) Val(X_K)$ is endowed with the smallest sigma algebra
  that contains
  ${x in Val(X_K) : K subset.eq I, i in K "and" x_i in B}$ for all $i in I$ and measurable $B subset.eq Val(X_i)$.
] <def:random_family>

#lemma[
  The random family $X_J$ defined in @def:random_family is measurable and
  $sigma(X_J) = sigma({i in J, X_i in B} :i in I, B in Val(X_i))$.
] <lem:random_family_generator>
#proof[
  Let $i in I$, $B subset.eq Val(X_i)$ measurable, and
  $A = {x in Val(X_K) : K subset.eq I, i in K "and" x_i in B}$.
  Since sets of this form generate the sigma algebra of $Val(X_J)$ by definition,
  it suffices to show that
  $X_J^(-1) (A)$ is measurable.
  Because $J$ is a random index set, ${i in J}$ is measurable.
  and because $X_i$ is a random element, ${X_i in B}$ is measurable.
  Now
  $X_J^(-1) (A) = {omega in Omega : X_J (omega) in A}
  = {omega in Omega: i in J(omega) "and" X_i (omega) in B} = {i in J, X_i in B}$, which is measurable.
]

#corollary[
  Let $X_J$ be the random family defined in @def:random_family. Then $sigma(X_J)$ is generated by 
  the sect stable system
  $
  {{K subset.eq J, X_K in B} :
  K subset.eq I "finite and" B = Times_(k in K) B_k, "where" B_k subset.eq Val(X_k) "measurable"}.
  $
] <cor:sigma_stable_generator_random_family>
#proof[Cleary, this is system is sect stable. It generates $sigma(X_J)$ by @lem:random_family_generator]

// \
We now want to see how random families behave w.r.t. set operations on their
random index sets.
// \
#notation[
  For $J subset.eq I$ we denote its complement by $comp(J) := I without J$.
  When working with random index sets, set operations and relations are understood pointwise.
  Specifically, for random index sets $J$ and $K$, we set
  $comp(J) (omega) := comp(J(omega))$, $(J sect K) (omega) := J(omega) sect K(omega)$ and
  $(J union K) (omega) := J (omega) union K (omega)$, as well as
  $J subset.eq K :<=> forall omega : J(omega) subset.eq K(omega)$.
]


*In the following*, let $(X_i)_(i in I)$ be a family of random elements.

#lemma[
  Let $J$ be a random index set.
  Then $sigma(J) subset.eq sigma(X_J)$.
] <lem:random_index_set_measurable_in_projection>
#proof[
  For $B = Val(X_i)$, the set ${omega in Omega: i in J(omega) "and" X_i (omega) in B}$ is measurable and equal to
  ${i in J}$.
]

#lemma[
  Let $J$ and $K$ be random index sets, s.t. $J subset.eq K$.
  Then $sigma(X_J) subset.eq sigma(X_K,J)$.
] <lem:random_index_set_subset>
#proof[
  Let $i in I$ and $B subset.eq  Val(X_i)$ measurable.
  By @lem:random_family_generator, it suffices to show that ${i in J, X_i in B}$
  is contained in $sigma(X_K, J)$, since sets of this form generate $sigma(X_J)$.
  Now, since $J subset.eq K$, we have
  ${i in J, X_i in B} = underbrace({i in J}, in sigma(J)) sect underbrace({i in K,X_i in B}, in sigma(X_K)) in sigma(X_K, J)$.
]

#example[
  In @lem:random_index_set_subset,
  it is essential to include the random index set $J$ in $sigma(X_K,J)$.
  Let $I={1,2}$, $Omega = {1,2,3}^2$, and for $i in I$ let $X_i = pi_i : Omega -> {1,2,3}$ be the projection
  on the $i$'th coordinate.
  Define random index sets $J$ and $K$ by
  #align(center)[#table(columns:2,stroke:none,column-gutter: 2em)[
  $
  J(omega) := cases({1} &"if" omega_2 = 1, nothing &"else")
  $
  ][
  $
  K(omega) := cases({1} &"if" omega_2 in {1,2}, nothing &"else")
  $]
  ]
  Clearly, $J subset.eq K$.
  Then by @lem:random_index_set_measurable_in_projection,
  $pi_2^(-1){1} = {2 in J}$ is $sigma(X_J) ms$.
  But it is not contained in
  $sigma(X_K) = sigma({a} times {1,2} : a in {1,2,3})$.
]

#corollary[
  Let $J$ and $K$ be random index sets.
  Then
  $sigma(X_(J sect K)) subset.eq sigma(X_J, J sect K) sect sigma(X_K, J sect K)$
]
#proof[
  follows immediately from @lem:random_index_set_subset.
]
The other direction is not true in general.
#example[
  We have $sigma(X_J) sect sigma(X_K) subset.eq.not sigma(X_(J sect K), J, K)$ in general.
  Let $I = {1,2}, Omega ={1,2}^2$ and for $i in I$ let $X_i = pi_i : Omega -> {1,2}$ be the projection on the $i$'th coordinate.
  Define random index sets $J$ and $K$ by
  #align(center)[#table(columns:2,stroke:none,column-gutter: 2em)[
  $
  J(omega) := cases({1} &"if" omega_1 = omega_2, {2} &"else")
  $
  ][
  $
  K(omega) := cases({2} &"if" omega_1 = omega_2, {1} &"else")
  $]
  ]
  Then clearly, $sigma(X_J) = sigma(X_K) = powerset(Omega)$,
  but since $J sect K = nothing$, $sigma(X_(J sect K),J, K) = sigma(J,K) =sigma({(1,1),(2,2)})$.
  Therefore, $sigma(X_J) sect sigma(X_K) subset.eq.not sigma(X_(J sect K),J,K)$.
] <ex:index_set_intersection>

#remark[
  In @ex:index_set_intersection, $comp(J)=K$. Furthermore $sigma(X_J) sect sigma(X_comp(J)) = powerset(Omega)$.
  Therefore we do not have $sigma(X_J) sect sigma(X_comp(J)) = nothing$ in general.
]


#lemma[
  Let $J$ and $K$ be random index sets.
  Then $sigma(X_J, X_K) = sigma(X_(J union K), J, K)$.
] <lem:random_index_set_union>
#proof[
  '$subset.eq$' By symmetry it suffices to show that $sigma(X_J) subset.eq sigma(X_(J union K),J, K)$. This follows directly from @lem:random_index_set_subset.
  '$supset.eq$': Let $i in I$ and $B subset.eq Val(X_i)$ be measurable.
  By @lem:random_index_set_measurable_in_projection, we have
  $sigma(J,K) subset.eq sigma(X_J,X_K)$.
  Therefore, by @lem:random_family_generator, it suffices to show that ${i in J union K, X_i in B}$
  is contained in $sigma(X_J,X_K)$.
  Again, by @lem:random_family_generator,
  ${i in J union K, X_i in B} = {i in J, X_i in B} union {i in K, X_i in B} in sigma(X_J,X_K)$.
]





= Construction of the History
<sec:construction>


Let $(Omega,AS,PP)$ be a complete probability space.
Let $I$ be an arbitrary index set.
Let $(U_i)_(i in I)$ be a family of random elements.
$
distributionstimes := {P : AS' -> RR |& P "is a probability measure,"\
&(U_i)_(i in I) "is an independent family w.r.t." P \
&"and" P "is absolutely continuous w.r.t." PP "and vice versa"}
$

*In the following* $X,Y$ and $Z$ will be arbitrary random elements.
#notation[completed sigma algebras, almost surely][
  Let $NS = {A in AS: PP(A) = 0}$ be the nullsets w.r.t. $PP$.
  For ease of notation, we will assume all sigma algebras to be complete w.r.t. the reference measure $PP$.
  $AS$ is already assumed to be complete and whenever
  we write $sigma(dot)$, we mean the generated sigma algebra, completed w.r.t. $PP$,
  i.e. $sigma(dot) = sigma(dot,NS)$.
  This behaves well, since for any set systems $BS_1,BS_2$, we have
  $sigma(BS_1) subset.eq sigma(BS_2) => sigma(BS_1,NS) subset.eq sigma(BS_2,NS)$.
  Therefore all results proven in @sec:random_index_sets about sigma algebras carry over.
  // Note thate this behaves well with
  Furthermore, we consider the set relation up to nullsets. For clarity, we will keep writing 'a.s.'
  on top of the relations.
]
#definition[almost surely relations for sets and random index sets][
  For $A,B in AS$,
  $A subsetaseq  B :<=> B without A in NS$ and
  $A aseq B :<=> A subsetaseq B  and B subsetaseq A$.
  Moreover, extending this to random index sets $J$ and $K$, we have
  $J subsetaseq K :<=> forall i in I: {i in J} subsetaseq {i in K} $,
  and
  $J aseq K :<=> J subsetaseq K and K subsetaseq J$.
]
#lemma[
  Let $J$ and $K$ be random index sets, s.t. $J aseq K$, then
  $sigma(J) aseq sigma(K)$.
  Moreover, if $J aseq nothing$, then $sigma(J) = sigma(nothing)$.
] <lem:as_random_index_set_sigma_algebra_subset>
#proof[
  By definition, ${i in J} aseq {i in K}$ for all $i in I$.
  These sets and $NS$ generate $sigma(J)$ and $sigma(K)$ respectively.
  If $K=nothing$, then ${i in K} in NS$.
]
#remark[
  Note that $J subsetaseq K$ is only equivalent to $J(omega) subset.eq K(omega)$ for $PP$-a.e. $omega$,
  whenever $I$ is at most countable.
  Indeed, complications arise immediately, since ${J subset.eq K}$ is apriori not measurable if $I$ is uncountable. Take $I=[0,1]$ and $Omega=[0,1]^I$ endowed with the product sigma algebra.
  Let $PP=Times_(i in I) lambda|_([0,1])$ be the product of uniform distributions.
  Let $AS$ be the completed product sigma algebra on $Omega$.
  Let $(U_i)_(i in I) = (pi_i)_(i in I)$ be the coordinate projections.
  Define $J(omega) = {omega_0}$.
  Clearly, $J$ is measurable by @lem:random_index_set_measurability, since for $i in I$,
  ${i in J} = {pi_0 = i}$.
  Define $K(omega) = nothing$.
  Note that for any $i in I$, ${i in J}$ is a nullset,
  therefore $J subsetaseq K$. But the set
  ${J subset.eq.not K} = Omega$.
] <rem:aseq_random_indexset>


We can now use random index sets to describe the dependance on $U$ as $Z$ varies.
Let $Sigma$ denote the set of all sub sigma algebras of $AS$.

Our goal is to construct a map we will call history, $history(dot|dot) : Sigma times Sigma -> powerset(I)^Omega$
that measures the dependence on $U$ of a sigma algebra given another sigma algebra with a random index set.
We write $history(X|Z)$ for $history(sigma(X)|sigma(Z))$.
We now give a list of desiderata that will be shown to completely determine $history$ almost surely in an appropriate sense.

#custombox("Desiderata")([
+ $history(X|Z)$ is a $sigma(Z) ms$ random index set.
+ Almost sure disjointess of the histories characterizes independence for all product distributions in $distributionstimes$. 
  More precisely,
  $forall P in distributionstimes: X indep_P Y | Z <=> history(X|Z) sect history(Y|Z) aseq nothing.
  $
+ Let $J$ be a random index set.
  Whenever $U_J$ depends on $U$, it should depend on it through $J$.
  Morally, we require that for a.e. $omega in {J != nothing}$ we have
  $J(omega) subset.eq history(X|Z) (omega)$.
  As we have seen, ${J != nothing}$ and ${J subset.eq history(X|Z)}$ are not measurable in general,
  so formalizing this requires some care.
  // For a.e. $omega in Omega$, $history(U_i|Z)(omega) != nothing => i in history(U_i|Z)(omega)$.
  // for any $i,j in I$, we require for a.e. $omega in {j in J}$, that
  // $i in history(U_J|Z)(omega) => j in history(U_J|Z)(omega)$.
+ Monotonicity: if $sigma(X) subset.eq sigma(Y)$ then $history(X|Z) subsetaseq history(Y|Z)$.
+ Given $Z$, $Z$ should not depend on $U$: $history(Z|Z) aseq nothing$.
]) <des:history>

Our construction will mimic the finite case (@def:finite_generation).
Specifically, we first define what it means for a random indexset $J$
to be sufficient for $X$ given $Z$.
Then we show that there exists an almost surely minimal and unique sufficient $J$.

#lemma[
  Let $S$ be an index set. For $s in S$, let $A_s in AS$.
  Then there exists an almost surely unique and minimal set $B$, s.t.
  $forall s in S: A_s subsetaseq B$.
  Furthermore, there exists a countable set $S_0 subset.eq S$, s.t.
  $Union_(s in S_0) A_s aseq B$.
] <lem:as_union_exists>
#proof[
  The proof is trivial if $S$ is countable.
  We will directly construct $S_0 = {s_n : n in NN}$ as a sequence and show
  that
  $Union_(n in NN) A_s_n$ can be chosen to be $B$.
  We inductively define $s_n$ by a sequence.
  For $n = 1$, let $s_n in S$ be arbitrary.
  Let $n in NN$ and $s_n$ be defined.
  Set $B_n := Union_(m=1)^n A_s_m$ and $p_n := sup_(s in S) PP(A_s without B_n)$.
  Choose $s_(n+1) in S$, s.t. $PP(A_(s_(n+1)) without B_n) <= p_n - 1/n$,
  // Finally, set $S_0 := Union_(n in NN) S_0^n$ and
  // Set $A = Sect_(n in NN_0) A_s_n$ and $S_0 = {s_n:n in NN_n}$.
  We now prove the required properties.
  + $forall s in S: A_s subsetaseq B$: Let $s in S$. We need to show $PP(A_s without B) = 0$.
    Assume that $PP(A_s without B) = p>0$.
    Then $PP(A_s without B_n) >= PP(A_s without B) = p$ because $B_n subset.eq B$.
    By the choice of $s_n$, $PP(A_s_n without B_n) >= PP (A_s without B_n) - 1/n >= p - 1/n$.
    But then with $B_0 = nothing$,
    $1 >= PP(B) = PP(Union_(n in NN) A_s_n without B_(n-1)) = sum_(n in NN) PP(A_s_n without B_(n-1)) = oo$,
    a contradiction.
  + Minimality and uniqueness:
    Let $C in AS$, s.t. $forall s in S: A_s subsetaseq C$.
    Then clearly, $B = Union_(n in NN) A_s_n subsetaseq C$.
    Therefore, if $C$ is minimal too, i.e. $C subsetaseq B$, we have $B aseq C$.
    #qedhere
]
#definition[almost sure union and intersection][
  We call the set $B$ from @lem:as_union_exists the almost sure union of
  the family $(A_s)_(s in S)$ and write
  $Union^astext_(s in S) A_s := A$.
  We define the almost sure intersection of $(A_s)_(s in S)$
  by $Sect^astext_(s in S) A_s := (Union^astext_(s in S) A_s^c)^c$.
  It then follows immediately
  that the almost sure intersection is the almost surely unique, maximal set that fulfills
  $Sect^astext_(s in S) A_s subsetaseq A_s$ for all $s in S$.
] <def:as_union>

We have seen in @rem:aseq_random_indexset, that for random index sets $J$ and $K$ in an uncountable index set $I$,
the set ${J=K}$ is not measurable.
Nonetheless, we can define an appropriate generalizing.

#definition[
  ${J aseq K} := Sect^astext_(i in I) {i in J sect K}$.
]


#definition[disintegration, generation][
  Let $J$ be a $sigma(Z) ms$ random index set.
  We say that $J$ disintegrates $Z$, if
  $forall P in distributionstimes: U_J indep_P U_comp(J) | Z$.
  We say that $J$ generates $X$ given $Z$, if
  $sigma(X) subset.eq sigma(U_J,Z,AS|_{I aseq J})$ and $J$ disintegrates $Z$.
] <def:generation>

// To see that a minimal generating set exists, we 

#lemma[
  Let $J$ be a random index set s.t. $J aseq nothing$.
  $sigma(U_J) = sigma(nothing)$.
] <lem:as_empty_random_index_set>
#proof[
  Let $i in I$ and $B subset.eq Val(X_i)$ measurable.
  It suffices to show that $PP{i in J, X_i in B} = 0$,
  since sets of this form and the nullsets $NS$ generate $sigma(U_J)$
  and
  then $sigma(U_J) subset.eq sigma(NS) = sigma(nothing)$.
  This follows immediately by $J aseq nothing$.
]

#lemma[
  Let $J$ and $K$ be random index sets s.t. $J aseq K$. Then $sigma(U_J) = sigma(U_K)$.
] <lem:aseq_random_indexsets_eq_random_family>
#proof[
  Clearly, $J sect K aseq J$.
  We can therefore, w.l.o.g. assume
  $J subset.eq K$.
  By @lem:random_index_set_union,
  $sigma(U_J, U_(K without J)) = sigma(U_K, J, K without J)$.
  By @lem:as_empty_random_index_set,
  $sigma(U_(K without J)) = sigma(nothing)$.
  By @lem:as_random_index_set_sigma_algebra_subset,
  $sigma(J) = sigma(K)$
  and $= sigma(K without J) = sigma(nothing)$.
  Therefore, $sigma(U_J) = sigma(U_K)$.
]

#corollary[
  Let $J$ and $K$ be random index sets s.t. $J aseq K$.
  Then $J "generates" X | Z$ if and only if $K "generates" X | Z$.
]
#proof[
  Follows immediately from @lem:aseq_random_indexsets_eq_random_family,
  because @def:generation only uses $J$ through $sigma(U_J)$, $sigma(U_comp(J))$ and $AS|_{J aseq I}$.
  Clearly, $sigma(AS|_{J aseq I}) = sigma(AS|_{K aseq I})$.
]


To prove that a minimal generating index set exists, we apply Zorn's lemma to show existence
and use stability under intersections for uniqueness. We start with the latter.
#lemma[
  Let $J$ and $K$ be random index sets that disintegrate $Z$.
  Then $J sect K$ disintegrate $Z$.
] <lem:disintegration_intersection>
#proof[
  We let $(J_1,J_2,J_3,J_4) := (J sect K,J without K, K without J, K)$
  and $J_(i j) := J_i union J_j$.
  By assumption,
  $J_12 = J$ and $J_13 = K$ disintegrate $Z$.
  We need to show that $J_1 = J sect K$ disintegrates $Z$.


  
  // From @def:generation, it follows immediately, that $comp(J)$ disintegrates $Z$.
  Let $P in distributionstimes$.
  It suffices to show that the family $(U_J_i)_(i=1)^4$ is independent given $Z$.
  This is equivalent to the conditional independence of
  $(U_J_i,Z)_(i=1)^4$
  By @lem:random_index_set_union and the $sigma(Z)$-measurability of $J$ and $K$, we have
  $sigma(U_J_1, U_J_2, Z) = sigma(U_J_12, Z)$
  and likewise for other choices of indices.
  By disintegration w.r.t $J_12$ and $J_13$, we have

  #set math.equation(numbering: "(1)")
  $
  (U_J_12,Z) indep_P (U_J_34,Z) | Z \ 
  $ <eq:first_independence>
  $
  (U_J_13,Z) indep_P (U_J_24,Z) | Z \
  $ <eq:second_independence>
  // $U_J indep_P comp(U_J) | Z$.
  // Because we condition on $Z$, this is equivalent to
  // $(U_J,Z) indep_P (comp(U_J),Z) | Z$.

  For $i in {1,...,4}$ let $A_i in sigma(U_J_i,Z)$.
  It suffices to show
  $A_1 indep_P A_2 sect A_3 sect A_4 | Z$, since sets of this form are a sect stable system
  that generates $sigma(U_234,Z)$.

  Now clearly,
  $P(Sect_(i=1)^4 A_i|Z) =^#[@eq:first_independence]P(A_1 sect A_2 | Z) P(A_3 sect A_4 | Z)
  =^#[@eq:second_independence] product_(i = 1)^4 P(A_i|Z)$.
]

// #lemma[
//   //   Let $(S,<)$ be a totally ordered set.
//   // Let $(J_s)_(s in S)$ be a family of random index sets that disintegrate $Z$.
//   // s.t. $forall s,t in S : s < t => J_s subset.eq J_t$.
//   Let $(J_n)_(n in NN)$ be a sequence of disintegrating random index sets
//   s.t. $J_n supset.eq J_(n+1)$.
//   Then $Sect_(n in NN) J_n$ disintegrates $X$ given $Z$.
// ] <lem:disintegration_decreasing_sequence>
// #proof[
//   Let $J := Sect_(n in NN) J_n$.
//   Let $P in distributionstimes$.
//   We need to show that $U_J indep_P U_comp(J) | Z$.
//   For this let $A in sigma(U_J,Z)$ and $n in NN$ and $B in sigma(U_comp(J_n), Z)$.
//   Since $Union_(n in NN) sigma(U_J_n,Z)$ is a sect stable system that generates $sigma(U_comp(J),Z)$,
//   this implies the required independence.
//   But clearly, $A in sigma(U_(J_n),Z)$, so that $A indep_P B | Z$ follows because $J_n$ disintegrates $Z$.
// ]

#lemma[
  Let $J$ and $K$ be $sigma(Z) ms$ random index sets.
  Then
  $sigma(U_J,Z,AS|_{J aseq I}) sect sigma(U_K,Z,AS|_{K aseq I})
  =
  sigma(U_J,Z,AS|_{J sect K aseq I}) sect sigma(U_K,Z,AS|_{J sect K aseq I})$.
] <lem:underlying_sigma_algebra_sect>
#proof[
  Since '$supset.eq$' is trivial, it suffices to show '$subset.eq$'.

  
  Let $A_1 = {J sect K aseq I}, A_2 = {J aseq I} without A_1, A_3 = {K aseq I} without A_1$ and $A_4 = Omega without Union_(n=1)^3 A_i$.
  Clearly, any $sigma(Z) ms$ sub sigma algebras $AS_1$ and $AS_2$ fulfill
  $AS_1 subset.eq AS_2 <=> forall i in {1,...,4} : AS_1|_A_i subset.eq AS_2|_(A_i)$.
  The statement now follows directly by comparing on all $A_i$.

  On $A_1$ both sides are equal to $AS|_A_1$
  On $A_2$ $K subsetaseq I$, so that by @def:as_union_random_index_set,
  $sigma(U_J,Z)|_A_2 subset.eq sigma(U_K,Z)|_A_2 = sigma(U,Z)|_A_2$.
  Similarly for $A_3$.
  $A_4$ is trivial.
]

#lemma[
  Let $J$ and $K$ generate $X$ given $Z$.
  Then $J sect K$ generates $X$ given $Z$.
] <lem:generation_sect>
#proof[
  By @lem:disintegration_intersection, $J sect K$ disintegrates $X$ given $Z$.
  By the definition of generations, we have
  $sigma(X) subset.eq sigma(U_J, Z, AS|_{J aseq I}) sect sigma(U_K, Z, AS|_{K aseq I})$
  It suffices to show that the right hand side is a subset of
  $sigma(U_(J sect K), Z, AS|_{J sect K aseq I})$.

  Let $A in sigma(U_J, Z, AS|_{J aseq I}) sect sigma(U_K, Z, AS|_{K aseq I})$.
  Clearly, ${J sect K aseq I} aseq {J aseq I} sect {K aseq I}$.
  
  By @lem:underlying_sigma_algebra_sect,
  $A in sigma(U_J, Z, AS|_{J sect K aseq I}) sect sigma(U_K, Z, AS|_{J sect K aseq I})$.

  Since $U_(J sect K) indep_PP U_(J without K) | Z$, we have
  $PP(U_(J without K) in dot | Z) = PP(U_(J without K) in dot | U_(J sect K), Z)$.
  Since the same holds true for $K without J$, we get
  $U_(J without K) indep_PP U_(K without J) | U_(J sect K) , Z $ and therefore
  $U_(J) indep_PP U_(K) | U_(J sect K), Z$ from @lem:random_index_set_subset and the $sigma(Z)$-measurability of the involved random index sets.

  Since $AS|_{J sect K aseq I}$ is the underlying sigma algebra restricted to a measurable set, we can condition on
  it and only gain independencies.
  Therefore
  $U_J indep_PP U_K | U_(J sect K), Z, AS|_{J sect K aseq I}$
  and
  $sigma(U_J,Z,AS|_{J sect K aseq I}) indep_PP sigma(U_K,Z,AS|_{J sect K aseq I}) | U_(J sect K), Z, AS|_{J sect K aseq I}$.

  Therefore
  $A indep_PP A | U_(J sect K) , Z, AS|_{J sect K aseq I}$.
  This implies $A in sigma(U_(J sect K), Z, AS|_{J sect K aseq I})$.
]

To apply Zorn's lemma, we want to use the almost sure intersection for random index sets.

#definition[
  Let $S$ be an index set and
  $(J_s)_(s in S)$ a family of random index sets.
  Then we define the almost sure union by
  ${i in Union^astext_(s in S) J_s} = Union^astext_(s in S) {i in J_s}$.
  Similarly, the almost sure intersection is defined by
  ${i in Sect^astext_(s in S) J_s} = Sect^astext_(s in S) {i in J_s}$.
  These definitions determine the corresponding random index set almost surely uniquely.
] <def:as_union_random_index_set>

#lemma[
  Let $frak(I)$ be a set of index functions s.t.
  for any totally ordered set $(S,<=)$ and any random index set family $(J_s)_(s in S)$ with
  $forall s,t in S: s <= t => J_s subsetaseq J_t$, we have
  $Sect^astext_(s in S) J_s in frak(I)$.
  Then there exists a almost surely subset wise minimal element in $frak(I)$.
  Furthermore, if $J,K in frak(I)$ implies $J sect K in frak(I)$, this element is almost surely unique and is given by
  $Sect^astext frak(I)$.
] <lem:random_index_set_zorn>
#proof[
  For existence, apply Zorn's lemma to the random index sets modulo almost sure equality where
  the ordering is given by $J <= K :<=> J subsetaseq K$.
  For unqiueness, assume that $J$ and $K$ are minimizers.
  If $J aseq K$ does not hold, $J sect K aseq J$ does not hold and therefore 
  $J$ is not a minimizer. Similarly, if $Sect^astext frak(I) in.not frak(I)$.
]

It remains to show that generation is closed under chains.

#lemma[
  Let $S$ be an index set.
  Let $(J_s)_(s in S)$ be a family of $sigma(Z) ms$ random index sets.
  Let $J = Union^astext_(s in S) J_s$.
  Then $sigma(U_J, Z) = sigma(U_J_s, Z : s in S)$.
] <lem:as_union_random_index_set>
#proof[
  '$supset.eq$':
  Follows immediately by @lem:random_index_set_subset
  and the $sigma(Z)$-measurability of all involved random index sets.
  \
  '$subset.eq$':
  Let $i in I$ and $B subset.eq Val(X_i)$ measurable.
  It suffices to show that ${i in J, X_i in B} in sigma(U_J_s, Z : s in S)$,
  since these sets generate $sigma(U_J)$.
  By @def:as_union_random_index_set and @lem:as_union_exists,
  there is a countable subset $S_0 subset.eq S$, s.t.
  ${i in J} aseq Union_(s in S_0) {i in J_s}$.
  Now clearly,
  ${i in J, X_i in B} aseq Union_(s in S_0) {i in J_s, X_i in B} in sigma(U_J_s, Z : s in S)$.
]

#lemma[
  Let $(S,<=)$ be a totally ordered set.
  Let $(J_s)_(s in S)$ be a family of random index sets that disintegrate $Z$.
  s.t. $forall s,t in S : s <= t => J_s subsetaseq J_t$.
  Then $Sect^astext_(s in S) J_s$ disintegrates $Z.$
] <lem:disintegration_chain>
#proof[
  Let $J := Sect^astext_(s in S) J_s$.
  Let $P in distributionstimes$.
  We need to show that $U_J indep_P U_comp(J) | Z$.
  For this let $A in sigma(U_J,Z)$ and $s in S$ and $B in sigma(U_comp(J_s), Z)$.
  Since $comp(J) = Union^astext_(s in S) comp(J_s)$ and $Union_(s in S) sigma(U_comp(J_s),Z)$ is a sect stable system that generates $sigma(U_comp(J),Z)$ (@lem:as_union_random_index_set),
  it suffices to show $A indep_P B | Z$ for all such $B$.
  Now clearly, $A in sigma(U_(J_s),Z)$ implies $A indep_P B | Z$ because $J_s$ disintegrates $Z$.
]


#lemma[
  Let $(S,<=)$ be a totally ordered set.
  Let $(J_s)_(s in S)$ be a family of $sigma(Z) ms$ random index sets
  s.t. $forall s, t in S: s <= t => J_s subsetaseq J_t$.
  Let $J := Sect^astext_(s in S) J_s$.
  Then
  $Sect_(s in S) sigma(U_J_s, Z, AS|_{J_s aseq I}) = Sect_(s in S) sigma(U_J_s, Z, AS|_{J aseq I})$.
] <lem:underlying_sigma_algebra_chain>
#proof[
  '$supset.eq$': Follows from $sigma(AS|_J) subset.eq sigma(AS|_J_s)$.
  \
  '$subset.eq$':
  // Let $S_0 subset.eq S$ countable, s.t. $J = $
  @lem:as_union_exists, there is $S_0 subset.eq S$ countable,
  s.t. $Sect^astext_(s in S_0) {J_s aseq I} aseq {J aseq I}$.
  W.l.o.g. $S_0 = {s_n : n in NN}$.
  // Set $A_0 = Omega$ and for $n in NN$, $A_n = A_(n-1) without {J_n aseq I}$.
  // Set $A_(oo) = Omega without Union_(n in NN) A_n$.
  Set $A_n = Union_(m = n)^oo {J_s_n aseq I}^c $.
  Set $A_* = {J aseq I}$.
  
  Let $B in Sect_(s in S) sigma(U_J_s, Z, A|_{J_s aseq I})$.
  Clearly, it suffices to show that
  $B sect A_n in Sect_(s in S) sigma(U_J_s,Z, AS|_{AS aseq J})$
  for all $n in NN union {*}$.
  
  Let $n in NN$.
  Then $B sect A_n in Sect_(s in S:s <= s_(n+1)) sigma(U_J_s, Z, AS|_{J_s aseq I})|_A_n$.
  Now since $A_n sect {J_s aseq I} aseq nothing$ for all $s <= s_(n+1)$.
  $sigma(U_J_s, Z, AS|_{J_s aseq I})|_A_n = sigma(U_J_s, Z)|_A_n subset.eq sigma(U_J_s,Z,AS|_{J aseq I})$.
  This shows the claim for all $n in NN$.
  \
  Now let $n = *$.
  Then $B sect A_n = B sect {J aseq I} in sigma(AS|_{J aseq I}) subset.eq sigma(U_J_s,Z,AS|_{J aseq I})$.
]

#lemma[
  Let $(S,<=)$ be a totally ordered set.
  Let $(J_s)_(s in S)$ be a family of random index sets that generate $X$ given $Z$.
  s.t. $forall s,t in S : s <= t => J_s subsetaseq J_t$.
  Then $Sect^astext_(s in S) J$ generates $Z$ given $X$
] <lem:generation_chain>

#proof[
  Let $J := Sect^astext_(s in S) J_s$.
  By @lem:disintegration_chain, $J$ disintegrates $X$ given $Z$, therefore
  $U_J indep_PP U_comp(J) | Z$.
  By the definition of generation and @lem:underlying_sigma_algebra_chain,
  we have $sigma(X) subset.eq Sect_(s in S) sigma(U_J_s, Z, AS|_{J_s aseq I}) = Sect_(s in S) sigma(U_J_s, Z, AS|_{J aseq I})$.
  It suffices to show that the latter is almost surely equal to
  $sigma(U_J, Z, AS|_{J aseq I})$.
  
  Let $s in S$, then by @lem:as_union_random_index_set
  $sigma(U_comp(J_s),Z) subset.eq sigma(U_comp(J),Z)$ and $sigma(U_comp(J),Z) subset.eq sigma(U_(J_s without J))$. 
  Therefore
  $U_J indep_PP U_comp(J_s) | Z$,
  and
  $U_J indep_PP U_(J_s without J) | Z$.
  \
  This implies
  $PP(U_comp(J_s) in dot | Z) =
  PP(U_comp(J_s) in dot | Z, U_J)
  $ and
  $PP(U_(J_s without J) in dot | Z) =
   PP(U_(J_s without J) in dot | Z, U_J).
  $
  Since $J_s$ disintegrates $Z$ and by @lem:as_union_random_index_set,
  we have
  $U_(J_s without J) indep_PP U_comp(J_s) | Z, U_J$.
  \
  Therefore
  $U_(J_s) indep_PP U_(comp(J_s) union J) | Z, U_J$.
  Since $AS|_{J aseq I}$ is a restriction of the underlying sigma algebra to a $sigma(U_J) ms$ set,
  we can condition on it. Therefore
  $U_(J_s) indep_PP U_(comp(J_s) union J) | Z, U_J, AS|_{J aseq I}$.

  Finally, let $A in Sect_(s in S) sigma(U_J_s, Z, AS|_{J_s aseq I})$.
  By the last independence statement,
  $A indep_PP U_(comp(J_s) union J) | Z, U_J, AS|_{J aseq I}$.
]

#theorem[
  There exists an almost surely unique minimal generating random index set of $X$ given $Y$
] <thm:history_exists>
#proof[
  Combine @lem:generation_chain, @lem:generation_sect and @lem:random_index_set_zorn.
]

#definition[history][
  The almost surely unique minimal generating random index set of $X$ given $Y$ is called the history of $X$ given $Y$.
  We write
  $
  history(X|Z) := Sect^astext {J : Omega -> powerset(I) | J "generates" X "given Z"}
  $
  @thm:history_exists implies that $history(X|Z)$ generates $X$ given $Z$.
]

We are now ready to define structural independence in terms of histories.

#definition[
  $X$ and $Y$ are structurally independent given $Z$, if their histories are almost surely disjoint.
  More precisely,
  $
  X orth Y | Z :<=> history(X|Z) sect history(Y|Z) aseq nothing.
  $
] <def:structural_independence>


// We now want to see that all desiderata from @des:history are fulfilled and determine the history almost surely uniquely.
In the next section we prove the fundamental theorem of structural independence that is listed in @des:history#[.2] and states that this definition of structural independence characterizes all the independencies that are implied by our assumptions.






= The Fundamental Theorem of Structural Independence
<sec:fundamental_theorem>

The goal of this section is to prove that structural independence (@def:structural_independence) characterizes
independence in all product distributions $P in distributionstimes$.

More precisely, our goal is to prove
$
forall P in distributionstimes: X indep_P Y | Z
<=>
history(X|Z) sect history(Y|Z) aseq nothing
.
$
This is @des:history#[.2] for the history map.

One direction is essentially implied directly by the definition of generation.
#theorem[Soundness of structural independence][
  Structural independence is sound.
  For any possible realization of a product probability distribution $P in distributionstimes$, structural independence implies independence.
  More precisely,
  $X orth Y | Z => forall P in distributionstimes : X indep_P Y | Z$.
]
#proof[
  Let $P in distributionstimes$.
  Since $J :=history(X|Z)$ generates $X$ given $Z$, we have
  $sigma(X) subset.eq sigma(U_J,Z,AS|_{J aseq I})$
  and $U_J indep_P U_comp(J) | Z$.
  Likewise with @lem:as_union_random_index_set and $history(Y|Z) subsetaseq comp(J)$,
  $sigma(Y) subset.eq sigma(U_history(Y|Z), Z, AS|_{history(Y|Z) aseq I}) subset.eq sigma(U_comp(J), Z, AS|_{comp(J) aseq I})$.
  Let $A in sigma(U_J,Z,AS|_{J aseq I})$ and $B in sigma(U_comp(J),Z,AS|_{comp(J) aseq I})$.
  Clearly, it suffices to show that $A sect C indep_P B sect C | Z$ for $C in {{J aseq I},{comp(J) aseq I},
  Omega without ({J aseq I} union {J aseq nothing})} subset.eq sigma(Z)$.
  + If $C = {J aseq I}$, then $B sect C in sigma(U_comp(J),Z,AS|_{comp(J) aseq I})|_C = sigma(Z)|_C$, so the independence is trivial.
  + Similarly, if $C = {comp(J) aseq I}$, then $A sect C in sigma(Z)|_C$ and the independence is trivial.
  + If $C = Omega without ({J aseq I} union {comp(J) aseq I})$, then
    $A sect C in sigma(U_comp(J),Z,AS|_{J aseq I})|_C subset.eq sigma(U_J,Z)$.
    Similarly, $B sect C in sigma(U_comp(J),Z)$.
    Since $U_J indep_P U_comp(J) | Z$, the independence follows. #qedhere
]


To prove the other direction, completeness, we define a dual notion to the history and generation, irrelevance.
While history and generation talk about depending, irrelevance talks about there being no information.

To motivate this notion we look at a simple lemma.
// #notation[
//   For ease of notation, we index $P in distributionstimes$ to
//   refer to the pushforward under $U_J$.
//   More precisely, let $J$ be a random indexset, then
//   $P_J := P_U_J$.
// ]
#lemma[
  Let $i in I$ and $P, Q in distributionstimes$, s.t.
// $P$ and $Q$ differ only for $U_i$,
  // i.e. $P_comp({i}) = Q_comp({i})$.
  // i.e.
  there is a $sigma(U_i) ms$ positive density $f:Omega -> RR_(>0)$, s.t. $P = f dot Q$.
  Then for all $A in sigma(X)$ we have
  $P(A|Z)(omega) = Q(A|Z)(omega)$ for a.e. $omega in {i in comp(history(X|Z))}$.
] <lem:history_comp_irrelevant>
#proof[
  Let $J := history(X|Z)$
  It suffices to show that $P(A|Z) = Q(A|Z)$
  for all $A in sigma(U_J,Z,AS|_{J aseq I})|_{i in comp(J)} = sigma(U_J,Z)|_{i in comp(J)}$.
  Let $A=B sect C$, where $B in sigma(U_J)$ and $C in sigma(Z)|_{i in comp(J)}$.
  Since sets of this form are sect stable and generate $sigma(U_J,Z)|_{i in comp(J)}$,
  and ${A in AS: P(A|Z) aseq Q(A|Z)}$ is a dynkin system,
  it suffices to show the statement for such $A$.
  Note that $1_C f indep_P B | Z$, since $J$ disintegrates $Z$ and
  $sigma(1_C f) subset.eq sigma(U_comp(J))$ and 
  $B in sigma(U_J)$.
  Let $E$ denote the expectation w.r.t. $Q$.
  Now
  $P(A|Z) aseq E(1_C f 1_B|Z)/E(f|Z)  aseq  (E(1_C f|Z)E(1_B|Z))/EE(f|Z)  aseq  1_C E(1_B|Z)  aseq  Q(A|Z)$.
]

This lemma tells us, that when we change the distribution of $U_i$, we cannot change
$P(A|Z)$ in the region ${i in.not history(X|Z)}$.
This is a dual notion to the dependance of history.
This motivates the following definition.

== The random index set of irrelevance

#definition[
  Let $K subset.eq I$.
  Let
  $
  distributionstimes2(K)
  := {(P,Q) in distributionstimes times distributionstimes:
  exists f : Omega -> RR_(>0), sigma(U_K) ms, "s.t." Q = f dot P}
  $
  For $i in I$, set $distributionstimes2(i) = distributionstimes2({i})$.
]

#definition[
  Let $J$ be a $sigma(Z) ms$ random index set.
  We say $J$ is irrelevant to $X$ given $Z$, if for all $i in I$,
  $(P,Q) in distributionstimes2(i)$ and $A in sigma(X)$, we have
  $P(A|Z) (omega) = Q(A|Z) (omega)$ for a.e. $omega in {i in J}$.
]
Of course, irrelevance extends to arbitrary index sets.

#lemma[
  Let $J$ be irrelevant to $X$ given $Z$.
  Let $K subset.eq I$. Then for $(P,Q) in distributionstimes2(K)$
  and $A in sigma(X)$, we have
  $P(A|Z) (omega) = Q(A|Z) (omega)$ for a.e. $omega in {K subsetaseq J\}$.
] <lem:irrelevance_index_set>
#proof[
  Let $phi$ be the probability density of $Q$ w.r.t. $P$.
  By ?? and the fact that $E(phi|U_K) = 1$, there is a family of probability densities $(phi_n)_(n in NN)$ and a family of indices in $K$, $(k_n)_(n in NN)$, s.t.
  $phi_n$ is $sigma(U_k_n) ms$ and
  $product_(n in NN_0) phi_n$ converges (unconditionally) in $L^1 (P)$ and a.s. to $phi$.
  For $n in NN$ define $ (P_n,Q_n) = ((product_(m=1)^(n-1) phi) dot P, (product_(m=1)^(n) phi) dot P)$.
  By the independence of $U$, we have $P_n,Q_n in distributionstimes$.
  
  - We have $P_n (A|Z)(omega) = Q_n (A|Z)(omega)$ for a.e. $omega in {K subsetaseq J\}$.
    Indeed, note that $P_n = phi_n dot Q_n$ and therefore
    $(P_n,Q_n) in distributionstimes2(k_n)$.
    By the definition of irrelevance,
    #text(top-edge: "ascender", bottom-edge: "descender")[$P_n (A|Z)(omega) = Q_n (A|Z)(omega)$ for a.e. $omega in {k_n in J} subsetaseq {K subsetaseq J\}$]
  - Since $P_0 = P$, by induction on $n$, we have $forall n in NN: P (A|Z)(omega) = Q_n (A|Z)(omega) $
    for a.e. $omega in {K subsetaseq J\}$.
  - Finally, $Q_n -> Q$ in $d_(L^1 (P))$. Let $C = {K subsetaseq J\}$.
    By convergence $P(A,C|Z) aseq Q_n (A,C| Z) -> Q (A,C|Z)$ in measure, and therefore
    $P(A,C|Z) aseq Q(A,C|Z)$.
    #qedhere
]

We want to show that a maximal irrelevant random index set exists.
As we have seen in @lem:history_comp_irrelevant, the complement of the history is one irrelevant random index set.
We will show in this section that it is actually maximal.

#lemma[
  An almost surely unique
  maximal irrelevant random index set for $X$ given $Z$ exists.
] <lem:irrelevance_exists>
#proof[
  Let $frak(I)$ denote the set of irrelevant random index sets for $X$ given $Z$.
  Set $M = Union^astext frak(I)$.
  We show that $M$ is irrelevant to $X$ given $Z$.
  Then clearly, $M$ is a maximal irrelevant random index set.
  Let $i in I$, $(P,Q) in distributionstimes2(i)$ and $A in sigma(X)$.
  We need to show that
  $P(A|Z)(omega)=Q(A|Z)(omega)$ for a.e. $omega in {i in M}$.
  By the definition of almost sure union, there exists a sequence of irrelevant random index sets
  $(J_n)_(n in NN)$ in
  $frak(I)$, s.t. ${i in M} aseq union.big_(n in NN) {i in J_n}$.
  Therefore it suffices to show
  $P(A|Z)(omega)=Q(A|Z)(omega)$.
  for a.e. $omega in {i in J_n}$ and $n in NN$.
  This is immediate by the definition of irrelevance and $J_n in frak(I)$.
]

#definition[random index set of irrelevance][
  We call the almost surely unique maximal irrelevant random index set from
  @lem:irrelevance_exists
  the random index set of irrelevance for $X$ given $Z$, or
  the irrelevance to $X$ given Z for short.
  More precisely,
  $
  irrel (X|Z) := Union^astext {J : Omega -> powerset(I) | J "is irrelevant to " X "given" Z}.
  $
  @lem:irrelevance_exists tells us that $irrel(X|Z)$ is irrelevant to $X$ given $Z$.
]



We will establish that $irrel(X|Z) = comp(history(X|Z))$,
so it really is the dual the history.
Recall that our goal in this section is to prove
the following direction of the fundamental theorem
$
forall P in distributionstimes : X indep_P Y | Z => history(X|Z) sect history(Y|Z) aseq nothing.
$
Under the assumption that $irrel(X|Z) = comp(history(X|Z))$, this becomes equivalent to
the dual notion
#set math.equation(numbering: "(1)")
$
forall P in distributionstimes : X indep_P Y | Z => irrel(X|Z) union irrel(Y|Z) aseq I.
$ <eq:fthm_irrel>


The reason why it is necessary to define $irrel(X|Z)$ is that
in the definition of $history(X|Z)$ we have to show the measurability
condition $sigma(X) in sigma(U_history(X|Z),Z,AS_{history(X|Z) aseq I})$
and the independence $U_history(X|Z) indep_P U_history(Y|Z) | Z$
for all $P in distributionstimes$.
This is not in direct connection with the provided assumption
$forall P in distributionstimes: X indep_P Y | Z$.
The definition of $irrel(X|Z)$, however, uses only probabilities
in its definition. So there is in a much more direct connection with this assumption
that we can exploit.

We might get the idea to define the history directly through
$history(X|Z) := comp(irrel(X|Z))$.
But there are a few issues.
Firstly, the definition of $irrel(X|Z)$ is rather indirect and
not very telling about what kind of $X$ and $Y$ fulfill
$irrel(X|Z) union irrel(Y|Z) aseq I$.
Secondly,
recall that it was relatively straightforward to prove the direction
$
history(X|Z) sect history(Y|Z) aseq nothing => forall P in distributionstimes : X indep_P Y | Z
$ <eq:fthm_back>
If we dualize with $irrel(X|Z)$ this is equivalent to
$
irrel(X|Z) union irrel(Y|Z) aseq I => forall P in distributionstimes : X indep_P Y | Z
$ <eq:fthm_back_irrel>
But now this statement is not easily proven directly. The way to prove @eq:fthm_back_irrel
moves through showing $history(X|Z) = comp(irrel(X|Z))$ and dualizing back to @eq:fthm_back.

In summary, $history(X|Z)$ and $irrel(X|Z)$ are dual notions that
more suitable to prove the (4) and (3) directions of the fundamental theorem, respectively.
The power of them is precisely that they are dual and come together to prove the fundamental theorem in full.

The next theorem proves that @eq:fthm_irrel holds in a weaker form.
If we unwrap @eq:fthm_irrel, it states that,
whenever $forall P in distributionstimes : X indep_P Y | Z$, we have
$comp(irrel(X|Z)) subsetaseq irrel(Y|Z)$.
// This condition on the irrelevances is equivalent to


// While irrelevance requires that $P(A|Z)=Q(A|Z)$ on ${i in J}$ for all $i in I$ $(P,Q) in distributionstimes2(i)$

#set math.equation(numbering: none)

#theorem[
  Let $forall P in distributionstimes : X indep_P Y | Z$.
  Let $i in I$, $(P,Q) in distributionstimes2(i)$ and $A in sigma(X), B in sigma(Y)$.
  Then $(P(A|Z) - Q(A|Z))(P(B|Z) - Q(B|Z)) aseq 0$.
  Therefore, for a.e. $omega in Omega$, $P(A|Z)(omega) = Q(A|Z)(omega)$
  or $P(B|Z)(omega) = Q(A|Z)(omega)$.
] <thm:mutual_exclusion>
#proof[
  Let $f : Omega -> RR_(>0)$ $sigma(U_i) ms$ s.t. $P = f dot Q$.
  We use the fact that for the positive $sigma(U_i) ms$ density $g=(1+f)/2$, we can define
  $R:= (P+Q)/2 =  g dot Q in distributionstimes$.
  Therefore $X indep_R Y | Z$.
  Denoting $E$ the expectation w.r.t $Q$ and noting that $g>0$,
  $
  R(A|Z)R(B|Z) aseq R(A,B|Z) \
  <=> 
  E (g 1_A|Z) E (g 1_B|Z) aseq E(g|Z) E(g 1_A 1_B|Z) \
  $
  We can now substitute $g$ by $(f+1)/2$ and multiply by 4.
  $
  <=> (E (f 1_A|Z) + E(1_A|Z)) (E (f 1_B|Z) E(1_B|Z))
  aseq (E(f|Z) + 1) (E(f 1_A 1_B|Z)+ E(1_A 1_B|Z) \
  $

  By the independence of $X$ and $Y$ given $Z$ w.r.t. $P$ and $Q$, we have
  $E(f 1_A|Z) E(f 1_B|Z) aseq E(f|Z) E(f 1_A 1_B|Z)$ and
  $E(1_A|Z)E(1_B|Z) aseq E(1_A 1_B|Z)$ respectively.
  Multiplying out and canceling these terms, we get
  
  $
  <=> E(f 1_A|Z) E(1_B|Z) + E(1_A|Z) E(f 1_B|Z) aseq E(f|Z) E(1_A 1_B|Z) + E(f 1_A 1_B|Z)
  $
  Dividing by $E(f|Z)$, we get
  $
  <=> P(A|Z) Q(B|Z) + Q(A|Z) P(B|Z) aseq Q(A,B|Z) + P(A,B|Z)
  $
  Using the independence w.r.t. $P$ and $Q$ again,
  $
  <=> P(A|Z) Q(B|Z) + Q(A|Z) P(B|Z) aseq Q(A|Z)Q(B|Z) + P(A|Z)P(B|Z)
  $
  which we can factorize as
  $
  <=> (P(A|Z)-Q(A|Z))(P(B|Z)-Q(B|Z)) aseq 0. #qedhere
  $
]

== An excursion to a Hilbert space embedding of measures
#lemma[
  Let $P,Q in distributionstimes$.
  Then there is a countable index set $I_0 subset.eq I$,
  a family of positive densities $(phi_i)_(i in I_0 union {*})$, s.t.

  + $forall i in I_0: phi_i : Omega -> RR_(>0)$ is $sigma(U_i) ms$,
  + $product_(i in I_0) phi_i (omega)$ converges for a.e. $omega in Omega$
  // and $product_(i in I_0) phi_i$ converges in $L^2$.
  + $phi_* : Omega -> RR_(>0)$ that doesn't influence the pushforward under $U$, i.e.
    $integral_A phi_* dif Q = Q(A)$ for all $A in sigma(U)$.
  + $P = (product_(i in I_0 union {*}) phi_i) dot Q$.
]
#proof[
  follows from @kakutani1948equivalence with some care. (TODO).
]


#lemma[
  $P in distributionstimes$ then $P = phi dot PP$,
  $P |-> sqrt(phi) in L^2 (PP)$ is an embedding into a hilbert space.
]

#definition[
  $angles(P,Q) := angles(sqrt((dif P)/(dif PP)), sqrt((dif Q)/(dif PP)))$.

  $norm(P)_2^2 := angles(P,P)^2+ angles(Q,Q)^2 - 2 angles(P,Q) = 2(1-angles(P,Q))$.

  $P -> Q$ in $norm(dot)_2 <=> angles(P,Q) -> 1$.
]

#lemma[
  Let $p$ be a probability density w.r.t. a probability measure $PP$ with expectation $EE$.
  // The w.r.t $A$ regularized density
  // $p_A := 1_A EE(1_A p)/PP(A) + 1_(A^c) EE(1_(A^c) p)/(PP(A^c))$ fulfills $integral_A p_A dif PP = integral_A p dif PP$
  // and $integral sqrt(p_A) >= integral sqrt(p)$.
  Then $EE(sqrt(EE(p|Z))) >= EE(sqrt(p))$.
  
] <lem:eucl_density_cond_exp>
#proof[
  $EE sqrt(EE(p|Z)) = EE sqrt(EE(p|Z)) >=^"Jensen" EE(EE(sqrt(p)|Z)) = EE(sqrt(p)) $.
]
#lemma[
  $X_n -> X, Y_n -> Y$ in $L^2(PP)$,
  Then $X_n Y_n -> X Y$ in $L^1 (PP)$.
]
#proof[
  Is an immediate consequence of the Hölder inequality.
  // $angles(X_n-X,Y_n-Y) = angles(X_n,Y_n) - angles(X_n,Y) - angles(X,Y_n) + angles(X,Y) -> 0$.
  // $
  // norm(X_n Y_n - X Y)_1
  // <=
  // norm(X_n Y_n - X_n Y)_1
  // + norm(X_n Y - X_n Y_y)_1
  // =
  // norm(X_n (Y_n-  Y))_1
  // + norm(X_n (Y -Y_y))_1 -> 0
  // $
]


#corollary[
  Let $P_n -> P$ and $X in L^oo (PP)$, then $phi_n X -> phi X$ in $L^1(PP)$
] <cor:hilbert_bounded_l1>
#proof[
  $sqrt(phi_n) -> sqrt(phi)$ in $L^2(PP)$.
  Since $X$ is bounded, $X_n := sqrt(phi_n X) in L^2$ and $X_n -> sqrt(phi X)$ in $L^2$.
  Therefore $phi_n X = X_n X_n -> sqrt(phi X) sqrt(phi X) = phi X$ in $L^1$.
]

#corollary[
  Let $PP_n -> PP$ and $A in AS$.
  Then $EE(phi_n A|Z) -> EE(A|Z)$ in $L^1$.
]
#proof[
  Follows by the linearity of conditional expectation and @cor:hilbert_bounded_l1.
]

#lemma[
  Let $mu$ be a finite measure on $(Omega,AS)$.
  Let $X_n -> X$ and $Y_n -> Y$ in $mu$-measure.
  If $(X,Y)$ is contained in a compact set $K subset.eq RR^2$ $mu$-a.e.
  and
  $f : RR^2 ->RR$ is continuous on an open set $U supset.eq K$.
  Then $f(X_n,Y_n) -> f(X,Y)$ in $mu$-measure.
] <lem:conv_measure_cont_func>
#proof[
  There is $K'$ compact and $U'$ open, s.t.
  $U supset.eq K' supset.eq U' supset.eq K$.
  The claim now follows by the uniform continuity of $f$ on $K'$.
]


#lemma[
  Let $PP_n -> PP$ in $L^1$ and $X$ be bounded.
  Then $EE_n (X|Z) -> EE(X|Z)$ in $PP$-measure.
] <lem:conditional_expectation_in_measure>
#proof[
  Let $phi_n$ be a density, s.t. $PP_n = phi_n dot PP$.
  Recall that $PP_n (A|Z) = EE(phi_n 1_A|Z) slash EE(phi_n|Z)$.
  Since $phi_n -> phi$ in $L^1$, we have
  $EE(phi_n|Z) -> EE(phi|Z)$ in $L^1$ and in measure.
  Clearly, $EE(phi_n X|Z) -> EE(X|Z)$ in $L^1$ and in measure.
  Let $epsilon > 0$.
  Then since $PP(phi < delta) ->^(delta -> 0) 0$.
  There is $delta > 0$, s.t. $PP(phi > delta) > 1 -epsilon$.
  Set $C = {phi>delta}$ and let $mu = PP|_C$ be a finite measure on $(C,AS|_C)$.
  Clearly, $EE(phi_n|Z)|_C -> EE(phi|Z)|_C$ and
  $EE(phi_n X|Z)|_C -> EE(X|Z)|_C$ in $mu$-measure.
  
  Define $f(x,y) = x/y 1_(y > 0)$. Then $f$ is continuous on $RR times RR_(>0)$
  while $(EE(phi X|Z)|_C,EE(phi|Z)|_C)$ is contained in $[0,1] times [delta,2]$ $mu$-a.e.
  By @lem:conv_measure_cont_func
  $EE_n (X|Z)|_C = f(EE(phi_n X|Z)|_C,EE(phi X|Z)|_C) -> f(EE(X|Z)|_C,1) = EE(X|Z)|_C$
  in $mu$-measure.
  Therefore, for any $xi > 0$,
  $limsup_(n) PP(abs(EE_n (X|Z) - EE (X|Z)) > xi)
  <= limsup_(n) mu(abs(EE_n (X|Z) - EE (X|Z)) > xi) + PP(C^c)
  = PP(C^c) <= epsilon.
  $

  Since $epsilon$ was arbitrary, we have
  $forall xi > 0: PP(abs(EE_n (X|Z) - EE (X|Z)) > xi) -> 0$.
]

#lemma[
  $sqrt(phi_n) -> sqrt(phi)$ in $L^2 (PP)$.
  Then $phi_n -> phi$ in $L^1$
]
#proof[
  Hölder.
]






== Fundamental theorem for the random index set of irrelevance.


#lemma[
  Let $phi,phi'$ and $psi,psi'$ be probability densities w.r.t. $PP$ s.t.
  $phi,phi'$ are $sigma(U) ms$ and
  $EE(psi|U)=EE(psi'|U)=1$.
  Then $phi psi$ is a density,
  and $norm(phi psi - phi' psi')_1 <=  norm(phi' - phi)_1 + norm(EE(abs(psi'-psi) :U))_oo$.
] <lem:cond_product>
#proof[
  First, note that $integral phi psi dif PP = integral phi EE(psi|U) dif PP = 1$,
  so $phi psi$ is a density.
  Second,
  $
  norm(phi' psi' - phi psi)_1 
  &<= norm(phi' (psi' - psi))_1 + norm((phi' - phi) psi)_1 \
  &= integral phi' EE(abs(psi'-psi):U) + integral (phi' - phi) EE(psi|U) dif PP \
  &<= norm(EE(abs(psi'-psi) :U))_oo + norm(phi' - phi)_1
  $
]

#theorem[
  Let $i in I$.
  If the set
  $
  distributionstimes2(i,C):= {(P,Q) in distributionstimes2(i) : P(A|Z)(omega) != Q(A|Z)(omega)
  "for a.e." omega in C}
  $
  is not empty, then it is dense in the topology $d_(L^1 (P))$ on $distributionstimes2(i)$ for any $(P,Q) in distributionstimes2(i,C)$.
] <thm:density>
#proof[
  Let
  $(P,Q) in distributionstimes2(i,C)$
  // $
  // : P(A|Z) (omega) != Q(A|Z) (omega)$ for a.e.
  // $omega in C$.
  Then $Q=q dot P$ for a $sigma(U_i) ms$ probability density $q$.

  Let $(P',Q') in distributionstimes2(i)$.
  Then there is a family of densities $(phi_n)_(n in NN_0)$ and indices ${i_n}_(n in NN)$, s.t.
  - $EE(phi_0|U) aseq 1$.
  - $forall n in NN : phi_n$ is $sigma(U_i_n) ms$.
  - $product_(n in NN_0) phi_n$ converges (unconditionally) in $L^1$
    and a.s. pointwise to $radiv(P',P)$.
  W.l.o.g. we can assume $i = i_1$.
  Then there is a $sigma(U_i) ms$ probability density $q'$, s.t.
  $Q' = q' dot P$. Set $phi'_1 =  q' dot phi_0$ and for $n in NN_0 without {1}$, set $phi'_n = phi_n$.
  Then $q dot product_(n in NN_0) phi_n = product_(n in NN_0) phi'_n = radiv(Q',P)$
  by independence of $U$, and @lem:cond_product.

  + Finite dimensional case:
    Suppose $exists m in NN: forall n>= m : phi_n = 1$.
    Then define
    $
    p : &[0,1] times RR^{0,..,m} -> [0,1] \
    &(lambda, x) |-> product_(n=0)^(m) (lambda x_n + comp(lambda)).
    $
    Note that
    $p(dot,x)$ is a polynomial for $x in RR^{0,...,m}$.
    Set $Phi = (phi_n)_(n=1)^m$
    and $Phi' = (phi'_n)_(n=1)^m$.
    Define $phi_lambda (omega) = p(lambda,Phi(omega))$ and
    $phi'_lambda (omega) = p(lambda, Phi'(omega))$.
    The following properties hold for $phi_lambda$ and $phi'_lambda$.
    // and $phi'_lambda (omega) = f(lambda,tilde(p')(omega))$.
    #set enum(numbering:"(i)")
    + We claim that $phi_lambda$ and $phi'_lambda$ are probability densities w.r.t. $P$.
      Indeed,
      $integral phi_lambda dif P = integral product_(n=0)^m (lambda phi_n + comp(lambda)) dif P
      = integral EE(lambda phi_0 + comp(lambda)|U) product_(n=1)^m ((lambda phi_n) + comp(lambda)) dif P
      = product_(n=1)^m integral ((lambda phi_n) + comp(lambda)) dif P = 1,$
      because of  $EE(phi_0|U) aseq 1$ and the independence of $U$.
      
    + We claim that $lambda |-> phi_lambda$ and $lambda |-> phi'_lambda$ are continuous maps
      into $L^1$.
      Indeed,
      let $lambda,lambda' in [0,1]$.
      Then, since $lambda phi_n - comp(lambda) - (lambda' phi_n - comp(lambda')) 
      // = (lambda - lambda')phi_n - (1-lambda -(1- lambda')) =
      // (lambda - lambda') phi_n -(lambda'-lambda)
      = (lambda - lambda') (phi_n - 1)$,
      $
      norm(phi_lambda - phi_lambda')_1
      &= integral abs(product_(n=0)^m (lambda phi_n - comp(lambda)) - product_(n=0)^m (lambda' phi_n - comp(lambda'))) dif P  \
      &<= norm(EE(abs((lambda - lambda') (phi_0-1)):U))_oo
      product_(n=1)^m norm((lambda - lambda')(phi_n - 1))_1 \
      // &= (lambda - lambda')^m norm(EE(abs(phi_0-1):U))_oo product_(n=1)^m norm(phi_n - 1)_1 \
      &<= (lambda - lambda')^m dot 2 dot product_(n=1)^m 2 \
      &= (2(lambda - lambda'))^m.
      $
    
    Set $R_lambda := phi_lambda dot P$ and $R'_lambda := phi'_lambda dot P$.
    Our goal is to show that for $lambda$ near $1$, we
    have $R_lambda (A|Z) != R'_lambda (B|Z)$ a.s. on $C$.
    Set
    $E_(Phi,A) = (EE(phi_n 1_A|Z))_(n=1)^m$,
    $E_(Phi',A) = (EE(phi'_n 1_A|Z))_(n=1)^m$.
    $E_(Phi) = (EE(phi_n|Z))_(n=1)^m$,
    $E_(Phi') = (EE(phi'_n|Z))_(n=1)^m$.

    Now note that for a.e. $omega in Omega$ conditional expectation is linear, and so
    $
    &R_lambda (A|Z)(omega) = R'_lambda (A|Z)(omega) \
    <=>& EE(phi_lambda 1_A|Z) EE(phi'_lambda|Z)(omega)
    = EE(phi'_lambda 1_A|Z)(omega)
    EE(phi_lambda|Z)(omega) \
    <=>& EE(p(lambda,Phi) 1_A|Z) EE(p(lambda,Phi')|Z)(omega)
    = EE(p(lambda,Phi') 1_A|Z)(omega)
    EE(p(lambda,Phi)|Z)(omega) \
    <=>&
    p(lambda,E_(Phi,A)(omega)) p(lambda,E_(Phi')(omega))
    - p(lambda,E_(Phi',A)(omega)) p(lambda,E_(Phi)(omega)) = 0
    $

    Let $p'(lambda,omega) = 
    p(lambda,E_(Phi,A)(omega)) p(lambda,E_(Phi')(omega))
    - p(lambda,E_(Phi',A)(omega)) p(lambda,E_(Phi)(omega)).
    $
    Clearly, $p' : [0,1] times Omega -> RR$ is measurable and
    $p'(dot,omega)$ is a polynomial for all $omega in Omega$.
    Then we have just proved that
    $R_lambda (A|Z)(omega) = R'_lambda (A|Z)(omega) <=> p'(lambda,omega) = 0 .
    $
    Therefore, because $(R_0,R'_0) = (P,Q) in distributionstimes2(i,C)$, we have
    $p'(0,omega) != 0$ for a.e. $omega in C$.
    Therefore $p'(dot,omega)$ is not the zero polynomial for a.e. $omega in C$
    and the set ${lambda in [0,1]: p'(lambda,omega)=0}$ is finite for a.e. $omega in C$.
    Let $cal(L)$ be the Lebesgue measure on $[0,1]$.
    By Fubini, $(cal(L) times P){(lambda,omega) in [0,1] times C : p'(lambda,omega) = 0} = 0$.
    Again, by Fubini, for $cal(L)$-a.e. $lambda in [0,1]$,
    we have $P({omega in C: p'(lambda,omega) = 0}) = 0$.
    So we can choose a sequence $lambda_n in [0,1]$, s.t. $lambda_n arrow 1$ and
    for $n in NN$,
    $p'(lambda_n,omega) != 0$ for a.e. $omega in C$.
    Then by construction, $(R_lambda_n,R'_lambda_n) in distributionstimes2(i,C)$, while
    $R_lambda_n -> P'$ and $R'_lambda_n -> Q'$ in $L^1 (P)$.
    
  + General case:
    // Let now $(phi_n)_(n in NN_0)$ be arbitrary.
    #text(size:1em, top-edge:"cap-height",bottom-edge: "descender")[
    Let $epsilon > 0$.
    Choose, $m in NN$ s.t.
    $norm(product_(n=0)^m phi_n - phi)""_""_1 < epsilon$
    and
    $norm(product_(n=0)^m phi'_n - phi')_1 < epsilon$.
    Set $tilde(phi) = product_(n=0)^m phi_n$
    and
    $tilde(phi)' = product_(n=0)^m tilde(phi)_n$.
    Set $tilde(P) = tilde(phi) dot P$ and
    $tilde(Q) = tilde(phi)' dot P$.
    ]
    Then by the choice of $m$,
    $d_1 ((tilde(P),tilde(Q)\),(P',Q'\)\) < epsilon$
    Clearly, $\(tilde(P),tilde(Q)'\)$ fulfills the assumption of finite dimensional case
    and there is $(P'',Q''\) in distributionstimes2(i,C)$ s.t. $d_1((P'',Q''),(tilde(P),tilde(Q)\)\)< epsilon$.
    By the triangle inequality,
    $d_1((P'',Q''),(P',Q')) < epsilon$.
    Since $epsilon>0$ was arbitrary, we have shown $L^1 (P)$ density
    of $distributionstimes2(i,C)$ in $distributionstimes2(i)$.
    #qedhere
]


#theorem[
  If $forall P in distributionstimes: X indep_P Y | Z$, then
  $irrel(X|Z) union irrel(Y|Z) aseq I$.
] <thm:fthm_irrel>
#proof[
  // Look at the continuous $sigma(Z) ms$ function
  // Define the metric $d : distributionstimes times distributionstimes -> RR ; (P,Q) |-> norm(radiv(P,PP)-radiv(Q,PP))_oo$.
  // The function
  // $p_A : distributionstimes2(i) -> L^oo (Omega,sigma(Z),PP); (P,Q) |-> abs(P(A|Z) - Q(A|Z))$
  // is clearly continuous w.r.t. the topology on $distributionstimes2(i)$ induced by $d$.
  // By @thm:mutual_exclusion, we know $p_A p_B aseq 0$ for any $B in sigma(Y)$.
  Suppose, that there is $i in I$, $C_0 in sigma(Z) without NS$, s.t.
  $C subsetaseq {i in.not irrel(X|Z) union irrel(Y|Z)}$.
  Then by the definition of irrelevance, there is $A in sigma(X)$
  and $(P,Q) in distributionstimes2(i)$
  and a $C in sigma(Z) without NS$ s.t. $C subsetaseq C_0$
  and $P(A|Z)(omega) != Q(A|Z)(omega)$ for a.e. $omega in C$.

  Towards a contradiction, we show that
  $C subset.eq {i in irrel(Y|Z)}$.
  For this, let $(P',Q') in distributionstimes2(i)$ and $B in sigma(Y)$.
  It suffices to show that $P'(B|Z)(omega) = Q'(B|Z)(omega)$ for a.e. $omega in C$,
  since then the random index set $J(omega) := {i}$ if $omega in C$ and $nothing$ else;
  is irrelevant to $Y$ given $Z$.
  Restating this, we will prove $P'(B,C|Z) aseq Q'(B,C|Z)$.
  
  In @thm:density, we have $(P,Q) in distributionstimes2(i,C)$ is nonempty
  and therefore
  dense in $distributionstimes(i)$ in the topology induced by $d_(L^1(P))$.
  Let $(P_n,Q_n) in distributionstimes2(i,C)$ s.t. $(P_n,Q_n) -> (P',Q')$.
  By definition of $distributionstimes2(i,C)$, we have for all $n in NN$ that
  $P_n (A|Z) (omega) != Q_n (A|Z) (omega)$ for a.e. $omega in C$
  and therefore by @thm:mutual_exclusion, $P_n (B|Z) (omega) = Q_n (B|Z)(omega)$ for
  a.e. $omega in C$.
  Then by @lem:conditional_expectation_in_measure
  $P_n (B,C|Z) -> P' (B,C|Z)$ in measure, while
  $P_n (B,C|Z) aseq Q_n (B,C|Z) -> Q'(B,C|Z)$.
  Since a limit in measure is unique,
  $P' (B,C|Z) aseq Q'(B,C|Z)$.
]

== The duality between History and Irrelevance


#theorem[
  We have $forall P in distributionstimes: X indep_P U_irrel(X|Z) |Z$.
] <thm:irrel_indep>
#proof[
  Let $P in distributionstimes$ and $A in sigma(X,Z)$.
  Let $K subset.eq I$ and $B = Times_(k in K) B_k$, where $B_k subset.eq Val(U_k)$ measurable.
  By @cor:sigma_stable_generator_random_family, it suffices to show that
  $A indep_P {K subsetaseq irrel(X|Z), U_K = B\} | Z$.
  Let $E$ denote the expectation w.r.t. $P$.
  Since $C = {K subsetaseq irrel(X|Z)\} in sigma(Z)$, it suffices to show
  $A sect C indep_P B sect C | Z$ for all $B in sigma(U_K,Z)$.
  Therefore, w.l.o.g. we can assume $A subset.eq C$ and $B subset.eq C$.
  Let $phi_k$ be positive, $sigma(U_k) ms$ probability densities w.r.t. $P$.
  Set $phi = product_(k in K) phi_k$ and $Q = phi dot P$.
  Then $(P,Q) in distributionstimes2(K)$
  and by @lem:irrelevance_index_set $P(A|Z) aseq Q(A|Z)$ because $A,B subset.eq C$.

  By ??, it suffices to show that
  $P(A|Z) aseq P(A|U_K, Z)$.
  Now let $D in sigma(Z)$.
  $
  // integral E(1_D P(A|Z)|U_K) dif Q
  // &=
  integral_D P(A|Z) dif Q
  &= integral_D Q(A|Z) dif Q \
  &= integral_D 1_A dif Q \
  &= integral_D f 1_A dif P \
  &= integral_D E(f 1_A|U_K,Z) dif P \
  &= integral_D P(A|U_K,Z) dif Q \
  // &= integral E(1_D P(A|U_K,Z),U_K) dif Q \
  $

  Therefore, taking conditional expectation w.r.t. $U_K$,
  $
  integral phi E(1_D (P(A|Z) - P(A|U_K,Z))|U_K) dif P = 0
  $
  Clearly, we can approximate the indicator variable of any rectangle $B = Sect_(k in K) B_k$, where
  $B_k in sigma(U_k)$, uniformly by a positive probability density
  $phi^epsilon = product_(k in K) phi_k^epsilon$, where $phi_k^epsilon = (1_B + epsilon)/(P(B)+epsilon)$.
  As $epsilon -> 0$, $phi^epsilon -> 1_B$ uniformly.
  Therefore,
  #[
  #set math.equation(numbering:"(1)")
  $
  integral_B E(1_D (P(A|Z) - P(A|U_K,Z))|U_K) dif P = 0
  $ <eq:integral_equality>
  ]
  for all these choices of $B$. This set of rectangles is a sect stable generator of $sigma(U_K)$.
  The set of $B subset.eq Val(X_K)$ which fullfill @eq:integral_equality,
  clearly form a Dynkin system, therefore @eq:integral_equality holds for all $B in sigma(U_K)$ measurable.

  Therefore,
  since
  $E(1_D (P(A|Z) - P(A|U_K,Z))|U_K)$ is $sigma(U_K) ms$, we have
  $
  E(1_D (P(A|Z)- P(A|U_K,Z))|U_K) aseq 0
  $
  Now let $F in sigma(U_K)$ then 
  $E(1_(D sect F) (P(A|Z)- P(A|U_K,Z))|U_K) aseq 0$. Then

  #[
  #set math.equation(numbering:"(1)")
  $
  integral_G P(A|Z) - P(A|U_K,Z) = 0
  $ <eq:second_integral_equality>
  ]
  for all $G=D sect F$, where $D in sigma(Z)$ and $F in sigma(U_K)$.
  Since ${D sect F : D in sigma(Z)}$ is a sect stable generator of $sigma(U_K,Z)$ and
  the set of all $G in sigma(U_K,Z)$ for which @eq:second_integral_equality holds, form
  a dynkin system, @eq:second_integral_equality holds for all $G in sigma(U_K,Z)$.
  Since $P(A|Z) - P(A|U_K,Z)$ is $sigma(U_K,Z) ms$, we have
  $P(A|Z) aseq P(A|U_K,Z)$.
]



#lemma[
  We have $forall P in distributionstimes: U_comp(irrel(X|Z)) indep U_irrel(X|Z) | Z$.
] <lem:irrel_disintegration>
#proof[
  By @thm:irrel_indep, $forall P in distributionstimes: X indep_P U_irrel(X|Z) | Z$.
  Let $B in sigma(U_irrel(X|Z))$.
  Then $forall P in distributionstimes X indep_P B | Z$, and therefore
  by @thm:fthm_irrel $irrel(X|Z) union irrel(B|Z) = I$ and
  $irrel(B|Z) supset.eq comp(irrel(X|Z))$.
  By @thm:irrel_indep, $forall P in distributionstimes : B indep_P U_(irrel(B|Z)) | Z$
  and by @lem:as_union_random_index_set,
  $sigma(U_(irrel(B|Z)),Z) supset.eq sigma(U_(comp(irrel(X|Z))),Z)$.
  Therefore, $forall P in distributionstimes: B indep_P U_comp(irrel(X|Z))$.
  Since $B in sigma(U_(irrel(X|Z)))$ was arbitrary, we have
  $forall P in distributionstimes: U_comp(irrel(X|Z)) indep U_irrel(X|Z) | Z$.
]


#theorem[
  Then
  $sigma(X,U_comp(irrel(X|Z))) indep_P U_irrel(X|Z) | Z$.
] <lem:irrel_combined_indep>
#proof[
  By @lem:irrel_disintegration, we have
  $forall P in distributionstimes: U_comp(irrel(X|Z)) indep_P U_irrel(X|Z) | Z$.
  By @thm:irrel_indep, we have
  $forall P in distributionstimes: X indep_P U_irrel(X|Z) | Z$.

  Let $P in distributionstimes$.
  Let $K subset.eq I$ be finite and nonempty.
  // and $B in sigma(U_K)$ measurable.
  // Let $A in sigma(X|Z)$.
  Let $C = {K subset.eq comp(irrel(X|Z))}$.
  By @cor:sigma_stable_generator_random_family it suffices
  to show
  $sigma(X,Z,U_K)|_C indep_P U_irrel(X|Z) | Z$.


  Let $A in sigma(X,Z)|_C$.
  Let $phi = product_(n=1)^m phi_k$, where $phi_k$ is a $sigma(U_k) ms$
  probability density.
  Set $Q = phi dot P$,
  // Then $(P,Q) in distributionstimes2(i,K)$.
  Then $Q in distributionstimes$ and therefore
  $X indep_Q U_irrel(X|Z)$.
  
  // By @lem:irrelevance_index_set, we have $P(A|Z) aseq Q(A|Z)$ because $A subset.eq {K subset.eq I}$.
  Let $E$ be the expectation w.r.t $P$.
  Now, we have $Q(A|Z)Q(B|Z) aseq Q(A,B|Z)$.
  Therefore,
  $E(phi 1_A|Z)E(phi 1_B|Z) aseq E(phi|Z)E(phi 1_A 1_B|Z)$.
  Since $1_C phi$ is $sigma(U_K)|_C subset.eq sigma(U_comp(irrel(X|Z)))|_C ms$,
  we have $1_C phi indep_Q B | Z$.
  Therefore we have
  $E(phi 1_A|Z)E(phi|Z)E(1_B|Z) aseq E(phi|Z)E(phi 1_A 1_B|Z)$ and so
  $E(phi 1_A|Z)E(1_B|Z) aseq E(phi 1_A 1_B|Z)$
  By approximating rectangles $D = Sect_(k in K) D_k$, where $D_k in sigma(U_k)$
  by $phi^epsilon = product_(n=1)^k phi_k^epsilon$,
  where $phi^k_epsilon = (D_k + epsilon)/(P(D_k) + epsilon)$,
  we have $phi^epsilon -> 1_B$ uniformly and therefore
  #[#set math.equation(numbering:"(1)")
  $
  E(1_D 1_A|Z)E(1_B|Z) aseq E(1_D 1_A 1_B|Z)
  $ <eq:expectation_equality>
  ]
  holds for all rectangles.
  Note that all $D in sigma(U_K)$ for which @eq:expectation_equality holds
  form a Dynkin system and are generated by the sect stable system of rectangles.
  Therefore @eq:expectation_equality holds for all $D in sigma(U_K)$.
  In conclusion, we have $(X,U_comp(irrel(X|Z))) indep_P U_irrel(X|Z)$.
]

#lemma[
  Let $C in sigma(Z)$.
  If for all $psi$ with $EE(psi|U) aseq 1$, we have
  $1_C EE(psi|U,Z) aseq 1_C$, then
  $C in sigma(U)$ and
  $sigma(Z)|_C subset.eq sigma(U)|_C$.
]
#proof[
  Let $f$ be positive and $sigma(Z) ms$.
  Set $f' = f/EE(f|U)$.
  Then $f' in sigma(U,Z)$.
  and $EE(f|U) = 1$.
  Then $EE(f|U) aseq 1$ and so $1_C EE(f'|U,Z) aseq 1_C$ and so $1_C f/EE(f|U) aseq 1_C$, and therefore
  $1_C f = 1_C EE(f|U)$.
  Approximating, $1_C$, we get
  $1_C = 1_C EE(1_C|U)$.
  Since $f$ was arbitrary, we have  $sigma(Z)|_C subset.eq sigma(U)|_C$.
]

#lemma[
  Let $B in sigma(U)$.
  // Suppose that
  // ${res in irrel(B|Z)} aseq Omega$.
  // $EE(B|Z) = EE_g (B|Z)$.
  Let $C = {EE(B|Z) in (0,1), res in irrel(B|Z)}$.
  Then $sigma(Z)|_C subset.eq sigma(U)$.
]
#proof[
  It suffices to show that $1_C EE(g|U,Z) aseq 1_C$.
  Note that $EE(B|Z)(omega) EE(g|Z)(omega) = EE(g B|Z)(omega)$ for a.e.
  $omega in {res in irrel(B|Z)}$.
  Therefore, for a.e. $omega in C$, we have
  $EE(g|Z)(omega) = (EE(g B|Z)(omega))/(EE(B|Z)(omega))$.

  Define $g' = 1_B g + 1_(B^c)$, Then note that $E(g'|U) = 1$.
  Therefore, since $g$, was arbitrary, for
  a.e. $omega in C$
  // {E(B|Z) in {0,1}} aseq {E(B^c|Z) in {0,1}}$,
  we have
  $
  EE(g|Z)(omega)
  = (EE(g 1_B|Z)(omega))/(EE(1_B|Z)(omega))
  = (EE(g' 1_B|Z)(omega))/(EE(1_B|Z)(omega))
  = EE(g'|Z)(omega).
  $
  Furthermore, since 
  ${EE(B|Z) in (0,1)} aseq {EE(B^c|Z) in (0,1)}$, we can continue for a.e. $omega in C$,
  $
  EE(g'|Z)(omega)
  = (EE(g' 1_(B^c)|Z)(omega))/(EE(1_(B^c)|Z)(omega))
  = (EE(1_(B^c)|Z)(omega))/(EE(1_(B^c)|Z)(omega))
  = 1
  $
  Therefore, $1_C EE(f g |Z) = 1_C EE(f|Z)$ for all $f$ densities.
  Therefore, integrating,
  $integral_D f g = integral_D f$ for all $D in sigma(Z)|_C$.
  Therefore, $1_C EE(g|Z,U)= 1_C$.
]


#lemma[
  Let $C = {irrel (X|Z) aseq I}^c$.
  Then $sigma(Z)|_C subsetaseq sigma(U)$.
]
#proof[
  Let $J = irrel(X|Z)$.
  We have shown 
  $forall P in distributionstimes: U_J indep_P U_comp(J)$.
  Therefore,
  $irrel^res (U_J|Z) union irrel^res (U_comp(J)|Z) = I^res$.
  
  First we show
  $sigma(Z)|_(C^res) subset.eq sigma(U)$ for $C^res = {res in irrel^res (U_J|Z)} sect C$.
  We claim that $Union^astext_(B in sigma(U_J)) {EE(B|Z) in (0,1)} supsetaseq C^*$.

  Indeed, suppose that there is some $C' subsetaseq C^*$, s.t.
  for all $B in sigma(U_J)$
  $EE(B|Z)(omega) in {0,1}$ for a.e. $omega in $
  Then $B sect C' in sigma(Z)$ and therefore $sigma(U_J)|_C' subset.eq sigma(Z)$.


  Contraiction for $comp(J)$.
]

#lemma[
  If ${res in irrel(X|Z)} subsetaseq {I subsetaseq irrel(X|Z)}$.
]
#proof[
  Let $i in I$ and $A in sigma(X)$.
  Let $(P,Q) in distributionstimes2(i)$.
  It suffices to show $P(A|Z)(omega) = Q(A|Z)(omega)$
  for a.e. $omega in {res in irrel(X|Z)}$.
  
]



#lemma[
  For all $A in sigma(U)$, let $C={EE(A|Z) in (0,1)} sect {irrel(X|Z) asneq I}$,
  we have
  $sigma(Z)|_C subset.eq sigma(U)$.
]
#proof[
  Let $J = irrel(X|Z)$.
  Let $A in U_J$ and $B in U_comp(J)$.
  Then we have either
  $forall P in distributionstimes: P(A|Z) = P_g (A|Z)$ or
  $P(B|Z) = P_g (B|Z)$.
  By arguments,
  WLOG
  $P_g (A|Z) = P(A|Z)$, then
  Then $sigma(Z)|_(EE(B|Z) in (0,1)) subset.eq sigma(U)$.

  Therefore
  $sigma(Z)|_(EE(A sect B|Z) in (0,1)) subset.eq sigma(U)$.


  We show that all $A in sigma(U)$ that fullfill
  $sigma(Z)|_(EE(A|Z) in (0,1)) subset.eq sigma(U)$ form a Dynkin system.
  1. $Omega$ yes
  2. Let $A subset.eq B$ with this property
     Now $EE(B without A|Z) in {0,1}$
     only if $EE(B|Z) = 1$ and $EE(A|Z) = 0$. (doesnt happen)
     or $EE(B|Z) = EE(A|Z)$. so it becomes less

  3. union is clear. since it can become only less
]
#lemma[
  Let $C = {irrel(X|Z) asneq nothing}$.
  Then $sigma(Z)|_C subset.eq sigma(U)$.
]
#proof[
  
]


#lemma[
  For all $psi$ with $EE(psi|U,Z) = 1$, we have

  $EE(psi 1_A 1_B|Z) = EE(psi 1_A|Z) EE(psi 1_B|Z)$
  
  $EE(psi 1_A 1_B|Z)/EE(psi 1_B|Z) = EE(psi 1_A|Z)$
  $EE(psi 1_A 1_B|Z)/EE(psi 1_B|Z) = EE(psi 1_A|Z)$ on $EE(1_B|Z) > 0$.
  $(psi 1_B EE)(1_A|Z) = (psi EE)(1_A|Z)$
]

#lemma[
  Let $C = {irrel(X|Z) asneq nothing}$.
  Then for all positive densities $psi$ with
  $EE(psi|U) = 1$, we have
  $(psi dot EE)(1_A|Z) = EE(1_A|Z)$.
  // Then $sigma(X,Z)|_C subset.eq sigma(U,Z)$.
]
#proof[
  Let $P in distributionstimes$.
  Let $A in sigma(X,Z)|_C$.
  It suffices to show that
  $1_A = E(A|U,Z)$.
  Let $psi$ be a positive density, s.t. $EE(psi|U)= 1$.
  We show that
  $E(psi 1_A|Z) = E(psi E(1_A|U,Z)|Z)$.
  For every $B in sigma(U_irrel(X|Z))$, we have 
  $EE(psi 1_A|Z) EE(psi 1_B|Z) = EE(psi|Z) EE(psi 1_A 1_B |Z)$.
  Since $Z|_C$ is $sigma(U) ms$, we have
  for 
  a.e. $omega in {EE(B|Z) in (0,1)} sect C$, that
  $EE(psi 1_A|Z)(omega) = (EE(psi 1_B 1_A|Z)(omega))/(EE(psi 1_B|Z)(omega))$.
  Furthermore, $B in sigma(U_irrel(X|Z)) subset.eq sigma(U)$.
  Choosing $psi' = 1_B psi + 1_(B^c)$, and $psi'' = 1_B + 1_(B^c) = 1$ we get
  $EE(psi 1_A|Z)(omega) = EE(psi' 1_A|Z)(omega) = EE(psi'' 1_A|Z)(omega) = EE(1_A|Z)(omega)$.
  Further, note that $1_C EE(psi|Z) aseq 1_C$, since $sigma(Z)|_C subset.eq sigma(U)$
  and $EE(psi|U) = 1$.
  In conclusion, we have for a.e. $omega in {EE(B|Z) in (0,1)} sect C$, that
  $1_C (psi dot EE) (1_A|Z) aseq 1_C (EE(psi 1_A|Z) (omega))/EE(psi|Z) aseq 1_C EE(1_A|Z)$.
]

#theorem[
  $history(X|Z) aseq comp(irrel(X|Z))$.
]
#proof[
  We show both inclusions.
  \
  '$supset.eq$': It suffices to show $comp(history(X|Z)) subset.eq irrel(X|Z)$.
  This follows immediately from showing that $comp(history(X|Z))$ is irrelevant to $X$ given $Z$.
  We have shown this in @lem:history_comp_irrelevant.
  \
  '$subset.eq$': It suffices to show that $comp(irrel(X|Z))$ generates $X$ given $Z$.
  Let $A in sigma(X)$, then
  $forall P in distributionstimes: A indep_P U_(irrel(X|Z))$.
  and $forall P in distributionstimes: U_comp(irrel(X|Z)) indep_P U_(irrel(X|Z))$.
  Let $H = comp(irrel(X|Z))$ and $P in distributionstimes$. Let $E$ be the expectation w.r.t $P$.
  Let $P in distributionstimes$ and denote by $E$ its expectation.
  To show that $A in sigma(U_H, Z, AS_{H aseq I})$, note that $A sect {H aseq I} in sigma(AS|_{H aseq I})$,
  so it suffices to show that $1_(A without {H aseq I}) aseq E(1_(A without {H aseq I})|U_H,Z)$.
  Therefore, we can assume that $A subset.eq comp({H aseq I})$.
  // Now we have $irrel(A|Z)$
  // Let $Q in distributionstimes$ and $tilde(E)$ be the expectation w.r.t $Q$.

  By @lem:irrel_combined_indep, we have
  $(X,U_H) indep_P U_comp(H)$.

  We first show that for all $C in sigma(U)$, we have
  #[
  #set math.equation(numbering:"(1)")
  $
  E(1_C 1_A|Z) aseq E(1_C E(1_A|U_H,Z)| Z)
  $ <eq:condition_equality>
  ]
  For this, it suffice to show  @eq:condition_equality for all $C = B sect D$, where
  $B in sigma(U_comp(H))$ and $D in sigma(U_H)$, since sets of this form are a sect stable generator
  of $sigma(U_comp(H),U_H) supset.eq sigma(U)$ and the sets $C$ that fulfill @eq:condition_equality clearly
  form a Dynkin system. Now, by independence,
  $
  &&E(1_B 1_D 1_A|Z) &aseq E (1_B 1_D E(1_A|U_H,Z)|Z) \
  <=>&& E(1_B|Z) E(1_D 1_A|Z) &aseq E(1_B|Z)E(E(1_D 1_A|U_H,Z)|Z) \
  arrow.l.double&& E(1_D 1_A|Z)&aseq E(E(1_D 1_A|U_H,Z)|Z) \
  <=>&& E(1_D 1_A|Z)&aseq E(1_D 1_A|Z) \
  $ 
  Integrating @eq:condition_equality, and adding any $F in sigma(Z)$ we have
  $integral_C 1_A dif P = integral_C E(1_A|U_H,Z) dif P$ for all $C in sigma(U,Z)$.
  Therefore, $E(1_A|U,Z) aseq E(E(1_A|U_H,Z)|U,Z)$.


  Therefore
  $E(psi 1_A|U) aseq E(psi E(psi 1_A|U_H,Z)/E(psi|U_H,Z)|U)$
]


#lemma[
  Let $EE (X|U) = EE (Y|U)$ forall $EE$
  Then $X = Y$.
]
#proof[
  $EE(g|U) = 1$, so
  $EE(g X|U) = EE(g Y|U)$
  Integrating, adding any $f sigma(U) ms$,
  $E(g f Y) = E(g f Y)$.

  Now for general measurable $phi = EE(phi|U) phi/EE(phi|U)$.
  Therefore $EE(phi X) = EE(phi Y)$ for all $phi$, therefore $X = Y$.
]



#lemma[
  If $EE(A|Z) in {0,1}$ for all $A in sigma(U)$,
  $sigma(U) subset.eq sigma(Z)$.
]
#proof[
  trivial
]

#lemma[
  On this $sigma(U) subset.eq sigma(Z)$, we have
  $irrel(X|Z) = I$.
]
#proof[
  $EE(f 1_A|Z)/EE(f|Z) = f/f EE(1_A|Z)$
]

#bibliography("citations.bib")








