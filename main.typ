#import "template.typ": *
#show: showrules 

#show "sigma algebra": it => [$sigma$-algebra]


#align(center)[Writing notes]

In the intro we explain
d-separation and what it does.
We explain that there is D-separation and that it views functions as general position, but there was no theory for a fixed function until Garrabrant, Mayer et al. Having fixed functions makes the theory applicable to structural equations models.

This develops into a nice mathematical theory.

(Counterexample where?)

Overview over definitions

Define the basic notions

Theorem


Open:  Cyclic models

Open: continuous time

Open: How to make SEM directions identifiable

#pagebreak()

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

Independence is arguable the most important concepts in probability theory.
(Why?)
Often we assume that the independence of variables informs about the structure of the process that generated these variables.
We will formalize what it means for an independence to come from the structure of a process, this is called _structural independence_.
Under the assumption that the observed independences are coming from the process, it is possible to gain information about the process, this is called _discovery_. We will see causal discovery.


We will explain more about structural indpendence 


We observe a set of variables $V$ and we want to express their independence relationships.
We can do this through bayesian networks.
We assume common notation for graphs and leave the details to an appendix.

#definition[bayesian network][
  A bayesian network is a directed acyclic graph (DAG) $G$ with nodes $V$.
  A distribution $P in distributions(Val(V))$ is compatible with $G$
  if it fulfills the markov condition, i.e. for any $X in V$ and $Y in V$ with 
  $X cancel(arrow) Y$ we have $X indep_PP Y | PA(X)$.
  Let $distributions(G)$ denote all probability distributions over $V$ that are compatible with $G$.
]

From the definition of compatibility it is clear that for any $X cancel(arrow) Y$ we have $forall PP in distributions(G): X indep_P Y | PA(X)$, but we can also go further and characterize all independences between sets of variables
that arise in all compatible distributions.

#definition[d-separation][
  Let $X,Y,Z$ be sets of variables.
  Then $X$ and $Y$ are d-connected given $Z$
  if there is a trail from a node in X
  to a node in $Y$ on which every node is a collider if and only if it is in $Z$.
  $X$ and $Y$ are d-separated given $Z$ if they are not d-connected.
]

#theorem[
  Let $X,Y,Z$ be sets of variables.
  Then $X$ and $Y$ are d-seperated from $Z$ if and only if
  they are independent in all distributions compatible with $G$.
]



From this we can motivate the following definition.

#definition[structural independence][
  Let $X,Y,Z$ be random variables a sample space $Omega$.
  Let $distributions$ be a class of probability distributions on $Omega$.
  Then $X$ and $Y$ are structurally independent given $Z$ w.r.t. $distributions$ if they are independent in all probability distributions in $distributions.$ We write $orth_distributions$ for the structural independence relation w.r.t. $distributions$. Therefore,
  $
  X orth_distributions Y | Z :<=> forall PP in distributions : X indep_PP Y | Z.
  $
]

We can now further motivate why this is good definition informally:

We argue that '$=>$' has to hold for any reasonable definition for structural independence. This is because once you endow your structure with a probability distribution, i.e. a specific realization of your model, the independences that you argued structurally, should be realized as well.

'$arrow.l.double$' means that structural independence is the largest relation that fulfills these requirements.


Now the key part is that we want to characterize the structural independence for nice classes of distributions. We already saw the example of bayesian networks.
Bayesian networks have the problem that their independence criterion only works for sets of nodes and not for arbitrary random variables.
We will see that we can use our theory to fully characterize structural independence for all random variables defined on the graph.


In general we can't characterize independence in terms of simple properties, since we can choose any singleton set as our reference class.

We are interested in nice classes.
One first definition we can do is look at all distributions with a certain independence structure.
But even this sometimes singles out one distributions. (e.g. uniform distribution on 4 elements).

We are interested in independencies where changing numerical values around does not change the independencies.

i.e.

Let $distributions$ be induced by some partial independence relation $indep$.
Then we can look at a particular instance

$
X indep_PP Y | Z
$

Then clearly for a $X ms$ $Z$ density $f$ and
$Y ms$ $Z$ denstity $G$ we have

and we have for $Q := f dot g dot PP(dot | Z)$ that
$X indep_Q Y | Z$.
But other relations can be destroyed.
We require that all relations are retained under such transformations.
(This is too strong for continuous time)


We now want to see that this makes structural independence compositional.

#theorem[
  Let $PP$ be a probability distribution over $Omega$. Further let $X : Omega -> RR$ and $f$ be a density w.r.t. $PP$.
  Let $PP' := f dot PP$.
  We have
  $EE'(X|Z) dot EE(f | Z) = EE(f dot X | Z) $.
]
#proof[
  Note that $EE'(X|Z) EE(f|Z)$ is $Z ms$. Let $C in sigma(Z)$. Then
  $
  integral_C EE'(X|Z) EE(f|Z) dif PP
  &= integral_C EE'(X |Z) dif EE(f|Z) PP \
  &= integral_C EE'(X |Z) dif f PP \
  &= integral_C X dif f PP \
  &= integral_C f dot X dif PP
  $
  The second equality follows from
  $(EE(f|Z) PP)|_sigma(Z) = (f PP)_sigma(Z)$ by definition of conditional expectation.
]

#corollary[
  Let $f$ be a probability density w.r.t. $PP$ and $PP' := f PP$, then
  $A indep_P' B | Z <=> EE(f 1_A | Z) EE(f 1_B | Z) = EE(f | Z) EE(1_(A sect B) | Z)$.
]


#lemma[
  Let $X indep Y | Z$ and
  $X' indep Y | Z$
  then
  $(X,X') indep Y | Z$.
  and therefore $(X,X',Y)$ is independent given $Z$.
]
#proof[
  Let $A in sigma(X)$ and $A' in sigma(X')$.
  Let $B in sigma(Y)$.
  It suffices to show that $A sect A' indep B | Z$.

  By applying our assumption to $1_A'$, we get
  with independence of $A$ and $B$ given $Z$ w.r.t. $PP':= PP(dot | A')$ that

  $
  PP(A,A'|Z) PP(B, A'| Z) = PP(A'|Z) PP(A,A',B|Z) \
  $
  using independence of $A'$ and $B$ given $Z$ we get

  $
  PP(A,A'|Z) PP(B|Z) = PP(A,A',B|Z).
  $
  

  // Set $Q_lambda (S) = (lambda 1_A + comp(lambda) 1_(A^c) ) dot PP (S) = lambda PP(S sect A) + comp(lambda) PP(S sect A^c) $.

  // Note that
  // $QQ_lambda (S | Z) =(lambda PP(S A|Z) + comp(lambda)PP ( S A^c|Z))/(lambda PP(A|Z) + comp(lambda) PP (A^c|Z))$

  // By our assumptions we have
  // $A' indep_Q_lambda B | Z$.

  // Therefore
  // $
  // (lambda PP(A' A|Z) + comp(lambda)PP (A' A^c|Z))
  // (lambda PP(B A|Z) + comp(lambda)PP (B A^c|Z))
  // = (lambda PP(A|Z) + comp(lambda) PP (A^c|Z))
  // (lambda PP(A' B A|Z) + comp(lambda) PP (A' B A^c|Z))
  // $

  // collecting terms by lambda, we have


  // $
  // A' A dot B A - A' A^c dot B A^c = A dot A' B A - A^c dot A' B A^c \
  // (A' A  - A' A^c) dot B A^c  + (B A - B A^c) dot A' A^c
  // = (A'B A  - A'B A^c) dot A^c  + (A - A^c) dot A' B A^c \
  // A' A^c dot B A^c = A^c dot A' B A^c \
  // 1+3: A' A dot B A = A dot A' B A \
  
  
  // $


  
  




  
  // $
  // PP(A,A' | Z) PP(B | Z) = PP(A,A',B | Z) \
  // <=> PP(A,A' | Z)  = PP(A,A',B | Z)/PP(B | Z) \
  // $
  
  // $
  // PP(A,A' | Z) PP(B | Z) = PP(A,A',B | Z) \
  // <=> PP(B | Z)  = PP(A,A',B | Z)/PP(A,A' | Z) \
  // $


  // $
  // PP_A' (A | Z) PP_A' (B | Z) = PP_A' (A,B | Z) \ 
  // PP (A lambda A' comp(lambda) A'^c | Z) PP (A' B | Z) = PP(A'|Z) PP (A' A B | Z) \ 
  // $
  
]






= Preliminaries

#let ground = $Omega$
#let groundalg = $AS$
#let groundprob = $PP$

// #let factor = $Omega$
// #let factoralg = $AS$
// #let factorprob = $PP$

// 
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


Which independencies in $PP$ are implied by $U_i$ being independent?



To formalize this question, we let
$
distributionstimes := {P : AS' -> RR |& P "is a probability measure,"\
&(U_i)_(i in I) "is an independent family w.r.t." P \
&"and" P "is absolutely continuous w.r.t." PP}
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
We want to say that $X indep_P Y$ for all $P in distributionstimes$ implies that
there are $J, K subset.eq I$ disjoint, s.t.
$sigma(X) subset.eq sigma(U_J)$ and
$sigma(Y) subset.eq sigma(U_K)$.
We will later see that this is indeed the case.

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
Even if $J_z$ and $K_z$ are disjoint, we cannot conclude independence.
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
]

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
]
#proof[
  Note that $J^(-1){K subset.eq I : i in K} = {omega in Omega: i in J(omega)}$.
  The statement now follows directly from the definition of a random index set (@def:random_index_set).
]

#definition[
  Let $(X_i)_(i in I)$ be a family of random elements.
  Let $J subset.eq I$. Then we denote by
  $X_J := (X_i)_(i in J)$, the restriction of this family to $J$.
]

Canonically, $X_J$ is a random element by 
$(X_i)_(i in J) (omega) = (X_i (omega))_(i in J)$.


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


\
We now want to see how random families behave w.r.t. set operations on their
random index sets. \

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
]
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
&"and" P "is absolutely continuous w.r.t." PP}
$

*In the following* $X,Y$ and $Z$ will be arbitrary random elements.
#notation[completed sigma algebras, almost sure][
  Let $NS = {A in AS: PP(A) = 0}$ be the nullsets w.r.t. $PP$.
  For ease of notation, we will assume all sigma algebras to be complete w.r.t. the reference measure $PP$.
  $AS$ is already assumed to be complete and whenever
  we write $sigma(dot)$, we mean the generated sigma algebra, completed w.r.t. $PP$,
  i.e. $sigma(dot) = sigma(dot,NS)$
  Furthermore, we consider the set relation up to nullsets. For clarity, we will keep writing 'a.s.'
  on top of the relations.
  More precisely,
  $A subsetaseq  B :<=> B without A in NS$ and
  $A aseq B :<=> A without B  union B without A in NS$.
]


We can now use random index sets to describe the dependance on $U$ as $Z$ varies.
Let $Sigma$ denote the set of all sub sigma algebras of $AS$.

Our goal is to construct a map we will call history, $history(dot|dot) : Sigma times Sigma -> powerset(I)^Omega$
that measures the dependence on $U$ of a sigma algebra given another sigma algebra with a random index set.
We write $history(X|Z)$ for $history(sigma(X)|sigma(Z))$.
We now give a list of desiderata that will be shown to completely determine $history$.

+ $history(X|Z)$ is a $sigma(Z) ms$ random index set.
+ Almost sure disjointess of the histories characterizes independence for all product distributions in $distributionstimes$. 
  More precisely,
  $forall P in distributionstimes: X indep_P Y | Z <=> history(X|Z) sect history(Y|Z) aseq nothing.
  $
+ Whenever $U_i$ depends on $U$, it should depend on $U_i$. More precisely,
  For a.e. $omega in Omega$, $history(U_i|Z)(omega) != nothing => i in history(U_i|Z)(omega)$.
+ Monotonicity: if $sigma(X) subset.eq sigma(Y)$ then $history(X|Z) subset.eq history(Y|Z)$.
+ Given $Z$, $Z$ should not depend on $U$: $history(Z|Z) aseq nothing$.






= The Fundamental Theorem of Structural Independence
<sec:fundamental_theorem>




#bibliography("citations.bib")








