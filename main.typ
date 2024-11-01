#import "template.typ": *
#show: showrules 

#show "sigma algebra": it => [$sigma$-algebra]
#show "sect stable": it => [$sect$-stable]


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
&"and" P "is absolutely continuous w.r.t." PP}
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
  $P(Sect_(i=1)^4 A_i|Z) =^((1))P(A_1 sect A_2 | Z) P(A_3 sect A_4 | Z)
  =^((2)) product_(i = 1)^4 P(A_i|Z)$.
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
  Since '$supset.eq$', it suffices to show '$subset.eq$'.

  
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
  Let $cal(I)$ be a set of index functions s.t.
  for any totally ordered set $(S,<=)$ and any random index set family $(J_s)_(s in S)$ with
  $forall s,t in S: s <= t => J_s subsetaseq J_t$, we have
  $Sect^astext_(s in S) J_s in cal(I)$.
  Then there exists a almost surely subset wise minimal element in $cal(I)$.
  Furthermore, if $J,K in cal(I)$ implies $J sect K in cal(I)$, this element is almost surely unique and is given by
  $Sect^astext cal(I)$.
] <lem:random_index_set_zorn>
#proof[
  For existence, apply Zorn's lemma to the random index sets modulo almost sure equality where
  the ordering is given by $J <= K :<=> J subsetaseq K$.
  For unqiueness, assume that $J$ and $K$ are minimizers.
  If $J aseq K$ does not hold, $J sect K aseq J$ does not hold and therefore 
  $J$ is not a minimizer. Similarly, if $Sect^astext cal(I) in.not cal(I)$.
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
  for all $n in NN union {*}$ (1).
  
  Let $n in NN$.
  Then $B sect A_n in Sect_(s in S:s <= s_(n+1)) sigma(U_J_s, Z, AS|_{J_s aseq I})|_A_n$.
  Now since $A_n sect {J_s aseq I} aseq nothing$ for all $s <= s_(n+1)$.
  $sigma(U_J_s, Z, AS|_{J_s aseq I})|_A_n = sigma(U_J_s, Z)|_A_n subset.eq sigma(U_J_s,Z,AS|_{J aseq I})$.
  This shows the claim (1) for all $n in NN$.
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
#notation[
  For ease of notation, we index $P in distributionstimes$ to
  refer to the pushforward under $U_J$.
  More precisely, let $J$ be a random indexset, then
  $P_J := P_U_J$.
]
#lemma[
  Let $i in I$ and $P, Q in distributionstimes$, s.t.
// $P$ and $Q$ differ only for $U_i$,
  // i.e. $P_comp({i}) = Q_comp({i})$.
  // i.e.
  there is a $sigma(U_i) ms$ density $f:Omega -> RR$, s.t. $P = f dot Q$.
  Then for all $A in sigma(X)$ we have
  $P(A|Z)(omega) = Q(A|Z)(omega)$ for a.e. $omega in {i in comp(history(X|Z))}$.
]
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

#definition[
  Let $distributionstimes2(i) := {(P,Q) in distributionstimes times distributionstimes: exists f : Omega -> RR, sigma(U_i) ms, s.t. P = f dot Q}$.
]

#definition[
  Let $J$ be a $sigma(Z) ms$ random index set.
  We say $J$ is irrelevant to $X$ given $Z$, if for any $i in I$ and
  $(P,Q) in distributionstimes2(i)$, we have
  $P(A|Z) = Q(A|Z)$ for all $A in sigma(X)$.
  $frak("I")$
]







#bibliography("citations.bib")








