#import "template.typ": *
#show: showrules 


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






= Definitions

conditional history

= Main Theorem



= Arbitrary independencies?

$#history (X)$











