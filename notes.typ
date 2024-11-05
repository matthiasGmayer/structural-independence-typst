
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





#pagebreak()

= Trashbag
#theorem[
  Let $PP_n -> PP$.
  Then $EE_n (X|Z) dot PP_n -> EE (X|Z) dot PP$.
  or maybe
  $EE_n (X|Z) dot PP -> EE (X|Z) dot PP$.
]


#theorem[
  Let $PP_n -> PP$, then
  $sqrt(EE_n (X|Z)) -> sqrt(EE(X|Z))$ in $L^2$.

  normed?
]
#proof[

  
  $
  integral (sqrt(EE_n (X|Z)) - sqrt(EE(X|Z)))^2  dif PP \

  -2 integral sqrt(EE(p_n X|Z)/ EE(p_n|Z) EE(X|Z)) dif PP

  + integral EE(p_n X|Z)/EE(p_n|Z) dif PP
  + integral EE(X|Z) dif PP
  // = integral (sqrt(EE(p_n X|Z)/EE(p_n|Z)) - sqrt(EE(X|Z)))^2  dif PP \
  $


  // $
  // integral sqrt(EE(p_n X|Z)/ EE(p_n|Z) EE(X|Z)) dif PP \
  // integral EE(p_n X|Z)/ EE(p_n|Z) EE(X|Z) sqrt(EE(p_n|Z)/(EE(p_n X|Z) EE(X|Z))) dif PP \
  // $

  $
  integral sqrt(EE(p_n X|Z)/ EE(p_n|Z) EE(X|Z)) dif PP
  &>= integral EE_n (sqrt(X) | Z) EE(sqrt(X)|Z) \
  &= integral EE (p_n sqrt(X) | Z) 1/EE(p_n|Z) EE(sqrt(X)|Z) dif PP. \
  &= integral EE (p_n sqrt(X) | Z) EE(sqrt(X)/EE(p_n|Z)|Z) dif PP. 
  
  $

  $
  integral sqrt(EE(p_n X|Z)/ EE(p_n|Z) EE(X|Z)) dif PP
  &>= integral EE (sqrt(p_n X) | Z) EE(sqrt(X/EE(p_n|Z))|Z) dif PP \
  &= integral sqrt(p_n X) EE(sqrt(X/EE(p_n|Z))|Z) dif PP \
  &= integral sqrt(X) EE(sqrt(X)|Z) sqrt(p_n/EE(p_n|Z)) dif PP \
  $

  Or

  
  $
  integral sqrt(EE(p_n X|Z)/ EE(p_n|Z) EE(X|Z)) dif PP
  &= integral sqrt(X EE(X|Z)) sqrt(p_n/EE(p_n|Z)) dif PP \
  &= integral EE(sqrt(X EE(X|Z)) sqrt(p_n/EE(p_n|Z)))|Z dif PP \
  &= integral EE(sqrt(X EE(X|Z)) sqrt(p_n))|Z) 1/sqrt(EE(p_n|Z)) dif PP \
  $


  $EE(sqrt(p_n)) -> 1$.

  $EE(sqrt(EE(p_n X|Z))) >= EE(sqrt(p_n X)|Z)$.
  
]

#definition[
  $X_n -> X$ if $EE_n (1_A X_n) -> EE(1_A X_n)$ .
]
Uniqueness, limit nice

#lemma[
  If $PP_n -> PP$, then $PP_n (X|Z) -> PP (X|Z)$.
]
#proof[
  Clearly it suffices to show for $C in sigma(Z)$.
  Let 
  $integral_C PP_n (X|Z) dif PP_n = integral_C X dif PP_n -> integral_C X dif PP$
  which is equal to $integral_C PP(X|Z) dif PP$.
]

#lemma[
  If $PP_n -> PP$ and $PP'_n -> PP$, then $X_n -> X <=> X_n ->' X$.
]
#proof[
  First use $A_n -> A$.
  Suppose $A_n ->' B$.
  Then there is w.l.o.g. $C subset.eq A without B$ nonnull.

  Then
  $
  integral_C A_n dif PP_n -> PP(A sect C).
  $

  and
  $
  integral_C A_n dif PP'_n -> 0.
  $

  Then $PP(C) > 0$.
  Then $PP(C_n) > 0$.
  
]

#lemma[
  If $PP_n -> PP$. $X_n -> Y$ and $X_n -> Z$, then $Y aseq Z$.
]
#proof[
  Suppose $Y asneq Z$.
  Then w.l.o.g. ${Y < Z} in.not NS$.
  Then there is $epsilon$, s.t. $A = {Y + epsilon < Z} in.not NS$.

  Then $PP_n (A) -> PP(A) > 0$, s.t.
  $integral_A abs(Y - Z) dif PP_n -> integral_A abs(Y-Z) dif PP > epsilon PP(A)$.
]

#lemma[
  If $P = f Q$, and $P_n -> P$, $Q_n -> Q$,
]

! If i show anything for $EE_n (X|Z) -> EE (X|Z)$, then i can choose $Z=AS$ and get for $X$.

I.e. we need to show

#lemma[
  Let $PP_n -> PP$ in $norm(dot)_2$ then for all bounded $X$, $X -> X$ in averages.
]
TRIVIAL!


#corollary[
  Let $PP_n -> PP$ in $norm(dot)_2$ then for all bounded $X$, $sqrt(EE_n (X|Z)) -> sqrt(EE(X|Z))$ in $L^2$.
]
#proof[
  Let $C in sigma(Z)$.
  Then $integral_C EE_n (X|Z) dif PP$
]




#theorem[
  Let $PP_n -> PP$ in $norm(dot)_2$ then for all bounded $X$, $EE_n (X|Z) -> EE(X|Z)$ in measure.
]
#proof[
  We proceed by measure-theoretic induction over $Z$.
  W.l.o.g. $X$ is bounded by $1$ and positive. 
  + Let $C in AS without NS$.
    Then $EE_n (X|C) = EE_n (1_C X) slash PP_n (C) -> EE (1_C X)slash PP(C) =EE (X|C)$.
  + Let $sigma(Z)$ be generated by a finite partition $cal(P) subset.eq AS without NS$. \
    Then $EE_n (X|Z) = sum_(C in cal(P)) EE_n (X|C) -> sum_(C in cal(P)) EE (X|C) = EE(X|Z)$ in $L^oo$.
    More precisely,
    $norm(EE_n (X|Z) - EE(X|Z))_oo <= sup_(C in cal(P)) abs(PP_n (C)""^(-1) - PP (C)""^(-1)) -> 0$.
  + Let $sigma(Z)$ be generated by a sequence $(A_n)_(n in NN)$, where $A_n in AS$.
    Set $Z_n := sigma(A_1,...,A_n)$.
    Then $Z_n arrow.t Z$ and by levy's upward theorem, $EE(X|Z_n) -> EE(X|Z)$ both almost surely and in $L^1$.
    Therefore, there is $n_0 in NN : forall n >= n_0:
    PP{abs(EE(X|Z_n) - EE(X|Z))>delta} < epsilon$
    and
    $PP_n {abs(EE(X|Z_n) - EE(X|Z))>delta} < epsilon 2^(-n)$.

    $norm(EE_n (X|Z) - EE (X|Z))$

    becomes 
    $
    norm(EE_n (X|Z) - EE_n (X|Z_m)) \
    norm(EE_n (X|Z_m) - EE (X|Z_m)) \
    norm(EE (X|Z_m) - EE (X|Z)) \
    $

    First fix $m$ last is small.
    Then for large $n$ second is small.
    First can be LARGE.
    
]

#theorem[
  Let $P_n -> P, Q_n -> Q$ and $P_n (A|Z) = Q_n (A|Z)$ then
  $P(A|Z) = Q(A|Z)$.
]
#proof[
  We have $P_n (A|Z) -> P(A|Z)$. for $P_n$.
  Then also $P_n (A|Z) P_n (q|Z) -> P(A|Z) P_n (q|Z)$. for $P_n$.
  Then $Q_n (A|Z) ->$

  $
  integral_C P_n (A|Z) dif P_n -> P(A sect C)
  $

  $
  integral_C P_n (A|Z) dif Q_n
  $

  


  Density,

  $P_n (B|Z) aseq Q_n (B|Z)$ for all $n$.
  $P_n -> P$, $Q_n -> Q$.


  $integral_C P (B|Z) dif P = integral_C 1_B dif P
  = lim_n integral_C P_n (B|Z) dif P_n
  = lim_n integral_C Q_n (B|Z) dif P_n
  = lim_n integral_C 1_B dif Q_n = integral_C Q(B|Z) dif Q$.

  $integral_C P (B|Z) dif PP = integral_C 1_B dif P
  = lim_n integral_C P_n (B|Z) dif P_n
  = lim_n integral_C Q_n (B|Z) dif P_n
  = lim_n integral_C 1_B dif Q_n = integral_C Q(B|Z) dif Q$.

  // $integral_C PP(B g |Z)/PP(g|Z) dif P =
  // lim_n integral PP(B g | Z)/PP(g|Z) dif P_n =
  // lim_n integral PP(B g | Z)/PP(g|Z) dif Q_n =
  // $

  
  

  
  // Define $phi_(lambda) := product (lambda phi_i + comp(lambda))$

  // $phi_lambda$ well-defined and $L^oo$ continuous in $lambda$?

  // Idea:

  // $phi_lambda = sum lambda^k$

  // $
  // product_(n=1)^m (lambda phi_n + comp(lambda))
  // &= sum_(S subset.eq {1,...,m}) (1-lambda)^(m-|S|) lambda^(abs(S)) product_(s in S) phi_n \
  // &= sum_(S subset.eq {1,...,m})
  // (sum_(n = 0)^(m-abs(S)) lambda^(m -abs(S) - n) (-1)^n
  // lambda^(abs(S)))
  // product_(s in S) phi_s \
  // &= sum_(S subset.eq {1,...,m})
  // sum_(n = 0)^(m - abs(S)) lambda^(m - n) (-1)^n
  // product_(s in S) phi_s \
  // $


  // $sum_(n =1)^oo log(1 - lambda(1 - phi_n))$


  // $product_i integral sqrt(phi_i) dif Q < oo$

  // $
  // product_i integral sqrt((phi_i+1)/2) dif Q
  // &= product_i 1/sqrt(2) integral sqrt(phi_i+1) dif Q \
  // &= product_i integral sqrt((phi_i+1)/2) dif Q \
  // $
  
  
]




$phi_lambda = sqrt(lambda) phi+ (1-sqrt(lambda))$

$norm(phi_lambda - phi)^2_2
= integral (sqrt(lambda) - 1)^2 (phi - 1)^2  dif PP \
= (sqrt(lambda) - 1) norm(phi - 1)_2^2
$


$phi_lambda = lambda phi+ (1-lambda)$

$norm(phi_lambda - phi)^2_2
= integral (lambda - 1)^2 (phi - 1)^2  dif PP \
= (lambda - 1) norm(phi - 1)_2^2
$



$
integral sqrt((dif P)/(dif Q)) dif Q > 1- epsilon => norm(P(A|Z) - Q(A|Z)) < epsilon?
$



$angle.l a,b angle.r in B_epsilon (1) => norm(a-b) < epsilon$

$epsilon >= norm(sqrt(phi) - sqrt(psi))_2 >= norm(sqrt(phi) - sqrt(psi))_1 $



$abs(x - y) < epsilon => abs(x^2 - y^2) =$

$
=> norm(sqrt(P(A|Z)Q(A|Z))) > 1-epsilon?
$


$
sqrt(P(A|Z)Q(A|Z)) =
sqrt(EE(p A|Z)/EE(p|Z) EE(q A|Z)/EE(q|Z)) >=^"jensen"
EE(sqrt(p) A|Z)/sqrt(EE(p|Z)) EE(sqrt(q) A|Z)/sqrt(EE(q|Z))
>= ^"am/gm"
2(EE(sqrt(p) A|Z)EE(sqrt(q) A|Z))/(E(p|Z) + E(q|Z)) \
= 2 P(A slash sqrt(p)|Z) Q(A slash sqrt(q) |Z)
$


Jensen f convex $f(EE(X|Z)) <=EE(f(X)|Z)$.

f concave $-f(EE(X|Z)) <= EE(-f(X)|Z) <=> f(EE(X|Z)) >= EE(f(X)|Z)$.
Therefore,$X>=0$, $sqrt(EE(X|Z)) >= EE(sqrt(X)|Z)$.






#lemma[
  Let $PP_n -> PP$ in $norm(dot)_2$, then for all $A in AS$, $PP_n (A) -> PP(A)$.
]
#proof[
  Let $p_n := (dif PP_n)/(dif PP)$.
  Then $EE(sqrt(p_n)) -> 1$.
  Let $q_n := EE(p_n|sigma(A))$
  By @lem:eucl_density_cond_exp, $EE(sqrt(q_n)) = PP(A) sqrt(EE(p_n|A)) + PP(A^c) sqrt(EE(p_n|A^c)) -> 1$,
  while $EE(1_A p_n) = EE(1_A q_n)$.
  We want to show that $PP_n (A) = PP(A) EE(p_n|A) -> PP(A) <=> EE(p_n|A) -> 1$.

  Set $a_n = EE(p_n|A), b_n = EE(p_n|A^c)$
  and $lambda = PP(A), comp(lambda) = (1-lambda)$.
  Then $a_n in [0,1/lambda],b_n in [0,1/(1-lambda)],lambda in [0,1]$, and
  $lambda sqrt(a_n) + comp(lambda) sqrt(b_n) -> 1$ and $lambda a_n + comp(lambda) b_n = 1$.
  We want to conclude that $a_n -> 1$.

  Define the function $f : [0,1] -> RR; x|-> lambda sqrt(x) +  sqrt(comp(lambda)(1 - lambda x))$.
  Then $f(a_n) -> 1$. Moreover,

  $f'(x) = lambda 1/(2sqrt(x)) -  lambda sqrt(1-lambda)/(2sqrt(1-lambda x)) 
  = lambda/2 (1/sqrt(x) -   sqrt((1-lambda)/(1-lambda x))).
  $
  Now
  $
  f'(x) > 0
  &<=> lambda/2 (1/sqrt(x) -   sqrt((1-lambda)/(1-lambda x))) > 0 \
  &<=> 1/sqrt(x) >   sqrt((1-lambda)/(1-lambda x))\
  &<=> 1- lambda x >   (1-lambda)x\
  &<=> x < 1\
  $
  Similarly, $f'(x) < 0 <=> x> 1$ and $f'(1) =0$.
  Therefore $f(1)=1$ is a global maximum and
  so $f(a_n) -> 1$ implies $a_n -> 1$.
]

#corollary[
  Let $PP_n -> PP$ in $norm(dot)_2$, then for all bounded $X$, $EE_n (X) -> EE(X)$.
]
#proof[
  It clearly is true for simple $X$.
  Now take uniformly approximating simple $X_n$.
]

#example[
  Let $PP_n -> PP$ then $EE_n (X) -> EE(X)$ does not hold in general for $X in Sect_(n in NN) L^1 (PP_n) sect L^1 (PP)$.
  Indeed let $PP$ be the uniform distribution on $[0,1]$.
  Let $X(x) = 1/(2sqrt(x))$. Clearly, $integral_0^1 X dif PP = 1$.
  Let $f_n = 1_[0,1/2^n] n + 1_[n/2^n,1]$.
  Then $integral f_n dif PP = 1$.
  and $integral sqrt(f_n) dif PP = sqrt(n)/(2^n) + 1-n/(2^n) -> 1$.
  Now $integral f_n X = n integral_0^(1/n) 1/(2 sqrt(x)) + integral_(n/(2^n))^1 1/(2 sqrt(x)) >= sqrt(n)$.
]



#corollary[
  Let $PP_n -> PP$,
  then $EE (sqrt(phi_n X)) -> EE (sqrt(X))$ for all $X in L^1 (PP)$.
]
#proof[
  Note that $angles(sqrt(phi_n), sqrt(X)) -> angles(1, sqrt(X))$, i.e.
  $EE(sqrt(phi_n X)) -> EE(sqrt(X))$.
]

#corollary[
  Let $PP_n -> PP$,
  then $EE (sqrt(phi_n) X) -> EE (X)$ for all $X in L^2 (PP)$.
]
#proof[
  Note that $angles(sqrt(phi_n), sqrt(X)) -> angles(1, sqrt(X))$, i.e.
  $EE(sqrt(phi_n X)) -> EE(sqrt(X))$.
]

#corollary[
  Let $PP_n -> PP$,
  $X_n -> X$ in $L^2(PP)$,
  Then $EE(sqrt(phi_n) X_n) -> EE(X)$.
]
#proof[
  $angles(sqrt(phi_n),X_n) -> angles(1,X) = EE(X)$.
]

#lemma[
  Let $PP_n -> PP$ and $A in AS$.
  Then $PP_n (A|Z) -> PP(A|Z)$ in measure w.r.t $PP$.
]
#proof[
  Let $phi_n$ be a density, s.t. $PP_n = phi_n dot PP$.
  Recall that $PP_n (A|Z) = EE(phi_n 1_A|Z) slash EE(phi_n|Z)$.
  
  Since $sqrt(phi_n) -> 1$ in $L^2$, we have
  $sqrt(EE(phi_n|Z)) -> 1$ in $L^2$ by ??.

  
  Let $delta > 0$.
  We need to show
  $PP(abs(EE(phi_n 1_A|Z) slash EE(phi_n|Z) - EE(1_A|Z))> delta) -> 0$.

  Let $epsilon > 0$, to be chosen later.
  Since $sqrt(phi_n) -> 1$ in $L^2$, we have
  $sqrt(EE(phi_n|Z)) -> 1$ in $L^2$ by ??.

  Therefore,
  $EE(phi_n|Z) -> 1$ in $PP$-measure.
  
  Now $PP(abs(sqrt(EE(phi_n|Z)) - 1) > epsilon) -> 0$ by $L^2$ convergence
  and $PP(abs(EE(phi_n A) - EE(A|Z)) > epsilon) -> 0$ by $L^1$ convergence.

  // Now clearly,
  // $abs(sqrt(a) - 1) <= epsilon => sqrt(a) = 1 + delta => a = 1 + 2 delta + delta^2$.
  // In conclusion $abs(a - 1) <= 2 epsilon + epsilon^2$
  

  Now for $tilde(epsilon) = (epsilon^2 + 2 epsilon)/(1 - 2 epsilon)$ and $rho = tilde(epsilon) (1+epsilon) + epsilon > 0$ we have for $a,b,c in [0,oo)$,
  where $c<=1$ with $abs(sqrt(a)-1) <= epsilon$ and $abs(b-c) <= epsilon$ that
  $abs(b/a - c) <= rho$.
  It is clear, that we can choose $epsilon > 0$, s.t. $rho < delta$.

  To prove this bound, note that
  $abs(sqrt(a) - 1) < epsilon$ implies that there is $xi in [-epsilon,epsilon]$ s.t. $sqrt(a) = 1+xi$.
  Then $1/a$ = $1/(1+xi^2 + 2 xi)$ and $abs(1/a - 1) = abs((xi^2 + 2 xi)/(1 + xi^2 + 2 xi)) <= (xi^2 + 2 xi)/(1 - 2 xi) <= tilde(epsilon)$.
  Now $abs(b/a - c) = abs(b/a - b) + abs(b + c) <= abs(1/a - 1) b + epsilon <= tilde(epsilon) b + epsilon$.
  Since $b <= abs(b-c) + 1 <= 1 + epsilon$,
  we have $abs(b/a - c) <= tilde(epsilon) (1+epsilon) + epsilon = rho$

  Therefore substituting $a = EE(phi_n|Z)(omega), b = EE(phi_n 1_A|Z)(omega), c= EE(1_A|Z)(omega)$
  for appropriate $omega$,
  $
  &PP(abs(EE(phi_n 1_A|Z) slash EE(phi_n|Z) - EE(1_A|Z))> delta) \
  <=&
  PP(abs(sqrt(EE(phi_n|Z)) - 1) > epsilon) +
  PP(abs(EE(phi_n A) - EE(A|Z)) > epsilon) -> 0. 
  $
  This concludes the proof.
]

#lemma[
  Let $phi_n -> 1$ in $L^1 (PP)$ and $X in L^oo$.
  Then $EE(phi_n X|Z)/EE(phi_n|Z) -> EE(X|Z)$ in $PP$-measure.
]
#proof[
  Clearly, $EE(phi_n X|Z) -> EE(phi X|Z)$ and $EE(phi_n|Z) -> EE(phi|Z)$ in $L^1(PP)$ and therefore in $PP$-measure.
  Therefore, $$
]




#lemma[
  Let $PP_n -> PP$ and $X$ be bounded. Then $EE_n (X|Z) -> EE(X|Z)$ in $PP$-measure.
]
#proof[
  WLOG $0 <= X <= 1$.
  Let $phi_n$ be a density, s.t. $PP_n = phi_n dot PP$.
  Recall that $PP_n (A|Z) = EE(phi_n 1_A|Z) slash EE(phi_n|Z)$.
  Since $sqrt(phi_n) -> 1$ in $L^2$, by ?? we have
  $sqrt(EE(phi_n|Z)) -> 1$ in $L^2$ and in measure.
  Clearly, $EE(phi_n X|Z) -> EE(X|Z)$ in $L^1$ and in measure.
  
  Define $f(x,y) = x/y^2 1_(y > 0.1)$. Then $f$ is continuous on $RR times RR_(>0.1)$
  while $(EE(phi X|Z),EE(phi|Z))$ is contained in $[0,1] times [0.5,1.5]$ almost surely.
  By @lem:conv_measure_cont_func
  $EE_n (X|Z) = f(EE(phi_n X|Z),EE(phi X|Z)) -> f(EE(X|Z),1) = EE(X|Z)$ in measure.
]





po

#lemma[
  Let $PP_n -> PP$ in $L^1$ and $X$ be bounded.
  Then $EE_n (X|Z) -> EE(X|Z)$ in $PP$-measure.
]
#proof[
  W.l.o.g. $0<= X <= 1$.
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
  
  Define $f(x,y) = x/y^2 1_(y > 0)$. Then $f$ is continuous on $RR times RR_(>0)$
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