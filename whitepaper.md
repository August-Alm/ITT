__SIC__

The Symmetric Interaction Calculus (SIC) is defined by the following grammar:
```
  t, u ::= ()                 nil
         | x                  variable
         | \x.t               abstraction
         | (t u)              application
         | [t, u]             superposition
         | [x, y] <- t; u     duplication
         | free t; u          free
```
Variables are bound by abstractions and duplications, and must occur exactly once in bound positions, i.e., the calculus is linear. _However, bound variables are scoped in the entire term_. For example,
```
[x, y] <- \z.x; free y; free z; ()
```
is a legitimate term. Furthermore, we adopt the convention that the syntactic constructs are linear in duplications and frees, so, e.g.,
```
(free s; t u) ~ free s; (t u)
\x.[y, z] <- t; u ~ [y, z] <- t; \x.u
```
We also assume that the order of sequences of duplications and frees are irrelevant, e.g.,
```
free s; free t; u ~ free t; free s; u
free s; [x, y] <- t; u ~ [x, y] <- t; free s; u
```
Finally, consistently renaming variables is also an equivalence, like in the lambda calculus. We shall refer to all these syntactical equivalences as _alpha-equivalence_.

As usual in variants of lambda calculus, one can define a _context_ to be a term of the grammar extended with a special "hole" term [] that may only occur once. If C is a context, then C[t] denotes the ordinary SIC term, obtained by replacing the distinguished hole with the specified term. The main reduction rules of SIC are:
```
C[(\x.t u)] ~> C[t]{x = u}      applying abstraction

C[[x, y] <- [s, t]; u] ~>       duplicating supersposition
    C[u]{x = s, y =t}

C[([s, t] u)] ~>                applying superposition
    C[[u1, u2] <- u; [(s u1), (t u2)]]

C[[x, y] <- \z.t; u] ~>         duplicating abstraction
    C[[t1, t2] <- t; u]{x = \z1.t1, y = \z2.t2, z = [z1, z2]}
```
The curly brace expressions denote the metatheoretic operation of variable substitution. The variables u1, u2, z1, and z2 above are tacitly assumed fresh. In addition to these, we have the "garbage rules":
```
C[free (); t] ~> C[t]
C[free \x.t; u] ~> C[free t; u]{()/x}
C[free [s, t]; u] ~> C[free s; free t; u]
C[(() t)] ~> C[free t; ()]
C[[x, y] <- (); t] ~> C[t]{x = (), y = ()}
```
We call the closure of the ~> reduction rules and the alpha equivalences _beta-reduction_ and the equivalence it imposes, beta-equivalence.

_Remark 1_
The most attractive property of the SIC is that all the beta reduction rules can easily be implemented as constant time operations. In fact, the calculus has a direct encoding as interaction nets (where the reduction steps are not just constant time, but confluent and naturally parallelizable).

_Remark 2_
It is possible to add notions of eta-equivalence, similar to how it is done in lambda calculus.

__Simply typed SIC__

Define a grammar of types by
```
S, T ::= Unit | S => T | S * T | !T
```
with ! (the "bang", "box" or "exponential") binding tighter than the binary constructors. We shall in what follows tacitly assume that the exponential is idempotent, !! = !, and that !(A * B) = !A * !B.
Also, introduce a subsumption (subtyping) relation S < T by
```
T < T,  !T < T, S * T < S' T' iff S < S' && T < T',
and S => T < S' => T' iff S' < S && T < S,
```
Define a _checkable type__ to be a type that is not boxed (recall, !(S * T) = !S * !T) and also is not an arrow type returning a boxed type. (So, inductively, a type is checkable if it is not boxed or if it is an arrow type returning a checkable type). We will let A, B, C, .. range over checkable types.

Now, let's extend the SIC grammar as follows:
```
t, u ::= ...
       | t : T              annotation
       | check A t          type-check
       | exn                exception
```
Note that annotations can use any type, by type-check only checkable types. Extend alpha-equivalence in the obvious way. We also add new beta reduction rules. The foremost are:
```
C[check A \x.t] ~>            checking abstraction
    if A = T => B then
        C[\x.check B t]{x = x : T}
    else exn

C[check C [s, t]] ~>          checking superposition
    if C = A * B then
        C[[check A s, check B t]]
    else exn

C[(s : T u)] ~>               applying annotation
    if T = A => S or
    if T = !(A => S) then
        C[(s check A u) : S]
    else exn

C[check A (t : T)] ~>           checking annotation
    if A < T then t
    else exn
```
These reduction steps mimic the steps of a type-checking algorithm! The key rule for how the
exponential is brought into play is the following rule:
```
C[[x, y] <- s : U; t] ~>      duplicating annotation
    if U = S * T then
        C[[s1, s2] <- s; t]{x = s1 : S, y = s2 : T}
    elif U = !T then
        C[[s1, s2] <- s; t]{x = s1 : !T, y = s2 : !T}
    else exn
```
Informally, only terms of superposed or exponential type can be duplicated.
Lastly, there are some obvious new garbage rules. The new exception term should essentially behave just like the nil term but we leave it unspecified as it is intended to be an implementation detail.

__Examples__

The garbage rule (left implicit above)
```
check nil A ~> nil
```
says that nil checks agains any checkable type (so we should maybe call it "bottom").

The identity abstraction checks against any type A => A:
```
check \x.x (A => A) ~>
\x.check (x : A) A ~>
\x.x
```
Note that it also checks against any A => B, where A < B is a subtype, e.g. A = !B.

Consider the following incarnation of the Church numeral "two":
```
two = [s1, s2] <- s; \s.\z.(s1 (s2 z))
``` 
Using the "checking abstraction" rule
```
check two !(A => A) => A => A ~>
[s1, s2] <- s : !(A => A);
\s.check \z.(s1 (s2 z)) A => A.
```
Then using the "duplicating annotation" rule once and again the "checking abstraction":
```
[s1, s2] <- s;
\s.\z.check (s1 : !E (s2 : !E z : A)) A
```
with E = A => A. Using the rule "applying annotation" on the inmost application:
```
(s2 : !(A => A) z : A) ~>
(s2 check A (z: A)) : A ~>
(s2 z) : A
```
So we then have
```
[s1, s2] <- s;
\s.\z.check (s1 : !E (s2 z) : A) A,
```
which after another application of the "applying annotation" rule reduces to
```
[s1, s2] <- s;
\s.\z.check ((s1 (s2 z)) : A) A ~>
two.
```
Note that if the type instead was (A => A) => A => A, i.e., without the exponential, then the reduction would have yielded an exception term in the "duplicating annotation" step.

__As a more traditional type theory__

As usual, let's say that a _typing context_ is a list of type annotations of variables. Given such a context, one can in the simply typed SIC discussed above define the substitution
```
t{ctx} := t{x1 = x1 : a1, ..., xN = xN : aN},
```
replacing all variables by their annotated versions. With this notation fixed, we can define the meaning of typing judgements. For checkable types:
```
(check A t){ctx} ~ t
--------------------      (~ means beta equivalence)
ctx |- t : A
```
Using that definition, we define typing with boxed types as:
```
ctx |- t : A    ctx |- [t', t''] <- t; free t''; t' : A
-------------------------------------------------------    box typing
ctx |- t : !A
```
Informally, a term t has type !A if it has type A and duplicates to terms that also have type A.

Now, note that
```
(check S => A \x.t){ctx} ~>
(\x.check A t){ctx, x : S} ~ \x.t
iff (check A t){ctx, x : S} ~ t.
```
It follows that for a checkable type A, we can equivalently define
```
ctx |- \x.t : S => A
```
by the traditional derivation
```
ctx, x : S |- t : A
--------------------
ctx |- \x.t : S => A
```
This latter then generalizes, so we can define typing also of arrows in general (also with non-checkable return types) by:
```
ctx, x : S |- t : T
--------------------
ctx |- \x.t : S => T
```

__Lemma.__ The derivation
```
ctx |- s : S => T      ctx |- t : S
-----------------------------------
ctx |- (s t) : T
```
is always valid.

__Proof.__ (Sketch.) We may assume s = \x.u. We know, from ctx |- s : S => T, that ctx |- (u{x = x : S}) : T, which means (check u{x = x : S} T){ctx} is beta-equivalent to u{ctx}. The reduction of this check-expression must at some point involve steps
```
check S'' (x' : S') ~> x'       (whence S'' < S')
```
with x' a duplicate of x, because the annotations have to dissappear for otherwise the reduction could not possibly be equivalent to u{ctx} (which has no annotated x). The beta-reduction steps are confluent, so we can follow an analogous sequence of reduction steps when reducing (\x.u t) and reach steps with subexpressions
```
check S'' t'
```
where now t' is a corresponding duplicate of t. We must argue that these check-expressions can all be resolved, i.e., that
```
check S'' t' ~ t'
```
There are four cases to consider:

1. No duplication: \x.u is linear in x. In this case x' = x and t' = t, and S' = S. Then check S'' t will be equivalent to t (because we're assuming ctx |- t : S).

2. Exponential duplication: \x.u is nonlinear and S = !A. In this case we also have S' = S = !A (because of the "duplicating annotation" rule). Because of the box typing rule, we moreover know that ctx |- t' : !A, which means that check S'' t' will reduce to t'.

3. Pair duplication: \x.u duplicates x and S = A * B. In this case S' is either A or B. We may assume that t = [t1, t2], so that t' is either t1 or t2, with corresponding type either A or B. Again check S'' t' ~ t.

4. Exponentials and pairs: \x.u is nonlinear and S is a combination of exponential and tuple types. This reduces to a combination of cases (2) and (3).

QED.