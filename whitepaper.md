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
We call all the closure of the ~> reduction rules and the alpha equivalences _beta-reduction_ and the equivalence it imposes, beta-equivalence.

_Remark 1_
The most attractive property of the SIC is that all the beta reduction rules can easily be implemented as constant time operations. In fact, the calculus has a direct encoding as interaction nets (where the reduction steps are not just constant time, but naturally parallelizable).

_Remark 2_
It is possible to add notions of eta-equivalence, similar to how it is done in lambda calculus.

__Type-extended SIC__

Let's extend the SIC grammar as follows:
```
t, u ::= ...
       | t => u             arrow
       | x => y <- t; u     deconstruct
       | t : u              annotation
       | check t u          type-check
       | exn                exception
```
Extend alpha-equivalence in the obvious way. We also add new beta reduction rules. The foremost are:
```
C[x => y <- s => t; u] ~>     deconstructing arrow
    C[u]{x = s, y = t}

C[check \x.t u] ~>            checking abstraction
    C[a => b <- u; \x.check t b]{x = x : a}

C[check [s, t] u] ~>          checking superposition
    C[[a, b] <- u; [check s a, check t b]]

C[(s : t u)] ~>               applying annotation
    C[a => b <- t; (s check u a) : b]

C[check s : t u] ~>           checking annotation
    if t ~ u then free t; free u; s else exn
```
These reduction steps mimic the steps of a type-checking algorithm! The equivalence relation ~ in the last rule is beta equivalence, but theoretically we could imagine using some other relation. See the remark at the end of this section, regarding how to precisely work with it. For consistency, we also add the more exotic
```
C[check s => t u] ~>          checking arrow
    C[a => b <- u; (check s a) => (check t b)]
```
and
```
C[[x, y] <- s => t; u] ~>     duplicating arrow
    C[[s1, s2] <- s; [t1, t2] <- t; u]{x = s1 => t1, y = s2 => t2}

C[[x, y] <- s : t; u] ~>      duplicating annotation
    C[[s1, s2] <- s; [t1, t2] <- t; u]{x = s1 : t1, y = s2 : t2}
```
as well as a bunch of obvious garbage rules. The new exception term should essentially behave just like the nil term but we leave it unspecified as it is intended to be an implementation detail.

_Remark_ There ought to be efficient ways to check beta equivalence without doing reduction to beta-normal form, using an interaction net encoding and the work by Mazza and LaFont, comparing "execution paths" in the manner of "geometry of interaction"; see Mazza's paper "Observational equivalence and full abstraction in the symmetric interaction combinators". We have not worked out the details.

__As a more traditional type theory__

As usual, let's say that a _typing context_ is a list of type annotations of variables. Given such a context, one can in the type-extended SIC discussed above define the substitution
```
t{ctx} := t{x1 = x1 : a1, ..., xN = xN : aN},
```
replacing all variables by their annotated versions. With this notation fixed, we can define the meaning of typing judgements:
```
(check t u){ctx} ~ t
--------------------
ctx |- t : u
```
Here, we can restrict "t" to be a term of the usual SIC, and "u" to be a term of some restricted subgrammar corresponding to types (e.g., not itself involving any type-check constructors).

_Remark_
Is this sensible? I think it is pretty well-defined at least.

__Examples and questions__

The identity abstraction has nil type:
```
check \x.x () ~>
s => t <- (); \x.check (x : s) t ~>
\x.check (x : ()) () ~>
free (); free (); \x.x ~>
\x.x
```
Also,
check \x.x (a => a) ~>
s => t <- (a => a); \x.check (x : s) t ~>
\x.check (x : a) a ~>
free a; free a; \x.x ~>
\x.x
assuming a can be fully freed. (Should ~ always discard "free terms"?)
On the other hand,
```
[a1, a2] <- a; check \x.x (a1 => a2) ~>
[a1, a2] <- a; t1 => t2 <- (a1 => a2); \x.check (x : t1) t2 ~>
[a1, a2] <- a; \x.check (x : a1) a2
```
If a = [b, b], then it checks out. If a = \t.t, then
```
[a1, a2] <- \t.t; u ~> u{a1 = \t1.t1, a2 = \t2.t2}
```
and it also checks out. The lesson here seems to be that there are no polymorphic identity arrow types a => a because the language of types is linear; the best we have is [a1, a2] <- a; (a1 => a2) -- which is an identity arrow type only when the type a can be truly duplicated.