\documentclass[format=sigconf, screen=true, review=false]{acmart}

\usepackage{fancyvrb}    %% Source Code listings
\usepackage{mathpartir}  %% Type Inference Rules

\DefineVerbatimEnvironment{code}{Verbatim}{fontsize=\small}
\DefineVerbatimEnvironment{spec}{Verbatim}{fontsize=\small}
\DefineVerbatimEnvironment{repl}{Verbatim}{fontsize=\small}
\DefineShortVerb{\|}

\newcommand{\ignoreCode}[1]{}
\newcommand
  {\creduce}
  [2]
  {#1 \rightarrow #2}
\newcommand
  {\creduced}
  [2]
  {#1~{\Rightarrow}~#2}
\newcommand
  {\abstr}
  [2]
  {[#1]#2}
\newcommand
  {\funty}
  [3]
  {(#1:#2) \rightarrow #3}
\newcommand
  {\lam}
  [2]
  {\lambda #1.#2}
\newcommand{\inferarrow}{\Rightarrow}
\newcommand{\checkarrow}{\Leftarrow}
\newcommand
  {\tinfer}
  [4]
  {#1 \vdash #2 \inferarrow #3 \rightsquigarrow #4}
\newcommand
  {\tcheck}
  [4]
  {#1 \vdash #2 \checkarrow #3 \rightsquigarrow #4}
\newcommand{\typ}{\ast}
\newcommand{\targ}{t_{\mathit{arg}}}
\newcommand{\tret}{t_{\mathit{ret}}}
\newcommand{\normeq}{\overset{\ast}{=}}
\renewcommand{\appendix}[1]{\section{Appendix: #1}}
\newcommand{\typingrule}[4]{
  #1
  #2
  #3
  #4
}
\newcommand{\todo}{\textbf{TODO:}}

\title{A New Implementation Technique For Dependently-Typed Languages}
\acmConference
  [IFL2026]
  {Symposium on Implementation and Application of Functional Languages}
  {28 -- 30 October, 2026}
  {Gothenburg, Sweden}
\author{Alexander Vandenbroucke}
\orcid{0000-0002-5683-1570}
\affiliation{
  \institution{Unaffiliated}
  \city{London}
  \country{United Kingdom}}

\email{alexander.vandenbroucke@gmail.com}

\begin{abstract}
\todo
\end{abstract}

\begin{document}

\maketitle

\ignoreCode{

\begin{code}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# OPTIONS_GHC -Wincomplete-patterns #-}

module LambdaPiCombinators where

import Text.Show (showParen)
import GHC.TypeLits (Nat, type (+))
import Text.ParserCombinators.ReadP
import Data.Char (isAlpha, isAlphaNum)
import Control.Exception (try, displayException)

\end{code}

}

Once upon a time, I was reading ``A tutorial implementation of a dependently
typed lambda-calculus''~\citep{DBLP:journals/fuin/LohMS10}.
It contains both a formal specification of a simple dependently typed
lambda-calculus and a Haskell implementation of the abstract syntax, evaluation
and type checking. However, in my opinion, the elegance of the core calculus
is spoiled somewhat by the locally-
nameless~\citep{DBLP:journals/jar/Chargueraud12} style of the implementation.
The locally-nameless style uses names (i.e., strings) to represent free
variables and De-Bruijn indices for locally bound terms.
While this has certain proof-engineering advantages, for implementing a simple
calculus, locally nameless representation combines the weaknesses of named and
nameless (De-Bruijn) representation:

\begin{enumerate}
\item
  Evaluation is also needed for type reduction during type checking, but
  evaluation with De-Bruijn indices is inefficient.

\item
  De-Bruijn indices are nevertheless used because they are alledgedly simple,
  but I find substitution with De-Bruijn indices is fiddly and annoying to
  implement.

\item
  Verifying type equivalence during type checking requires re-quoting a
  nameless term into a named representation anyway.
\end{enumerate}

The idea of this article is that we can avoid this unpleasantness by using
Turner's~\citep{DBLP:journals/spe/Turner79} combinator implementation technique
instead. This technique consists of two parts that are simple to understand
and implement: a set of basic combinators and reduction rules, and an
abstraction algorithm which eliminates variables from a lambda-calculus term by
translating it into those combinators.
The abstraction algorithm for a dependently-typed lambda term is only a modest
generalisation from the untyped lambda calculus---though it is novel to the
best of our knowledge.

Because the key idea of this technique is to eliminate variables (and
substitution) altogether, it makes implementing a dependently typed calculus
much more straightforward.

The remainder of this article is laid out as follows:
\begin{itemize}
\item
  We recall the syntax for both the simple dependently typed calculus
  introduced by the previous tutorial. Introduce the following set of
  combinators that we will use throughout the article: |S|, |K|, |I|, |B|, |C|,
  |P|, |S'|, |B'| and |C'| (Section~\ref{sec:syntax}).
  We also recall the reduction rules for these combinators
  (Section~\ref{sec:reduction}).

\item
  We present the bracket abstraction algorithm, extended with a rule to
  abstract function types (Section~\ref{sec:bracket-abstraction}).

\item
  We introduce a bi-directional type system bearing a strong resemblance
  to the system introduced by the original tutorial.
  The key innovation is that our typing relations simultaneously perform an
  elaboration of the term that is being typed into a combinator expression.
  This means that whenever we needed to reduce a term in the original typing
  relation (necessitating re-quoting the term), we can now reduce the
  elaborated combinator expression instead.
  (Section~\ref{sec:typing})

\item
  Section~\ref{sec:examples} gives some examples of typing and executing
  the new calculus.
  Section~\ref{sec:related-work}) discusses related work and
  Section~\ref{sec:conclusion} concludes.
\end{itemize}

Despite our best efforts, two places remain where we need to substitute into
a type: when typing the body of a dependent function (Pi) type or of an
anonymous function (Lambda). But since types are combinator expressions,
substitution is simply function application.


\section{Syntax}
%% ----------------------------------------------------------------------------
\label{sec:syntax}

To begin, let us define the (abstract) syntax of the calculus and the
combinator. Since this is a dependently typed calculus, there is no syntactic
distinction between types and terms: both are captured by the |Term| GADT.
However, there is a separation between terms whose type can be inferred, and
whose type can only be checked. For this reason, |Term| is indexed by a |Mode|.
In all other respects the syntax should be entirely unsurprising.

\begin{code}
data Mode = Infer | Check

data Term (mode :: Mode) where
  Var :: String -> Term Infer
  -- ^ Variable, x
  Ann :: Term Check -> Term Check -> Term Infer
  -- ^ Type annotation, t : t
  App :: Term Infer -> Term Check -> Term Infer
  -- ^ Application, t t
  Typ :: Term Infer
  -- ^ Type of Types, *
  Fun :: String -> Term Check -> Term Check -> Term Infer
  -- ^ Function Type,  (x:t) -> t

  Lam :: String -> Term Check -> Term Check
  -- ^ Lambda, \x.t
  Inf :: Term Infer -> Term Check
  -- ^ Embed Inferrable Term, t
\end{code}

The combinator syntax contains standard |S|, |K|, |I|, |B| and |C| combinators;
as well as |P| for (dependent) function types ($\Pi$-types); |T| for the type
of types; |V| for variables, and lastly an infix application constructor |:@:|.
The |S'|, |B'| and |C'| combinators and the ``constant'' application
constructors |:<@:|, |:@>:| and |:<@>:| are used for the more efficient bracket
abstraction algorithm, described by
Turner~\citep{DBLP:journals/jsyml/Turner79}. They can be ignored on a first
reading.

\begin{code}
data Combinator where
  S :: Combinator
  K :: Combinator
  I :: Combinator
  B :: Combinator
  C :: Combinator
  P :: Combinator            -- ^ Pi-type
  T :: Combinator            -- ^ Type
  V :: String -> Combinator  -- ^ Variable
  (:@:) :: Combinator -> Combinator -> Combinator
  -- ^ Application

  S' :: Combinator
  B' :: Combinator
  C' :: Combinator
  (:<@: ) :: Combinator -> Combinator -> Combinator
  ( :@>:) :: Combinator -> Combinator -> Combinator
  (:<@>:) :: Combinator -> Combinator -> Combinator
  deriving Eq

infixl :@:
\end{code}

For reduction, these extra application constructors are irrelevant. It is thus
useful to "normalise" them away at the top-level of a combinator expression:

\begin{code}
wnf :: Combinator -> Combinator
wnf (a :<@:  b) = a :@: b
wnf (a  :@>: b) = a :@: b
wnf (a :<@>: b) = a :@: b
wnf a = a

pattern a :*: b <- (wnf -> a :@: b)
\end{code}

Here |:*:| is a pattern synonym for "any application constructor", think of
the |*| as a wildcard for any combination of |<|, |>| and |@|.

The extra application constructors are also irrelevant when comparing two
combinator expressions, so we define an equality operator which ignores this
difference:

\begin{code}
(=*=) :: Combinator -> Combinator -> Bool
a =*= b | a == b = True
(a :*: b) =*= (c :*: d) = a =*= c && b =*= d
_ =*= _ = False
infix 4 =*=
\end{code}

\section{Combinator Reduction}
%% ----------------------------------------------------------------------------
\label{sec:reduction}

Combinators have the usual reduction rules. The |reduce| function (written
in formulae as $\creduce{}{}$) performs a single step of reduction if possible.
The first 5 clauses implement standard reduction rules for |S|, |I|, |K|, |B|,
|C|:

\begin{code}
reduce :: Combinator -> Maybe Combinator
reduce = \case
  S :*: f :*: g :*: x -> Just (f :@: x :@: (g :@: x))
  I :*: x             -> Just x
  K :*: x :*: y       -> Just x
  B :*: f :*: g :*: x -> Just (f :@: (g :@: x))
  C :*: f :*: g :*: x -> Just (f :@: x :@: g)
\end{code}

The next three clauses implement the following reduction rules for |S'|, |B'|
and |C'|:

\begin{align*}
\creduce{S'~k~f~g~x}{&k~(f~x)~(g~x)}
\\
\creduce{B'~k~f~g~x}{&k~f~(g~x)}
\\
\creduce{C'~k~f~g~x}{&k~(f~x)~g}
\end{align*}

Again, feel free to ignore these on a first reading.

\begin{code}
  S' :*: k :*: f :*: g :*: x->Just (k :@: (f :@: x) :@: (g :@: x))
  B' :*: k :*: f :*: g :*: x->Just (k :@: f :@: (g :@: x))
  C' :*: k :*: f :*: g :*: x->Just (k :@: (f :@: x) :@: g)
\end{code}

Finally, if none of the previous cases match, we recurse down the left
argument until we find the left-most expression that can be reduced. If
reduction is not possible there, we try the right argument.

\begin{code}
  f :*: g | Just f' <- reduce f -> Just (f' :@: g)
          | Just g' <- reduce g -> Just (f  :@: g')
  _                             -> Nothing
\end{code}

This implies, for instance, that in |P x y|, |x| and |y| can be reduced.

\todo~what is the implication for normal order reduction? Note that rules
similar to this are already required for numerical operations (|plus|) and
|U|.

The extension of $\creduce{}{}$ to multiple steps, denoted $\creduced{}{}$, is
implemented by |reduce'|:

\begin{code}
reduce' :: Combinator -> Combinator
reduce' c = maybe c reduce' (reduce c)
\end{code}

\section{Bracket Abstraction}
%% ----------------------------------------------------------------------------
\label{sec:bracket-abstraction}

The bracket abstraction algorithm is also standard, except that dependent
function types (|Fun|) are abstracted by the following rule (using [x]E to
denote abstracting E with respect to x):

\begin{equation*}
\abstr{x}{(\funty{y}{E_1}{E_2})} = P~\abstr{x}{E_1}~\abstr{x}{(\abstr{y}{E_2})}
\end{equation*}

That is, the both argument and result type are abstracted over

For convenience, abstraction is defined in a type-class. This allows ad-hoc
polymorphism in the |abstract| function, because we need to be able to abstract
both terms and combinators expressions.

\begin{code}
class Abstraction e where
  abstract :: String -> e -> Combinator

instance Abstraction (Term m) where
  abstract x Typ           = K @@ T
  abstract x (App e1 e2)   = S @@ abstract x e1
                               @@ abstract x e2
  abstract x (Lam y e)     = abstract x (abstract y e)
  abstract x (Ann e _)     = abstract x e
  abstract x (Inf e)       = abstract x e
  abstract x (Fun y e1 e2) =
    P @@ abstract x e1 @@ abstract x (abstract y e2)
  abstract x (Var x') | x == x' = I
                      | otherwise = K @@ V x'

instance Abstraction Combinator where
  abstract x (V x') | x == x' = I
  abstract x (e1 :*: e2)      = S @@ abstract x e1
                                  @@ abstract x e2
  abstract x c                = K @@ c
\end{code}

The |@@| operator is a smart constructor for application. It implements a more
efficient abstraction. On a first reading, the reader may pretend that
|@@| is simply |:@:|. Like |:@:| it binds most tightly to the left.

The first four cases of |@@| replace degenerate applications of |S| with
applications of |K|, |B| and |C|. Degenerate means that the variable being
abstracted does not occur in one or both of the sub-expressions.

The next four cases replace applications of |S|, |B| and |C| with the special
combinators |S'|, |B'| and |C'|. This eliminates the blow-up that might occur
after repeated abstraction with a series of variables---this happens if you
abstract a sequence of nested lambdas.

The final four cases define the special application operator |@@| tracking
which operands are composed entirely of constants.
The < or > points to the arguments that are constant.

\begin{code}
(@@) :: Combinator -> Combinator -> Combinator
(S :*: (K :*: a)) @@ (K :*: b) = K @@ (a @@ b)
(S :*: (K :*: a)) @@ I         = a
(S :*: (K :*: a)) @@ b         = B @@ a @@ b
(S :*: a)         @@ (K :*: b) = C @@ a @@ b

(S :*: ((B :<@>: k) :*: a)) @@ b = S' @@ k @@ a @@ b
(B :*: (k :<@: a))          @@ b = B' @@ k @@ a @@ b
(B :*: (k :<@>: a))         @@ b = B' @@ k @@ a @@ b
(C :*: ((B :<@>: k) :*: a)) @@ b = C' @@ k @@ a @@ b

a @@ b | constant a, constant b = a :<@>: b
       | constant a             = a :<@:  b
       | constant b             = a  :@>: b
       | otherwise              = a  :@:  b
       where
         constant (V _)       = False
         constant (_  :@>: _) = False
         constant (_ :<@:  _) = False
         constant (_  :@:  _) = False
         constant _ = True

infixl @@
\end{code}

\section{Typing}
%% ----------------------------------------------------------------------------
\label{sec:typing}

We now turn to implementing a bi-directional dependently typed calculus.
Declaratively, the rules are not essentially different from the Lambda-Pi
calculus, except that we also elaborate the terms into combinator expressions
while type-checking. Thus, type inference results in two combinator
expressions: the type (|Typ|) and an elaboration (|Elaboration|), essentially
capturing the static and dynamic semantics of a term.
The type must be irreducible, and follows from the Lambda-Pi bi-directional
type system.
The elaboration follows bracket abstraction (more or less) and may admit
additional reduction.

\begin{code}
type Typ         = Combinator -- irreducible
type Elaboration = Combinator
data Inferred    = Typ :~> Elaboration deriving Show
\end{code}

As a preliminary, we define simple environments:

\begin{code}
type Env = [(String,Typ)]
\end{code}

Given variable $x$ and type $t$, extending an environment $E$ results in a new
environment $x:t',E$ where $t'$ is the result of substituting all variables
currently in $E$ into $t$.
Therefore $t'$ should not have any free variables.

\begin{code}
extend :: String -> Combinator -> Env -> Env
extend x c env = (x,t') : env
  where
    t' = reduce' (foldr (\(y,c) -> (@@ c) . abstract y) c env)
\end{code}


\subsection{Type Inference}
%% ========================

In the following, $\tinfer{\Gamma}{e}{t}{e'}$ will
denote that a type $t$ is inferred for term $e$ under environment $\Gamma$ and
elaborates to $e'$ and $\tcheck{\Gamma}{e}{t}{e'}$ means that $e$ has type $t$
under environment $G$ and elaborates to $e'$.
The arrows $\inferarrow$ and $\checkarrow$ are meant to suggest that
information flows from the term to the type and vice versa.
As before, abstraction of $e$ with respect to variable $x$ is written as
$\abstr{x}{e}$, and $\creduced{e}{e'}$ means that the expression $e$ reduces to
$e'$, where $e'$ is irreducible.

\paragraph{Variable}
A variable's type is inferred by looking it up in the environment.

\[
\inferrule
  {x:T \in \Gamma}
  {\tinfer{\Gamma}{x}{T}{x}}
\]

\begin{code}
infer :: Env -> Term Infer -> Either String Inferred
infer env (Var x) = case lookup x env of
  Nothing -> Left  $ "unbound variable: " <> x
  Just t  -> Right $ t :~> V x
\end{code}

\paragraph{Annotation}
For a type annotation, we must first check that the expression on the
right-hand side of the annotation is indeed a type, i.e., has type |Typ|. As a
by-product of type checking, we also get the elaboration.
This is a combinator expression, which we must reduce further to obtain a type.
Finally, we check that the expression on the right-hand side of the annotation
indeed has this type.

\[
\inferrule
  {
    \tcheck{\Gamma}{r}{T}{r'}\\
    \creduced{r'}{t}\\
    \tcheck{\Gamma}{e}{t}{c}
  }
  {
    \tinfer{\Gamma}{e:r}{t}{c}
  }
\]

\begin{code}
infer env (Ann e r) = do
  r' <- check env r T
  let t = reduce' r'
  c <- check env e t
  Right $ t :~> c
\end{code}

\paragraph{Type}
Inferring the type of |Typ| is entirely trivial. It is |Typ|. (A bit
controversial perhaps.)

\[
  \inferrule{ }{\tinfer{\Gamma}{\typ}{\typ}{T}}
\]

\begin{code}
infer _ Typ = Right $ T :~> T
\end{code}

\paragraph{Application}
Inferring the type of an application starts by inferring the type of the left-
hand expression. This must be a function type ($P$-combinator). Next, we check
that the argument (the right-hand expression) has the expected argument type.
As a by-product, we now have the elaboration of the argument available, which
we apply to the function type's body to calculate the return type.

\[
\inferrule
  {
    \tinfer{\Gamma}{e_1}{t_1}{c_1}\\
    t1 = P~t_2~f\\
    \tcheck{\Gamma}{e_2}{t_2}{c_2}\\
    \creduced{f~c_2}{t}
  }
  {\tinfer{\Gamma}{e1~e2}{t}{c_1~c_2}}
\]

\begin{code}
infer env (App e1 e2) = do
  t1 :~> c1 <- infer env e1
  case t1 of
    P :*: t2 :*: f -> do
      c2 <- check env e2 t2
      let t = reduce' (f @@ c2)
      Right $ t :~> (c1 @@ c2)
    _ -> Left $
      "Could not match expected type " <>
      show (Fun "x" (Inf (Var "A")) (Inf (Var "B"))) <>
      " with actual type " <>
      show t1
\end{code}

\paragraph{Function Type}
Lastly, to infer the type of a function type, we check that the argument
type is in fact a type. The elaboration of the argument type is a combinator
expression, which we reduce as far as possible. Then we check that the return
type is a type, under an environment extended with the argument variable.
The elaboration of the function is a P combinator applied to the (reduced)
argument type and the return type (abstracted over the argument variable).

\[
\inferrule
  {
    \tcheck{\Gamma}{t_1}{\typ}{c_1}\\
    \creduced{c_1}{c_1'}\\
    \tcheck{x:c_1',\Gamma}{t_2}{\typ}{c_2}\\
    \creduced{c_2}{c_2'}
  }
  {\tinfer{\Gamma}{\funty{x}{t_1}{t_2}}{\typ}{P~c_1'~\abstr{x}{c_2'}}}
\]

\begin{code}
infer env (Fun x t1 t2) = do
  c1 <- check env t1 T
  let c1' = reduce' c1
  c2 <- check (extend x c1' env) t2 T
  let c2' = reduce' c2
  -- ^ The elaboration can be reducible, so probably not needed
  Right $ T :~> (P @@ c1' @@ abstract x c2')
\end{code}


\subsection{Type Checking}
%% =======================

We can check all inferrable terms simply by inferring their type, and then
verifying that the inferred and the expected combinator expressions are the
same.

\[
\inferrule
  {
   \tinfer{\Gamma}{e}{t'}{c}\\
   t \normeq t'
  }
  {\tcheck{\Gamma}{e}{t}{c}}
\]

\begin{code}
check :: Env -> Term Check -> Typ -> Either String Elaboration
check env (Inf e) t = do
  t' :~> e' <- infer env e
  if t =*= t' then
    Right e'
  else
    Left $
      "Type mismatch: Could not match expected type "
      <> show t <> " with inferred type " <> show t'
\end{code}

\paragraph{Lambda}
A lambda term can only be checked successfully against a function type. The
procedure is to check the body against the calculated return type, in an
environment extended with the bound variable. This return type is calculated by
applying the body of the function type to the same type with which we extended
the environment. In this type all variables that are inside the environment
will have been instantiated.

\[
\inferrule
  {
    x:x_t,\Gamma = \mathit{extend}~x~t_1~\Gamma\\
    \creduced{f~x_t}{t_2}\\
    \tcheck{x:x_t,\Gamma}{e}{t_2}{c}
  }
  {\tcheck{\Gamma}{\lam{x}{e}}{P~t_1~f}{\abstr{x}{c}}}
\]

\begin{code}
check env (Lam x e) t = do
  case t of
    P :*: t1 :*: f -> do
      let (_,xt):_ = extend x t1 env
          t2 = reduce' (f @@ xt)
      abstract x <$> check ((x,xt):env) e t2
      -- should we substitute into the body here?
      -- does lambda-pi have the same flaw?
    _ ->
      Left $
        "Could not match type " <> show t <>
        " while checking a lambda abstraction."
\end{code}




\section{Examples}
%% ----------------------------------------------------------------------------
\label{sec:examples}

The remaining code in this article implements pretty printing, parsing and a
small REPL, that, while useful, are not particularily interesting.
However, the REPL will serve as a vehicle for some small examples.

Typing an (inferrable) term at the REPL causes it to parse, type and then
reduce that term, for example:

\begin{repl}
  > *
  T -> T
   : T
\end{repl}

This means that the string |"*"| is elaborated into the term $T$.
The |=> T| means that this elaboration reduces to $T$, and |: T| means that it
has type $T$.
Let us look at an example that uses more than one combinator next:

\begin{repl}
  > (\x.x) : (x:*) -> *
  I => I
   : P T (K T)
\end{repl}

The term $\lam{x}{x} : \funty{x}{\typ}{\typ}$ elaborates to $I$, which is
irreducible and it has type $P~T~(K~T)$, that is, a function ($P$) accepting
some argument $x$ of type $T$ (i.e., $x$ is a type) and returning a value
of type $\creduce{K~T~x}{T}$ (also a type).
Contrast with the following:

\begin{repl}
  > (\f.f *) : (f:(x:*) -> *) -> *
  C I T => C I T
   : P (P T (K T)) (K T)
\end{repl}

Here the expression takes a function $f : \funty{x}{\typ}{\typ}$ as argument,
and applies it to $\typ$. The type $P~(P~T~(K~T))~(K~T)$ is a function, taking
a function $f$ (see above) as an argument and returning $\creduce{K~T~f}{T}$.

So far, all combinator expressions have been irreducible. Let's change that by
applying (|\f.f *|) to the identity function:

\begin{repl}
  > ((\f.f *) : (f:(x:*) -> *) -> *) (\x.x)
  C I T I => T
   : T
\end{repl}

The expression now elaborates to
$\creduce{C~I~T~I}{\creduce{I~I~T}{\creduce{I~T}{T}}}$. The overall expression
has type $T$ as expected. Finally, we are not restricted to just types ($\typ$)
as arguments. Here is an identity function that is polymorphic in the
type $A$:

\begin{repl}
  > (\A.\x.x) : (A:*) -> (x:A) -> A
  K I => K I
   : P T (S P K)
\end{repl}

Applying the return type to some type $A$, we get
$\creduce{S~P~K~A}{P~A~(K~A)}$, that is, a function where we expect an
argument, say $x$, of type $A$, and then the return type is
$\creduce{K~A~x}{A}$.

We can also introduce a higher-order type $T$, which we can then apply to a
matching type:

\begin{repl}
  > (A : (B : *) -> *) -> A *
  P (P T (K T)) (C I T) => P (P T (K T)) (C I T)
   : T
\end{repl}

The produced expression certainly looks impressive. We cannot just pass any old
type to $A$:

\begin{repl}
  > (C : (B : *) -> *) -> (A : (B : *) -> *) -> A C
  Type mismatch: Could not match expected type T with
  inferred type P T (K T)
\end{repl}

Where do we go from here? More language features? Comparison? Acknowledge that
Lambda-Pi is still pretty neat. Can we do implicits?

\section{Related Work}
%% ----------------------------------------------------------------------------
\label{sec:related-work}

\section{Conclusion}
%% ----------------------------------------------------------------------------
\label{sec:conclusion}

\appendix{Pretty Printing}
%% ----------------------------------------------------------------------------

The built-in Show class is good enough to insert the right parentheses when
appropriate:

\begin{code}
instance Show (Term m) where
  showsPrec d = \case
    Var x -> str x
    Typ   -> str "*"
    Inf e -> showsPrec d e
    Ann e t -> showParen (d > ann_d) $
      showsPrec (ann_d + 1) e . str " : " . showsPrec fun_d t
    App e1 e2 -> showParen (d > app_d) $
      showsPrec (app_d + 1) e1
      . str " "
      . showsPrec (app_d + 1) e2
    Lam x e -> showParen (d > lam_d) $
      str "\\" . str x . str "." . showsPrec lam_d e
    Fun x t1 t2 -> showParen (d > fun_d) $
      str "(" . str x . str  ":" . showsPrec (fun_d + 1) t1
      . str ") -> "
      . showsPrec fun_d t2
    where
      str x r = x ++ r
      lam_d = 1 :: Int
      fun_d = 2 :: Int
      ann_d = 3 :: Int
      app_d = 4 :: Int

instance Show Combinator where
  showsPrec d = \case
    S -> str "S"
    K -> str "K"
    I -> str "I"
    B -> str "B"
    C -> str "C"
    P -> str "P"
    T -> str "T"
    V x -> (x ++)
    c1  :@:  c2 -> app c1 c2
    c1 :<@:  c2 -> app c1 c2
    c1  :@>: c2 -> app c1 c2
    c1 :<@>: c2 -> app c1 c2
    S' -> str "S'"
    B' -> str "B'"
    C' -> str "C'"
    where
      app c1 c2 = showParen (d > 1) $
        showsPrec 1 c1 . (" " ++) . showsPrec 2 c2
      str x r = x ++ r
\end{code}


\appendix{Parsing}
%% -----------------------------------------------------------------------------

The parser recognises the following grammar:

\begin{spec}
Expr := \V -> Abs | App
Type := (x:Expr) -> Typ | Ann
Ann  := App : Type | App
App  := App Atom | Atom
Atom := var | * | (Expr)
\end{spec}

The approach followed here was inspired by "Design Patterns for Parser
Combinators (Functional Pearl)".

\begin{code}
data Expr  = ELam String Expr       | OfType EType deriving Show
data EType = EFun String Expr EType | OfAnn  EAnn  deriving Show
data EAnn  = EAnn EApp EType        | OfApp  EApp  deriving Show
data EApp  = EApp EApp EAtom        | OfAtom EAtom deriving Show
data EAtom = EVar String | ETyp | EPar Expr        deriving Show

expr :: ReadP Expr
expr = (<++ (OfType <$> etype)) $ do
  symbol "\\"
  x <- variable
  symbol "."
  e <- expr
  pure $ ELam x e

eann :: ReadP EAnn
eann = do
  e <- eapp
  ((EAnn e <$ symbol ":" <*> etype) <++ pure (OfApp e))

etype :: ReadP EType
etype = (<++ (OfAnn <$> eann)) $ do
  symbol "("
  x <- variable
  symbol ":"
  e1 <- expr
  symbol ")"
  symbol "->"
  e2 <- etype
  pure (EFun x e1 e2)

eapp :: ReadP EApp
eapp = infixl1 OfAtom eatom (pure EApp)

eatom :: ReadP EAtom
eatom =
      (ETyp <$  symbol "*")
  <++ (EVar <$> variable)
  <++ (EPar <$> (symbol "(" *> expr <* symbol ")"))


lexeme :: ReadP a -> ReadP a
lexeme p = p <* skipSpaces

symbol :: String -> ReadP String
symbol = lexeme . string

variable :: ReadP String
variable =
  lexeme $
    (:) <$> satisfy (liftA2 (||) isAlpha (=='_'))
        <*> munch isAlphaNum

infixl1 :: (a -> b) -> ReadP a -> ReadP (b -> a -> b) -> ReadP b
infixl1 wrap p op = (wrap <$> p) <**> rest
  where
    rest = (flip (.) <$> (flip <$> op <*> p) <*> rest) <++ pure id
    fx <**> ff = do
      x <- fx
      f <- ff
      pure (f x)

class ToTerm e where
  toTerm :: e -> Maybe (Term Check)

instance ToTerm Expr where
  toTerm (ELam x e) = Lam x <$> toTerm e
  toTerm (OfType e)  = toTerm e

instance ToTerm EAnn where
  toTerm (EAnn e t) = Inf <$> (Ann <$> toTerm e <*> toTerm t)
  toTerm (OfApp t) = toTerm t

instance ToTerm EType where
  toTerm (EFun x t1 t2) = Inf <$> (Fun x <$> toTerm t1 <*> toTerm t2)
  toTerm (OfAnn e)      = toTerm e

instance ToTerm EApp where
  toTerm (EApp e a) = do
    Inf t <- toTerm e
    Inf . App t <$> toTerm a
  toTerm (OfAtom a) = toTerm a

instance ToTerm EAtom where
  toTerm (EVar x) = Just (Inf (Var x))
  toTerm ETyp     = Just (Inf Typ)
  toTerm (EPar e) = toTerm e

parse :: String -> Either String (Term Check)
parse = result . readP_to_S (skipSpaces *> expr <* eof) where
  result [(e,"")] | Just t <- toTerm e = Right t
  result _                             = Left "Syntax error!"
\end{code}


\appendix{Simple REPL}
%% ----------------------------------------------------------------------------

\begin{code}
main :: IO ()
main =
  let
    eval str = either id id $ do
      t <- parse str
      case t of
        Lam{} -> Left "The top-level term must be inferrable!"
        Inf t -> do
          (t :~> c) <- infer [] t
          Right $
            show c <> " => " <> show (reduce' c)
            <> "\n : " <> show t
    go = do
      putStr "> "
      getLine >>= \str -> do
        case str of
          ":h" -> do
            putStrLn $ "Usage: <expression> | :l <file> | :h | :q"
            go
          ":q" -> pure ()
          (words -> [":l", file]) -> do
            try (readFile file) >>=
               putStrLn . either (displayException @IOError) eval
            go
          _ -> do
            putStrLn $ eval str
            go
  in go
\end{code}

\bibliographystyle{plain}
\bibliography{LambdaPiCombinators}

\end{document}
