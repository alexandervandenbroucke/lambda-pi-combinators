\documentclass[format=sigconf, screen=true, review=false]{acmart}

\usepackage{fancyvrb}    %% Source Code listings
\usepackage{mathpartir}  %% Type Inference Rules
\usepackage{mathtools}   %% \xRightarrow

\DefineVerbatimEnvironment{code}{Verbatim}{fontsize=\small}
\DefineVerbatimEnvironment{spec}{Verbatim}{fontsize=\small}
\DefineVerbatimEnvironment{repl}{Verbatim}{fontsize=\small}
\DefineShortVerb{\|}

\newcommand{\ignoreCode}[1]{}
\newcommand
  {\creduce}
  [2]
  {#1 \Rightarrow #2}
\newcommand
  {\creduced}
  [2]
  {#1~\xRightarrow{*}~#2}
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

\title{An New Implementation Technique For The Dependently-Typed Lambda
  Lambda Calculus}
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
Can you implement a dependently-typed lambda calculus using Turner's logical
combinator technique? Yes. The reason this is interesting is that type checking
a dependently-typed language inherently mixes type-checking with execution,
because your types can be terms (and terms can be types), and hence have
operational meaning. The solution presented here elaborates terms (or
types, whichever) into combinator expressions on-the-fly during type checking.
Only one extra combinator, T, is required in addition to Turner's 9 original
combinators, S, K, I, P, B, C, S', B' and C' to implement a simple
bi-directional type system (only the first four combinators are essential).
\end{abstract}

\keywords{combinators, dependent types, lambda calculus, type checking, type
inference, bracket abstraction}

\begin{CCSXML}
<ccs2012>
   <concept>
       <concept_id>10011007.10011006.10011041</concept_id>
       <concept_desc>Software and its engineering~Compilers</concept_desc>
       <concept_significance>500</concept_significance>
       </concept>
   <concept>
       <concept_id>10011007.10011006.10011039.10011311</concept_id>
       <concept_desc>Software and its engineering~Semantics</concept_desc>
       <concept_significance>500</concept_significance>
       </concept>
 </ccs2012>
\end{CCSXML}

\ccsdesc[500]{Software and its engineering~Compilers}
\ccsdesc[500]{Software and its engineering~Semantics}

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
{-# LANGUAGE DeriveLift      #-}
{-# LANGUAGE TemplateHaskell #-}

{-# OPTIONS_GHC -Wincomplete-patterns #-}

module LambdaPiCombinators where

import Text.Show (showParen)
import GHC.TypeLits (Nat, type (+))
import Text.ParserCombinators.ReadP
import Data.Char (isAlpha, isAlphaNum)
import Control.Exception (try, displayException)
import Language.Haskell.TH.Syntax (Lift, Exp, Q)
import Language.Haskell.TH.Quote (QuasiQuoter(..))
\end{code}

}

Can you implement a dependently-typed lambda calculus using Turner's logical
combinator technique? Yes. Here's an example of a polymorphic identity
function:

\begin{align*}
(\lam{\alpha}{\lam{x}{x}}) : \funty{\alpha}{\typ}{\funty{x}{\alpha}{\alpha}}
\end{align*}

And here is the combinator it is implemented by: |I|. This combinator
implements the identity function directly. More interestingly, the type of the
function, $\funty{\alpha}{\typ}{\funty{x}{\alpha}{\alpha}}$ elaborates to
|P T (S P K)|.
The |P| combinator constructs a function type, in other words, a \textbf{P}i
type. Rather than the usual infix-arrow syntax $\funty{x}{\typ}{\cdots}$, |P|
is a prefix operator. We can thus read |P T (S P K)| as the type of a function
expecting an argument $\alpha$ of type |T| (the type of types) and returning a
value of type $\texttt{S P K}~\alpha$ (note the dependency on the argument
$\alpha$).
This reduces as follows:
$\creduce{\texttt{S P K}~\alpha}{\texttt{P }\alpha~(\texttt{K }\alpha)}$.
This is another function type, this time expecting an argument $x$ of type
$\alpha$, and producing a value of type $\texttt{K }\alpha x$. This finally
reduces to $\alpha$: $\creduce{\texttt{K}~\alpha~x}{\alpha}$, as expected of
the identity function.

It should be obvious from the previous paragraph that a dependently-typed
calculus has just as much interesting execution going on in its types as in
its terms, if not more. This is because there is no (syntactic) distinction
between terms and types: you can have types in your terms and terms in your
types. The implication is that type checking and execution are inherently
interwoven. Therefore, while in the middle of type checking, we need to
generate an executable representation of the types against which terms are
checked.\footnote{We generate combinators both during type checking and
  inference, but only checking is mentioned here for simplicity.}
We choose to use Turner's logical combinators~\cite{DBLP:journals/spe/Turner79}
because they are straightforward to implement, yet admit an easy path to decent
performance via graph reduction. Most importantly, they make substitution
trivial (which is usually tricky to get right) because the key idea of the
combinators technique is to eliminate variables entirely.

Variable elimination is accomplished by the well-known bracket abstraction
algorithm~\cite{DBLP:journals/spe/Turner79,DBLP:journals/jsyml/Turner79}.
The bracket abstraction algorithm for a dependently-typed lambda term that is
presented here is only a modest generalisation from the original untyped
version---though it is novel to the best of our knowledge.

The calculus implemented in this article is based on the language presented in
``A tutorial implementation of a dependently typed
lambda-calculus''~\citep{DBLP:journals/fuin/LohMS10} by L\"{o}h et al. They
set out to prove that dependent types (and their implementation) need not be
scary or hard to understand.
It contains both a formal specification of a simple dependently typed
lambda-calculus and a Haskell implementation of its abstract syntax, evaluation
and type checking. The tutorial is excellent, and I would warmly recommend it
to anyone interested in a core implementation of dependent types.

The remainder of this article is laid out as follows:
\begin{itemize}
\item
  We recall the syntax for both the simple dependently typed calculus
  introduced by the previously mentioned tutorial and then introduce the
  set of combinators needed for the implementation in this article: |S|, |K|,
  |I|, |P|, |T|, |B|, |C|, |S'|, |B'| and |C'| (Section~\ref{sec:syntax}).
  We also recall the reduction rules for these combinators
  (Section~\ref{sec:reduction}).

\item
  Section~\ref{sec:bracket-abstraction} presents the bracket abstraction
  algorithm, extended with a rule to abstract function types, which is
  novel to the best of my knowledge.

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

\item
  Section~\ref{sec:conclusion} concludes and discusses future work.
\end{itemize}

This article is written in literate Haskell and is executable. In addition
to the functionality presented in the main text, the appendices contain code
implementing parsing, pretty printing, a simple REPL and
QuasiQuoters~\cite{ACM/geoffrey07}.

\section{Syntax}
%% ----------------------------------------------------------------------------
\label{sec:syntax}

To begin, let us define the (abstract) syntax of the calculus and the
combinators. Since this is a dependently typed calculus, there is no syntactic
distinction between types and terms: both are captured by the |Term| GADT.
However, there is a separation between terms whose type can be inferred, and
whose type can only be checked. For this reason, |Term| is indexed by a |Mode|.
In all other respects the syntax should be entirely unsurprising.
The constructors are annotated with their surface level syntax (e.g., |*| for
|Typ|, |\x.t| for |Lam x t|, etc.).


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
  -- ^ Function Type, (x:t) -> t

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

%% \todo~what is the implication for normal order reduction? Note that rules
%% similar to this are already required for numerical operations (|plus|) and
%% |U|.

The extension of $\creduce{}{}$ to multiple steps, denoted $\creduced{}{}$, is
implemented by |reduce'|:

\begin{code}
reduce' :: Combinator -> Combinator
reduce' c = maybe c reduce' (reduce c)
\end{code}

\section{Bracket Abstraction}
%% ----------------------------------------------------------------------------
\label{sec:bracket-abstraction}

The bracket abstraction algorithm is also standard, so we will not repeat most
of the rules here, except that dependent
function types $\funty{y}{E_1}{E_2}$ are abstracted by the following rule
(using $\abstr{x}{E}$ to denote abstracting $E$ over $x$):

\begin{align*}
\abstr{x}{(\funty{y}{E_1}{E_2})}
   &= [x](P~E_1~\abstr{y}{E_2}) \\
   &= S~\abstr{x}{(P~E_1)}~\abstr{x}{(\abstr{y}{E_2})} \\
   &= S~(S~(K~P)~\abstr{x}{E_1})~\abstr{x}{(\abstr{y}{E_2})}
\end{align*}

That is, the body of the function type is first abstracted over $y$, and then
the |P| combinator is applied to both $E_1$ and $\abstr{x}{E_2}$.
This presents a slight problem: since $E_1$ is not a combinator expression,
|P| cannot be applied to it directly, so $P~E_1$ is nonsense. This will be
addressed shortly. The entire expression is then abstracted over $x$.

Now, recall the bracket-abstraction rule for application:

\[
\abstr{x}{(E_1~E_2)} = S~\abstr{x}{E_1}~\abstr{x}{E_2}
\]

Applying this rule twice mends the notation.

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
  abstract x (Fun y e1 e2) = S @@ (S @@ (K @@ P)
                                     @@ abstract x e1)
                               @@ abstract x (abstract y e2)
  abstract x (Var x') | x == x' = I
                      | otherwise = K @@ V x'

instance Abstraction Combinator where
  abstract x (V x') | x == x' = I
  abstract x (e1 :*: e2)      = S @@ abstract x e1
                                  @@ abstract x e2
  abstract x c                = K @@ c
\end{code}

The |@@| operator is a smart constructor for application. It implements a more
efficient abstraction. Like |:@:| it binds most tightly to the left.
On a first reading, the reader may pretend that |@@| is simply |:@:|, and
skip the remainder of this section.

The first four cases of |@@| replace degenerate applications of |S| with
applications of |K|, |B| and |C|. Degenerate means that the variable being
abstracted does not occur in one or both of the sub-expressions.

The next four cases replace applications of |S|, |B| and |C| with the special
combinators |S'|, |B'| and |C'|. This eliminates the blow-up that might occur
after repeated abstraction with a series of variables---this happens if you
abstract a sequence of nested lambdas.

The final four clauses define the special application operator |@@| tracking
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

Given variable $x$ and type $t$, extending an environment $\Gamma$ results in
a new environment $x:t_x,\Gamma$ where $t_x$ is the result of substituting all
variables currently in $E$ into $t$.
Therefore $t_x$ should not have any free variables.

\begin{code}
extend :: String -> Combinator -> Env -> Env
extend x c env = (x,t') : env
  where
    t' = reduce' (foldr (\(y,c) -> (@@ c) . abstract y) c env)
\end{code}


\subsection{Type Inference}
%% ========================

In the following, $\tinfer{\Gamma}{e}{t}{c}$ will
denote that a type $t$ is inferred for term $e$ under environment $\Gamma$ and
elaborates to $c$ and $\tcheck{\Gamma}{e}{t}{c}$ means that $e$ has type $t$
under environment $G$ and elaborates to $c$.
The arrows $\inferarrow$ and $\checkarrow$ are meant to suggest that
information flows from the term to the type and vice versa.
As before, abstraction of $e$ with respect to variable $x$ is written as
$\abstr{x}{e}$, and $\creduced{e}{e'}$ means that the expression $e$ reduces to
$e'$, where $e'$ is irreducible.
Each typing rule is given together with the corresponding clause of |infer| or
|check| implementing that rule.

\paragraph{Variable}
A variable's type is inferred by looking it up in the environment.

\[
\inferrule
  {x:t \in \Gamma}
  {\tinfer{\Gamma}{x}{t}{x}}
\]

\begin{code}
infer :: Env -> Term Infer -> Either String Inferred
infer env (Var x) = case lookup x env of
  Nothing -> Left  $ "unbound variable: " <> x
  Just t  -> Right $ t :~> V x
\end{code}

\paragraph{Annotation}
For a type annotation, we must first check that the expression on the
right-hand side of the annotation is indeed a type, i.e., has type $\typ$. As a
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
Inferring the type of $\typ$ is entirely trivial---though perhaps a bit
controversial: it is |T|.

\[
  \inferrule{ }{\tinfer{\Gamma}{\typ}{T}{T}}
\]

\begin{code}
infer _ Typ = Right $ T :~> T
\end{code}

\paragraph{Application}
Inferring the type of an application starts by inferring the type of the left-
hand expression. This must be a function type (|P|-combinator). Next, we check
that the argument (the right-hand expression) has the expected argument type.
As a by-product, we now have the elaboration of the argument available, which
we apply to the function type's body to calculate the return type.

\[
\inferrule
  {
    \tinfer{\Gamma}{e_1}{P~t_2~f}{c_1}\\
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
type is in fact a type. Then we check that the return type is a type, under an
environment extended with the argument variable and the elaboration of the
argument type.
The elaboration of the function is thus the P combinator applied to the
argument type $c_1$ and the return type $c_2$ \emph{abstracted over the
argument variable}. The elaboration is allowed to be reducible, so there is no
need to reduce $c_1$ and $c_2$.

\[
\inferrule
  {
% Reduction of c_1 and c_2 is not needed
    \tcheck{\Gamma}{t_1}{\typ}{c_1}\\
%    \creduced{c_1}{c_1'}\\
%    \tcheck{(\mathit{extend}~x~c_1'~\Gamma)}{t_2}{\typ}{c_2}\\
%    \creduced{c_2}{c_2'}
   \tcheck{(\mathit{extend}~x~c_1~\Gamma)}{t_2}{\typ}{c_2}
  }
  {
%    \tinfer{\Gamma}{\funty{x}{t_1}{t_2}}{\typ}{P~c_1'~\abstr{x}{c_2'}}
    \tinfer{\Gamma}{\funty{x}{t_1}{t_2}}{\typ}{P~c_1~\abstr{x}{c_2}}
  }
\]

\begin{code}
infer env (Fun x t1 t2) = do
  c1 <- check env t1 T
  c2 <- check (extend x c1 env) t2 T
  Right $ T :~> (P @@ c1 @@ abstract x c2)
\end{code}


\subsection{Type Checking}
%% =======================

We can check all inferable terms simply by inferring their type, and then
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
    x:t_x,\Gamma = \mathit{extend}~x~t_1~\Gamma\\
    \creduced{f~t_x}{t_2}\\
    \tcheck{x:t_x,\Gamma}{e}{t_2}{c}
  }
  {\tcheck{\Gamma}{\lam{x}{e}}{P~t_1~f}{\abstr{x}{c}}}
\]

\begin{code}
check env (Lam x e) t = do
  case t of
    P :*: t1 :*: f -> do
      let (_,tx):_ = extend x t1 env
          t2 = reduce' (f @@ tx)
      abstract x <$> check ((x,tx):env) e t2
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
small REPL, that, while useful, are not particularly interesting.
However, the REPL will serve as a vehicle for some small examples.

Typing an (inferable) term at the REPL causes it to parse, type and then
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

Have we really unified terms and types? Let's define a function with a
non-trivial type:

\begin{repl}
  > (\x.x) : (((\t.(x:t) -> t) : (t : *) -> *) *)
  I => I
   : P T (K T)
\end{repl}

We have a function in a type, so yes!

\section{Conclusion}
%% ----------------------------------------------------------------------------
\label{sec:conclusion}

Turner's logical combinator technique is a flexible method for the
implementation of functional programming languages. As a testament to this, we
have shown that only a modest extension is required to adapt it to a
dependently-typed setting.
This setting is particularly interesting, because type checking in this
setting is inherently mixed with evaluation. This has guided us towards an
extension of the existing bi-directional type checking algorithm that
elaborates terms or types into combinators on-the-fly.

\paragraph{Future Work} Future work consists of two lines of research:
First, on the theoretical side, formalising the meta-theory, including a proof
that the type-directed elaboration is correct with respect to the usual
operational semantics is an important direction for future work. Given the
moderate size and unsurprising nature of the type system, we expect standard
proof techniques to be sufficient.

Secondly, practical combinator implementations rely on graph reductions to
obtain good performance. It is an open question how we can wed a graph
reduction engine, an essentially imperative piece of machinery, to the purely
functional implementation of type checking and inference.

%% \todo
%% More language features? Comparison with Lambda-Pi? Acknowledge that
%% Lambda-Pi is still pretty neat. Can we do implicits? Graph-reduction?

%% -----------------------------------------------------------------------------

\bibliographystyle{plain}
\bibliography{LambdaPiCombinators}


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
  toTerm (OfApp t)  = toTerm t

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
        Lam{} -> Left "The top-level term must be inferable!"
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

\appendix{Quasi Quoter}
%% ----------------------------------------------------------------------------

Scaffolding code

\begin{code}
deriving instance Lift (Term Infer)
deriving instance Lift (Term Check)
deriving instance Lift Combinator

qq :: String -> (String -> Q Exp) -> QuasiQuoter
qq name exp =
  QuasiQuoter
  { quoteExp  = exp
  , quotePat  = invalid "pattern"
  , quoteType = invalid "type"
  , quoteDec  = invalid "declaration"
  }
  where
    invalid :: String -> String -> Q a
    invalid ctx _ =
      fail $
        name
        <> "quasi-quoter cannot be used in a "
        <> ctx <> " context!"

\end{code}

Quoting of expressions |lpc| or, inferable expression |lpci|: 
\begin{code}
lpc :: QuasiQuoter
lpc = qq "lpc" $ \str -> case parse str of
  Left  err  -> fail $ "lpc quasi-quoter parse error: " <> err
  Right term -> [|term|]

lpci :: QuasiQuoter
lpci = qq "lpci" $ \str -> case parse str of
  Left  err ->
    fail $ "lpci quasi-quoter parse error: " <> err
  Right Lam{} ->
    fail "lpci quasi-quoter: quoted expression is not inferable"
  Right (Inf term) -> [|term|]
\end{code}

A quoter that any allows expressions of type $\typ$ to be quoted:

\begin{code}
typ :: QuasiQuoter
typ = qq "typ" $ \str -> case parse str of
  Left err -> fail $ "typ quasi-quoter parse error: " <> err
  Right t -> case check [] t T of
    Left err ->
      fail $
        "typ quasi-quoter: quoted expression is not a type: " <> err
    Right c ->
      let r = reduce' c in [|r|]
\end{code}


\end{document}
