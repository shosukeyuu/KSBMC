\section{Semantics}\label{sec:Semantics}

The semantics of $K\Box$ are given with respect to \emph{plausibility models}. A (single-agent) \emph{plausibility model} is a tuple $\M = (M, \leq, V)$, where
\begin{itemize}
  \item $M$ is a set of states or possible worlds;
  \item $\leq$ is a well-preorder, that is a reflexive, transitive, and well-founded relation. Well-foundedness means that for any non-empty subset $P \subseteq M$, the set of minimal-elements
  \[\Min_\leq P := \{s \in P \mid s \leq s' \text{ for all } s' \in P\} \]
  is non-empty. Note that this also implies that $\leq$ is connected;
  \item $V : Prop \to \mathcal{P}(M)$ is a valuation.
\end{itemize}
We call $\leq$ the plausibility relation. Following the convention in \cite{baltagQualitativeTheoryDynamic2008}, we interpret $s \leq t$ as the state $s$ as being more or equally as plausible as $t$. 

For each plausibility relation, there is a corresponding epistemic indistinguishability relation $\sim$, defined as the union between $\leq$ and it's converse $\geq$. That is, ${\sim} := {\leq} \cup {\geq}$. In the single-agent case, this reduces to the universal relation $s \sim t $ iff $s,t \in M$. 
\hide{
\begin{code}
module Semantics where

import Syntax

import Data.List ( nub )
import Data.IntMap (IntMap, (!), delete, restrictKeys, fromList) 
import qualified Data.IntSet as Data.Intset
import Prelude hiding (pred)
\end{code}
}
\begin{code}
type World = Int
type Universe = [World]
type Proposition = Int

type Valuation = IntMap [Proposition]
type Relation = [(World,World)]

data PlausibilityModel = PlM {worlds :: Universe, rel :: Relation, val :: Valuation}
  deriving (Eq,Ord,Show)
\end{code}
To make the representation of the plausibility models more compact, the following functions construct the reflexive-transitive closure of a relation:
\begin{code}
rClosure :: PlausibilityModel -> PlausibilityModel
rClosure m = PlM (worlds m) closure (val m) where
  closure = rel m ++ [(a,a) | a <- worlds m, (a,a) `notElem` rel m]

tClosure :: Relation -> Relation
tClosure r 
  | r == closureStep = r
  | otherwise                = tClosure closureStep 
  where
    closureStep = nub $ r ++ [(a,c) | (a,b) <- r, (b',c) <- r, b == b']

rtClosure :: PlausibilityModel -> PlausibilityModel
rtClosure m = rClosure $ PlM (worlds m) (tClosure (rel m)) (val m)
\end{code}

The semantic clauses of $K\Box$ are defined recursively as follows, where $\M$ is a plausibility model and $s \in M$ is a state:
\[
\begin{array}{l c l}
\M, s \vDash p & \text{iff} & s \in V(p) \ ;\\
\M, s \vDash \neg \phi & \text{iff} & \M,s \not\vDash \phi \ ; \\
\M, s \vDash \phi \wedge \psi & \text{iff} & \M,s \vDash \phi \text{ and } \M,s \vDash \psi \ ; \\
\M, s \vDash \Box \phi & \text{iff} & \M,t \vDash \phi \text{ for all } t \leq s \ ; \\
\M, s \vDash K \phi & \text{iff} & \M,t \vDash \phi \text{ for all } s \sim t \ . \\
\end{array}
\]
Note that $\Box$ is the Kripke modality of the converse plausibility relation $\geq$, due to our convention. We write $\| \phi \|_\M$ to denote the set $\{s \in M \mid \M,s \vDash \phi\}$.

To define the semantics of the dynamic modalities, we need the following three model transformers corresponding to the three modalities:
For a plausibility model $\M = (M, \leq, V)$ and formula $\phi$, the models $\M^{!\phi}$, $\M^{\Uparrow\phi}$, and $\M^{\uparrow\phi}$ are defined as follows:

$\M^{!\phi} = (M^{!\phi}, \leq^{!\phi}, V^{!\phi})$, where
\begin{itemize}
  \item $M^{!\phi} := \{s \in M \mid \M,s \vDash \phi\}$ ;
  \item $\leq^{!\phi}$ is the restriction of $\leq$ to $M^{!\phi}$ ;
  \item $V^{!\phi}(p) := V(p) \cup M^{!\phi}$.
\end{itemize}

$\M^{\Uparrow\phi} = (M^{\Uparrow\phi}, \leq^{\Uparrow\phi}, V^{\Uparrow\phi})$, where
\begin{itemize}
  \item $M^{\Uparrow\phi} := M$ ;
  \item $s \leq^{\Uparrow\phi} t$ iff either of the following hold: 
    \begin{itemize}
      \item $s \leq t$, where both $s,t \in \| \phi \|_\M$, or both $s,t \notin \| \phi \|_\M$;
      \item $\M,s \vDash \phi$ and $\M,t \not\vDash \phi$;
    \end{itemize}
  \item $V^{\Uparrow\phi}(p) := V(p)$.
\end{itemize}

$\M^{\uparrow\phi} = (M^{\uparrow\phi}, \leq^{\uparrow\phi}, V^{\uparrow\phi})$, where
\begin{itemize}
  \item $M^{\uparrow\phi} := M$ ;
  \item $s \leq^{\uparrow\phi} t$ iff either of the following hold: 
    \begin{itemize}
      \item $s \leq t$, where both $s,t \notin \Min_\leq \|\phi\|_\M$;
      \item $s \in \Min_\leq \|\phi\|_\M$;
    \end{itemize}
  \item $V^{\uparrow\phi}(p) := V(p)$.
\end{itemize}
The semantic clauses of the dynamic modalities are as follows:
\[
\begin{array}{l c l}
\M, s \vDash [!\phi]\psi & \text{iff} & \M,s \not\vDash \phi \text{ or } \M^{!\phi},s \vDash \psi \ ;\\
\M, s \vDash [\Uparrow\phi]\psi & \text{iff} & \M^{\Uparrow\phi},s \vDash \psi \ ; \\
\M, s \vDash [\uparrow\phi]\psi & \text{iff} & \M^{\uparrow\phi},s \vDash \psi \ ; \\

\end{array}
\]
The semantics are implemented as follows:
\begin{code}
pred :: Relation -> World -> [World]
pred r s = [t | (t,s') <- r, s == s']

(|=) :: (PlausibilityModel, World) -> KSBForm -> Bool
(m,s) |= P n      = n `elem` (val m ! s)
(m,s) |= Neg f    = not $ (m,s) |= f
(m,s) |= Con f g  = (m,s) |= f && (m,s) |= g
(m,s) |= Box f    = all (\t -> (m,t) |= f) (pred (rel m) s)
(m,_) |= K f      = all (\t -> (m,t) |= f) (worlds m)
(m,s) |= Ann f g  = (m,s) |= Neg f || (update m f, s) |= g
(m,s) |= Rad f g  = (radical m f, s) |= g
(m,s) |= Cons f g = (conservative m f, s) |= g

trueEverywhere :: PlausibilityModel -> KSBForm -> Bool
trueEverywhere m f = all (\s -> (m,s) |= f ) (worlds m)

update, radical, conservative :: PlausibilityModel -> KSBForm -> PlausibilityModel
update m f = PlM newWorlds newRel newVal where
  newWorlds = [s | s <- worlds m, (m,s) |= f]
  newRel    = [(s,t) | (s,t) <- rel m, s `elem` newWorlds && t `elem` newWorlds]
  newVal    = restrictKeys (val m) (Data.Intset.fromList newWorlds )

radical m f = PlM newWorlds newRel newVal where
  newWorlds  = worlds m
  newRel     = [(s,t) | (s,t) <- rel m, s `elem` trueWorlds && t `elem` trueWorlds] 
             ++ [(s,t) | (s,t) <- rel m, s `notElem` trueWorlds && t `notElem` trueWorlds]
             ++ [(s,t) | s <- trueWorlds, t <- newWorlds, t `notElem` trueWorlds]
  newVal     = val m
  trueWorlds = [s | s <- worlds m, (m,s) |= f]

conservative m f = PlM newWorlds newRel newVal where
  newWorlds  = worlds m
  newRel     = [(s,t) | (s,t) <- rel m, s `notElem` bestWorlds && t `notElem` bestWorlds] ++ [(s,t) | s <- bestWorlds, t <- newWorlds]
  newVal     = val m
  trueWorlds = [s | s <- worlds m, (m,s) |= f]
  bestWorlds = [s | s <- trueWorlds, all (\t -> (s,t) `elem` rel m) newWorlds]
\end{code}
