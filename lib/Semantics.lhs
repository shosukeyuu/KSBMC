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

import Data.List ( nub )
import Data.IntMap (IntMap, (!), delete, restrictKeys, fromList) 
import qualified Data.IntSet as Data.Intset

import Syntax
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
Note that $\Box$ is the Kripke modality of the converSse plausibility relation $\geq$, due to our convention.

\begin{code}
pred :: Relation -> World -> [World]
pred r s = [t | (t,s') <- r, s == s']

(|=) :: (PlausibilityModel, World) -> KSBForm -> Bool
(m,s) |= P n     = n `elem` (val m ! s)
(m,s) |= Neg f   = not $ (m,s) |= f
(m,s) |= Con f g = (m,s) |= f && (m,s) |= g
(m,s) |= Box f   = all (\t -> (m,t) |= f) (pred (rel m) s)
(m,_) |= K f     = all (\t -> (m,t) |= f) (worlds m)
\end{code}

\begin{code}
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
