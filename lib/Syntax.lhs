\section{Syntax of }\label{sec:Syntax}

The language of $K\Box$ is defined over a set of propositional variables $\Prop$:
\[\phi ::= p \mid \neg \phi \mid \phi \wedge \phi \mid \Box \phi \mid K \phi \ ,\]
where $\ in \Prop$.     We call $\Box$ and $K$ the \emph{safe belief} and \emph{knowledge} operator respectively.

Below is the implementation of the syntax of $K\Box$, where we index the propositional variables with integers:
\begin{code}
module Syntax where

data KSBForm = P Int | Neg KSBForm | Con KSBForm KSBForm | Box KSBForm | K KSBForm 
\end{code}
The other boolean operators $\vee, \rightarrow, \top, \bot$ can be defined in the usual way:

\begin{code}
dis, implies :: KSBForm -> KSBForm -> KSBForm
dis f g = Neg $ Con (Neg f) (Neg g)
implies f = dis (Neg f)
top, bot :: KSBForm
top = dis (P 0) (Neg $ P 0)
bot = Neg top
\end{code}

The \emph{conditional belief} and \emph{belief} operators can be defined as follows:
\begin{align*}
B^\phi \psi &:= \tilde K \phi \to \tilde K (\phi \wedge \Box(\phi \to \psi)) \ ; \\
B \phi      &:= B ^\top \phi \ ,
\end{align*}
where $\tilde K \phi := \neg K \neg \phi$ is the dual of the knowledge operator.

\begin{code}
cBel :: KSBForm -> KSBForm -> KSBForm
cBel f g = (Neg . K . Neg) f `implies` (Neg . K . Neg) (f `Con` Box (f `implies` g))

bel :: KSBForm -> KSBForm
bel = cBel top
\end{code}