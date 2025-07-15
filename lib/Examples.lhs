\section{Examples}\label{sec:Examples}

The following example is taken from Homework 3 of the course:

\hide{
\begin{code}
module Examples where

import Data.IntMap ( fromList )

import Syntax
import Semantics
\end{code}    
}
\begin{code}
m,e :: KSBForm
m = P 1
e = P 2
s1, s2, s3, s4 :: World
s1 = 1
s2 = 2
s3 = 3
s4 = 4
robotModel :: PlausibilityModel
robotModel = rtClosure $ PlM rworlds rrel rval where
  rworlds = [s1,s2,s3,s4]
  rrel    = [(s1,s2), (s1,s3), (s2,s3), (s3,s2), (s2,s4), (s3,s4)]
  rval    = fromList [(s1, []), (s2, [2]), (s3,[1]),(s4,[1,2])]
\end{code}