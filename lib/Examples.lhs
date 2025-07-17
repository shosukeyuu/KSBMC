\section{Examples}\label{sec:Examples}

The following example is taken from Homework 3 of the course:

\hide{
\begin{code}
module Examples where

import Syntax
import Semantics

import Data.IntMap ( fromList )
\end{code}    
}
\begin{code}
m,e :: Int
m = 1
e = 2
s1, s2, s3, s4 :: World
s1 = 1
s2 = 2
s3 = 3
s4 = 4
robotModel :: PlausibilityModel
robotModel = rtClosure $ PlM rworlds rrel rval where
  rworlds = [s1,s2,s3,s4]
  rrel    = [(s1,s2), (s1,s3), (s2,s3), (s3,s2), (s2,s4), (s3,s4)]
  rval    = fromList [(s1, []), (s2, [e]), (s3,[m]),(s4,[m,e])]

-- Whatever you currently believe about the enemy is false
robot1, robot2, robot3, robot4, beFalse :: KSBForm
robot1 = bel (Con (Neg $ P e) (Neg $ P d))
robot2 = sBel (Con (Neg $ P e) (Neg $ P d))
robot3 = Rad (P e) $ Rad (P m) $ Ann beFalse $ bigCon [bel (P m), bel (Neg $ P e), K (Neg $ P e)]
beFalse = Con (bel (P e) `implies` Neg (P e)) (bel (Neg $ P e) `implies` P e)
robot4 = undefined

robot5, robot6 :: KSBForm
robot5 = Rad (P e) $ Rad (P m) $ Ann beFalse $ bigCon [bel (P m), bel (Neg $ P e), K (Neg $ P e)]

robot6 = Ann beFalse $ Rad (P e) $ Rad (P m) $ bigCon [bel (P m), bel (P e), K (P e)]
\end{code}

The following is the Albert Winestein example from the lecture slides:
\begin{code}
d,g :: Int
d = 1
g = 2
w1, w2, w3 :: World
w1 = 1
w2 = 2
w3 = 3
albertModel :: PlausibilityModel
albertModel = rtClosure $ PlM aworlds arel aval where
  aworlds = [w1,w2,w3] 
  arel    = [(w1,w2), (w2,w3)]
  aval    = fromList [(w1,[g]), (w2,[d]), (w3, [d,g]) ] 
albertModelState :: (PlausibilityModel, World) 
albertModelState = (albertModel, w3)
-- He knows that he's a genius or drunk
albert1, albert2, albert3, albert4, albert5, albert6, albert7, albert8, albert9 :: KSBForm
albert1 = bel (P g)
albert2 = K (dis (P g) (P d))
albert3 = bel (Neg $ P d)
albert4 = cBel (P d) (Neg $ P g)
albert5 = Con (P d) (P g) 
albert6 = Ann (P d) (K $ P d)
albert7 = Rad (P d) (sBel $ P d)
albert8 = Cons (P d) (bel $ P d)
albert9 = Cons (P d) (sBel $ P d)
\end{code}