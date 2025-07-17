\section{Examples}\label{sec:Examples}

In this section, we encode two example models and some formulas, used to test our implementation in section \ref{sec:simpletests}


The first is the Albert Winestein example from the lecture slides:

\hide{
\begin{code}
module Examples where

import Syntax
import Semantics

import Data.IntMap ( fromList )
\end{code}    
}
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
The second example is the robot example from Homework 3:
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

robot1, robot2, robot3, robot4, robot5, robot6, robot7, beFalse :: KSBForm
robot1 = bel (Neg $ Con (P e) (Neg $ P d))
robot2 = sBel (Neg $ Con (P e) (Neg $ P d))
robot3 = Rad (P e) $ sBel (P e)
robot4 = Rad (P e) $ Rad (P m) $ sBel (P m)
robot5 = Rad (P e) $ Rad (P m) $ Con (bel $ P e) (Neg $ sBel $ P e)
-- whatever you currently believe about the enemy is false
beFalse = Con (bel (P e) `implies` Neg (P e)) (bel (Neg $ P e) `implies` P e)
robot6 = Rad (P e) $ Rad (P m) $ Ann beFalse $ Con (K $ Neg $ P e) (bel $ P m)
robot7 = Ann beFalse $ Rad (P e) $ Rad (P m) $ Con (K $ P e) (bel $ P m)
\end{code}