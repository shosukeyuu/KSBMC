\section{Simple Tests}
\label{sec:simpletests}

We now perform static tests on two example models in \ref{sec:Examples} using the Hspec library.
\hide{
\begin{code}
module Main where

import Syntax
import Semantics
import Examples

import Test.Hspec
import Test.QuickCheck
\end{code}
}

First, we have the Albert Winestein model: 

\begin{code}
main :: IO ()
main = hspec $ do
  describe "Albert Winestein Example" $ do
    it "Initially, Albert believes he is a genius;" $
      albertModelState |= albert1 `shouldBe` True
    it "he knows he's either a genius or drunk;" $
      albertModelState |= albert2 `shouldBe` True
    it "he believes he's not drunk;" $
      albertModelState |= albert3 `shouldBe` True
    it "but conditional on him being drunk, he would believe he's not a genius;" $
      albertModelState |= albert4 `shouldBe` True
    it "in the actual world, he is both drunk and a genius." $
      albertModelState |= albert5 `shouldBe` True
    it "Suppose he took a blood test, proving he is drunk beyond doubt. Then he knows he's drunk." $
      albertModelState |= albert6 `shouldBe` True
    it "Suppose his trusted friend Mary Curry tells him he's drunk. Then he strongly believes he's drunk." $
      albertModelState |= albert7 `shouldBe` True
    it "Suppose Mary Curry tells him he's drunk, but he doesn't trust her too much. Then he only believes he's drunk," $
      albertModelState |= albert8 `shouldBe` True
    it "but this belief is not strong." $
      albertModelState |= albert9 `shouldBe` False   
\end{code}

Then, we test the robot model:
\begin{code}
  describe "Robot Example" $ do
    it "Initially, the robot believes there is neither a mine nor an enemy;" $
      trueEverywhere robotModel robot1 `shouldBe` True
    it "but this belief is not strong." $
      trueEverywhere robotModel robot2 `shouldBe` False
    it "After its sensors indicate vibrations, it strongly believes there is an enemy." $
      trueEverywhere robotModel robot3 `shouldBe` True
    it "Then, its metal detector indicates a mine, so it strongly believes there is a mine." $
      trueEverywhere robotModel robot4 `shouldBe` True
    it "It still believes there is an enemy, but this belief is no longer strong." $
      trueEverywhere robotModel robot5 `shouldBe` True
    it "Afterwards, the controller announces that whatever it currently believes about the enemy is false. Then it knows that there is no enemy, and believes that there is a mine." $
      trueEverywhere robotModel robot6 `shouldBe` True
    it "If instead the robot first receives the controller's message, then senses vibration, and finally detects a mine, then it knows that there is an enemy, and believes there is a mine." $
      trueEverywhere robotModel robot7 `shouldBe` True
\end{code} 
To run the tests, use \verb|stack test|.
