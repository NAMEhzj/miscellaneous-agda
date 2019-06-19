

open import Agda.Builtin.Float
open import Equivalence hiding (map)
open import Data.Nat using (ℕ ; zero ; suc) renaming (_+_ to _+ℕ_ ; _*_ to _*ℕ_)
open import Data.Fin using (Fin ; zero ; suc)
open import Data.List using (List ; [] ; _∷_ ; foldr ; map)

module Butcher where

{- For Runge-Kutta methods (numerical integration / solving of differential equations), 
   there are certain equations in the coefficients of the method that need to hold 
   for the method to be exact to a certain degree (the error is in 𝒪(h^(q+1)), 
   for some number q and the stepsize h). John C. Butcher described how one can define what
   these equations are, based on the order (q). 
   (See "Coefficients for the study of Runge-Kutta integration processes", J.C.Butcher, 1962)
   There is one equation for each tree of size less or equal q, and the RHS 
   (depending on the coefficients of the RKM) as well as the LHS (constant) can be 
   recursively determined from the tree. These two algorithms (butcherRHS and butcherLHS) 
   are what I implemented here. -}


_+_ = primFloatPlus

_*_ = primFloatTimes

_/_ = primFloatDiv

sum : {n : ℕ} → (Fin n → Float) → Float
sum {zero} _ = primNatToFloat 0
sum {suc n} x = x zero + sum (λ i → x (suc i))


prod : List Float → Float
prod = foldr  _*_ (primNatToFloat 1)

data Tree : ℕ → Set where
  Node : {n : ℕ} → List (Tree n) → Tree (suc n)


rank : {n : ℕ} → Tree n → ℕ
rank (Node children) = foldr (λ t x → rank t +ℕ x) 1 children 


butcherLHS' : {s : ℕ} → {n : ℕ} → (Fin (suc s) → Fin s → Float) → Fin (suc s) → Tree n → Float
butcherLHS' {s} as i (Node children) = sum (λ j → (as i j) * prod (map (rec j) children))
                where rec : {n : ℕ} → Fin s → Tree n → Float
                      rec j t = butcherLHS' as (suc j) t

butcherLHS : {s : ℕ} → {n : ℕ} → (Fin s → Fin s → Float) → (Fin s → Float) → Tree n → Float
butcherLHS {s} as bs = butcherLHS' bs&as zero
                      where bs&as : Fin (suc s) → Fin s → Float
                            bs&as zero = bs
                            bs&as (suc j) = as j

gamma : {n : ℕ} → Tree n → ℕ
gamma t@(Node children) = foldr (λ t' x → gamma t' *ℕ x) (rank t) children

butcherRHS : {n : ℕ} → Tree n → Float
butcherRHS t = (primNatToFloat 1) / (primNatToFloat (gamma t))
