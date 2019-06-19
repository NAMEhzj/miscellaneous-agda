
open import Data.Bool
open import Data.Maybe hiding (map)
open import Data.Nat hiding (_+_ ; _*_)
open import Data.Fin hiding (_+_)
open import Data.Vec hiding (map ; foldr ; sum ; tail)
open import Data.List hiding (lookup ; sum)
open import Agda.Builtin.Float
open import Data.Float
open import Equivalence
open import ListStuff

module BayesianNetworks2 where

_*_ : Float → Float → Float
_*_ = primFloatTimes

sum : List Float → Float
sum = foldr primFloatPlus (primNatToFloat 0)

emptyFunc : ∀{l} → {A : Fin zero → Set l} → (i : Fin zero) → A i
emptyFunc ()

tail : ∀{l} {n : ℕ} → {A : Fin (suc n) → Set l} →
       (f : (i : Fin (suc n)) → A i) →
       (i : Fin n) → A (suc i)
tail f i = f (suc i)

record NodeType : Set₁ where
       field
        type : Set
        card-1 : ℕ
        finite : type ↔ Fin (suc card-1)

open NodeType


invImageTrue : {n : ℕ} → (Fin n → Bool) →
               List (Fin n)
invImageTrue {zero}  f = []
invImageTrue {suc i} f with (f zero)
... | true  = zero ∷ map suc (invImageTrue (tail f))
... | false = map suc (invImageTrue (tail f))



types : {n : ℕ} → Vec NodeType n → List (Fin n) → List Set
types ts = map (λ i → (type (lookup i ts)))

data BayesNet : {n : ℕ} → Vec NodeType n → Set₁ where
      Nil : BayesNet []
      Node : {n : ℕ} → {ts : Vec NodeType n}  →
             BayesNet ts → (t : NodeType) →  
             (ps : Fin n → Bool) →
             (type t → HList (types ts (invImageTrue ps)) → Float) →
             BayesNet (t ∷ ts)



map' : ∀{k l} → {A : Set k} → {B : A → Set l} →
       ((x : A) → B x) → (xs : List A) → HList (map B xs)
map' f []       = []
map' f (x ∷ xs) = f x ∷ map' f xs


density : {n : ℕ} → {ts : Vec NodeType n} →
          BayesNet ts → ((i : Fin n) → type (lookup i ts)) →
          Float
density Nil _                       = primNatToFloat 1         
density (Node subNet t ps cpt) args =
          (cpt (args zero) (map' args' (invImageTrue ps))) * density subNet args'
                         where args' = tail args

