
open import Data.Bool
open import Data.Maybe hiding (map)
open import Data.Nat hiding (_+_ ; _*_)
open import Data.Fin hiding (_+_)
open import Data.Vec hiding (map ; foldr ; sum ; tail ; concat ; toList)
open import Data.List hiding (lookup ; sum)
open import Agda.Builtin.Float
open import Data.Float
open import Equivalence
open import ListStuff

module BayesianNetworks3 where

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


_:#_ : ∀{l} → {n : ℕ} → {A : Fin (suc n) → Set l} →
       A zero → ((i : Fin n) → A (suc i)) →
       (i : Fin (suc n)) → A i
_:#_ head _ zero = head
_:#_ _ tail (suc i) = tail i

record NodeType : Set₁ where
       field
        type : Set
        predSize : ℕ 
        finite : type ↔ Fin (suc predSize)

open NodeType

everyFin : (n : ℕ) → List (Fin n)
everyFin zero = []
everyFin (suc n) = zero ∷ map suc (everyFin n)


toList : (t : NodeType) → List (type t)
toList t = map (_↔_.from (finite t)) (everyFin (suc (predSize t)))


data BayesNet : {n : ℕ} → Vec NodeType n → Set₁ where
      Nil : BayesNet []
      Node : {n : ℕ} → {ts : Vec NodeType n}  →
             BayesNet ts → (t : NodeType) →  
             (ps : Vec Bool n) →
             (type t → ((i : Fin n) → lookup i  ps ≡ true → type (lookup i ts)) → Float) →
             BayesNet (t ∷ ts)


density : {n : ℕ} → {ts : Vec NodeType n} →
          BayesNet ts → ((i : Fin n) → type (lookup i ts)) →
          Float
density Nil _                       = primNatToFloat 1         
density (Node subNet t ps cpt) args =
          (cpt (args zero) (λ i _ → args' i)) * density subNet args'
                         where args' = tail args



data Singleton {a} {A : Set a} (x : A) : Set a where
  _with≡_ : (y : A) → x ≡ y → Singleton x

inspect : ∀ {a} {A : Set a} (x : A) → Singleton x
inspect x = x with≡ refl



MaybeMaybe : ∀{l} → Bool → Set l → Set l
MaybeMaybe true A = A
MaybeMaybe false A = Maybe A 

forgetFalse : ∀{k l} → {A : Set k} →
              {B : A → Set l} →
              {ps : A → Bool} →
              ((a : A) → MaybeMaybe (ps a) (B a)) →
              (a : A) → ps a ≡ true → B a
forgetFalse {ps = ps} f a eq with f a
... | b rewrite eq = b


toMaybe : ∀{k l} → {A : Set k} →
              {B : A → Set l} →
              {ps : A → Bool} →
              ((a : A) → MaybeMaybe (ps a) (B a)) →
              (a : A) → Maybe (B a)
toMaybe {B = B} {ps} f a with inspect (ps a) | f a
... | true  with≡ eq | b  rewrite eq = just b
... | false with≡ eq | Mb rewrite eq = Mb



splitCases : {n : ℕ} → {ts : Vec NodeType n} →
             (ps : Vec Bool n) →
             ((i : Fin n) → Maybe (type (lookup i ts))) →
             List ((i : Fin n) → MaybeMaybe (lookup i ps) (type (lookup i ts)))
splitCases {zero} _ _ = emptyFunc ∷ []
splitCases {suc n} {t ∷ ts} (false ∷ ps) args = map (args zero :#_) (splitCases ps (tail args))
splitCases {suc n} {t ∷ ts} (true  ∷ ps) args with (args zero)
... | (just x) = map (x :#_) (splitCases ps (tail args))
... | nothing  = concat (map (λ x → map (x :#_) (splitCases ps (tail args))) (toList t))


margProb : {n : ℕ} → {ts : Vec NodeType n} →
           BayesNet ts →
           ((i : Fin n) → Maybe (type (lookup i ts))) →
           Float
margProb Nil _ = primNatToFloat 1
margProb {suc n} {t ∷ ts} (Node subNet t ps cpt) args with (args zero)
... | nothing  = margProb subNet (tail args)
... | (just x) = sum (map chain (splitCases ps (tail args)))
            where chain : ((i : Fin n) →
                          MaybeMaybe (lookup i ps) (type (lookup i ts))) →
                          Float
                  chain args' = (cpt x (forgetFalse args')) * margProb subNet (toMaybe args')

