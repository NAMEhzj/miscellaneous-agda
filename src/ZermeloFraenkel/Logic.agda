module Logic where

open import Relation.Binary.Core using (_≡_ ; refl)
open import Relation.Nullary hiding (¬_)
open import Data.Empty
open import Data.Sum

data Bool : Set where
    T : Bool
    F : Bool


¬_ : Bool → Bool
¬ T = F
¬ F = T

infix 10 ¬_ 


_∨_ : Bool → Bool → Bool
T ∨ b = T
F ∨ b = b


infixr 8 _∨_

_∧_ : Bool → Bool → Bool
F ∧ b = F
T ∧ b = b

infixr 9 _∧_

_⇒_ : Bool → Bool → Bool
a ⇒ b =  ¬ a ∨ b

infixr 7 _⇒_

_⇔_ : Bool → Bool → Bool
a ⇔ b = (a ⇒ b) ∧ (b ⇒ a)

infixr 6 _⇔_


[_] : Bool → Set
[ a ] = a ≡ T

infix 5 [_]

_↯_ : {a c : Bool} → [ a ] → [ ¬ a ] → [ c ]
_↯_ refl ()

proofByContradiction₁ : {a : Bool} → ([ ¬ a ] → [ a ]) → [ a ]
proofByContradiction₁ {T} f = refl 
proofByContradiction₁ {F} f = f refl

proofByContradiction₂ : {a : Bool} → ([ a ] → [ ¬ a ]) → [ ¬ a ]
proofByContradiction₂ {F} f = refl 
proofByContradiction₂ {T} f = f refl

∨-intro₁ : {a b : Bool} → [ a ] → [ a ∨ b ]
∨-intro₁ refl = refl

∨-intro₂ : {a b : Bool} → [ b ] → [ a ∨ b ]
∨-intro₂ {F} {T} refl = refl
∨-intro₂ {T} {T} refl = refl

∨-elim : {a b c : Bool} → [ a ∨ b ] → ([ a ] → [ c ]) → ([ b ] → [ c ]) → [ c ]
∨-elim {T} refl f _ = f refl
∨-elim {F} {T} refl _ g = g refl

∧-intro : {a b : Bool} → [ a ] → [ b ] → [ a ∧ b ]
∧-intro refl refl = refl

∧-elim₁ : {a b : Bool} → [ a ∧ b ] → [ a ]
∧-elim₁ {T} {T} refl = refl
∧-elim₁ {F} ()

∧-elim₂ : {a b : Bool} → [ a ∧ b ] → [ b ]
∧-elim₂ {T} {T} refl = refl
∧-elim₂ {F} ()

⇒-intro : {a b : Bool} → ([ a ] → [ b ]) → [ a ⇒ b ]
⇒-intro {F} {b} _ = ∨-intro₁ {T} {b} refl
⇒-intro {T} {T} _ = ∨-intro₂ {T} refl
⇒-intro {T} {F} f =  f refl ↯ refl

⇒-elim : {a b : Bool} → [ a ⇒ b ] → [ a ] → [ b ]
⇒-elim {b = T} _ _ = refl
⇒-elim {T} {F} ()  
⇒-elim {F} {F} _ () 

doubleNeg : (a : Bool) → ¬ (¬ a) ≡ a
doubleNeg T = refl
doubleNeg F = refl

doubleNeg-elim : {a : Bool} → [ ¬ (¬ a) ] → [ a ]
doubleNeg-elim {T} refl = refl
doubleNeg-elim {F} ()


doubleNeg-intro : {a : Bool} → [ a ] → [ ¬ (¬ a) ]
doubleNeg-intro {T} refl = refl
doubleNeg-intro {F} ()


cases : (a : Bool) → [ a ] ⊎ [ ¬ a ]
cases T = inj₁ refl
cases F = inj₂ refl

contrapos : {a b : Bool} → ([ a ] → [ b ]) → [ ¬ b ] → [ ¬ a ]
contrapos {T} {T} _ [F] = [F]
contrapos {T} {F} f _   = f refl
contrapos {F}     _ _   = refl


not-∨ : {a b : Bool} → [ ¬ (a ∨ b) ] → [ (¬ a) ∧ (¬ b) ]
not-∨ {F} {F} _ = refl
not-∨ {F} {T} ()
not-∨ {T} ()

not-∧-not : {a b : Bool} → [ (¬ a) ∧ (¬ b) ] → [ ¬ (a ∨ b) ]
not-∧-not {F} {F} _ = refl
not-∧-not {F} {T} ()
not-∧-not {T} ()

not-∧ : {a b : Bool} → [ ¬ (a ∧ b) ] → [ (¬ a) ∨ (¬ b) ]
not-∧ {T} {T} ()
not-∧ {T} {F} _ = refl
not-∧ {F}     _ = refl


not-∨-not : {a b : Bool} → [ (¬ a) ∨ (¬ b) ] → [ ¬ (a ∧ b) ]
not-∨-not {T} {T} ()
not-∨-not {T} {F} _ = refl
not-∨-not {F}     _ = refl
