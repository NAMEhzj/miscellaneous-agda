module BayesianNetworks where


open import Data.List hiding (sum)
open import Agda.Primitive
open import ListStuff
open import Relation.Binary.Core
open import Agda.Builtin.Float
open import Data.Product hiding ( map )
open import Data.Sum hiding (map)
open import Equivalence

data Bool : Set where
  True : Bool
  False : Bool

data Maybe {l} : Set l → Set l where
  Nothing : {a : Set l} → Maybe a
  Just : {a : Set l} → a → Maybe a


data ℕ : Set where
  Z : ℕ
  S : ℕ → ℕ

data Fin : ℕ → Set where
  FZ : {n : ℕ} → Fin (S n)
  FS : {n : ℕ} → Fin n → Fin (S n)


emptyFunc : {l : Level} → {a : Set l} → Fin Z → a
emptyFunc ()


everyFin : (n : ℕ) → List (Fin n)
everyFin Z = []
everyFin (S n) = FZ ∷ map FS (everyFin n)


data Vect {l} : ℕ → Set l → Set l where
  []   : {a : Set l} → Vect Z a
  _::_ : {n : ℕ} → {a : Set l} → a → Vect n a → Vect (S n) a 


toList : {l : Level} {a : Set l} {n : ℕ} → Vect n a → List a 
toList [] = []
toList (x :: ys) = x ∷ (toList ys)


vmap : {k l : Level} → {n : ℕ} → {a : Set k} → {b : Set l} → (a → b) → Vect n a → Vect n b
vmap _ [] = []
vmap f (x :: xs) = (f x :: vmap f xs) 

_!_ : {l : Level} → {n : ℕ} → {a : Set l} → Vect n a → Fin n → a
_!_ [] ()
_!_ (x :: xs) FZ     = x
_!_ (x :: xs) (FS k) = xs ! k




invImageTrue : {n : ℕ} → (Fin n → Bool) → List (Fin n)
invImageTrue {Z} f = []
invImageTrue {S n} f with (f FZ)
...               | True  = FZ ∷ map FS (invImageTrue (f ∘ FS))
...               | False = map FS (invImageTrue (f ∘ FS))


invImageNat : {n : ℕ} → (tns : Vect n ℕ) → (Fin n → Bool) → List ℕ
invImageNat {Z} _ f = []
invImageNat {S n} (tn :: tns) f with (f FZ)
...               | True = (tn) ∷ invImageNat tns (f ∘ FS)
...               | False = invImageNat tns (f ∘ FS)

_+_ : Float → Float → Float
_+_ = primFloatPlus

_*_ : Float → Float → Float
_*_ = primFloatTimes

zero : Float
zero = primNatToFloat 0

one : Float
one = primNatToFloat 1


sum : List Float → Float
sum = foldr _+_ zero








contradiction : {x : Bool} → {l : Level} → {a : Set l} → x ≡ True → x ≡ False → a
contradiction {True} refl ()
contradiction {False} ()


contradictionM : {l1 l2 : Level} → {a : Set l1} → {b : Set l2} → {x : Maybe a} → x ≡ Nothing → Σ a (λ y → x ≡ Just y) → b
contradictionM {x = Nothing} refl ()
contradictionM {x = Just y} ()





lala : {n : ℕ} → {ps : Fin (S n) → Bool} → {tn : ℕ} → {tns : Vect n ℕ} → ps FZ ≡ False → invImageNat (tn :: tns) ps ≡ invImageNat tns (ps ∘ FS)
lala {ps = ps} eq with (ps FZ)
... | True  = contradiction refl eq
... | False = refl


lolo : {n : ℕ} → {ps : Fin (S n) → Bool} → {tn : ℕ} → {tns : Vect n ℕ} → ps FZ ≡ True → invImageNat (tn :: tns) ps ≡ tn ∷ invImageNat tns (ps ∘ FS)
lolo {ps = ps} eq with (ps FZ)
... | True = refl
... | False = contradiction eq refl



MaybeCases : {l : Level} → {a : Set l} → (x : Maybe a) → x ≡ Nothing ⊎ (Σ a (λ v → x ≡ Just v))
MaybeCases Nothing  = inj₁ refl
MaybeCases (Just v) = inj₂ (v , refl)

Cases : (x : Bool) → Σ Bool (λ y → (y ≡ True ⊎ y ≡ False))
Cases True  = (True , inj₁ refl)
Cases False = (False , inj₂ refl)




data Singleton {a} {A : Set a} (x : A) : Set a where
  _with≡_ : (y : A) → x ≡ y → Singleton x

inspect : ∀ {a} {A : Set a} (x : A) → Singleton x
inspect x = x with≡ refl


data BayesNet : {n : ℕ} → Vect n ℕ → Set₁ where
     Nil : BayesNet []
     Node : {size : ℕ} → {tns : Vect size ℕ} →
            BayesNet tns →
            (tn : ℕ) →
            (ps : Fin size → Bool) →
            (cpt : Fin tn → HList (map Fin (invImageNat tns ps)) → Float) →
            BayesNet (tn :: tns)



apply1 : {n : ℕ} → {tns : Vect n ℕ} → {ps : Fin n → Bool} → (HList (map Fin (invImageNat tns ps)) → Float) → HList (map Fin (toList tns)) → Float
apply1 {Z} f _ = f []
apply1 {S n} {tn :: tns} {ps} f (x ∷ yzs) with inspect (ps FZ) | f
...                             | False  with≡ eqF | f' rewrite (lala {n} {ps} {tn} {tns} eqF) = apply1 {tns = tns} f' yzs
...                             | True with≡ eqT | f' rewrite (lolo {n} {ps} {tn} {tns} eqT) = apply1 {tns = tns} (λ ws → f' (x ∷ ws)) yzs


density : {n : ℕ} → {tns : Vect n ℕ} → BayesNet tns → HList (map Fin (toList tns)) → Float
density Nil _ = one
density (Node subNet tn ps cpt) (x ∷ yzs) = (apply1 (cpt x) yzs) * density subNet yzs



maybeToList : {k : ℕ} → Maybe (Fin k) → List (Fin k)
maybeToList {k} Nothing = everyFin k
maybeToList (Just i) = i ∷ [] 



probability1 : {n : ℕ} → {tns : Vect n ℕ} → BayesNet tns → HList (map (List ∘ Fin) (toList tns)) → Float
probability1 {tns = tns} network l rewrite =sym (map-∘-cong Fin List (toList tns)) = sum (map (density network) (listΠ l))



margProb1 : {n : ℕ} → {tns : Vect n ℕ} → BayesNet tns → HList (map (Maybe ∘ Fin) (toList tns)) → Float
margProb1 network = (probability1 network) ∘ (hmap maybeToList)





splitCases : {n : ℕ} → {tns : Vect n ℕ} → (ps : Fin n → Bool)  → ((i : Fin n) → Maybe (Fin (tns ! i))) →
             List ((i : Fin n) → Σ (Maybe (Fin (tns ! i))) (λ arg → arg ≡ Nothing → ps i ≡ False))
splitCases {Z}   ps args = (λ i → emptyFunc i) ∷ []
splitCases {S n} {tn :: tns} ps args with inspect (ps FZ) | (args FZ)
... | True with≡ _ | Nothing  = concat (map (λ i → map (append' i) recSplit) (everyFin tn))
                  where recSplit = splitCases {tns = tns} (ps ∘ FS) (args ∘ FS)
                        append' : Fin tn → ((i : Fin n) → Σ (Maybe (Fin (tns ! i))) (λ arg → arg ≡ Nothing → ps (FS i) ≡ False))
                                         → (i : Fin (S n)) → Σ (Maybe (Fin ((tn :: tns) ! i))) (λ arg → arg ≡ Nothing → ps i ≡ False)
                        append' x ys FZ = (Just x) , (λ arg=noth → contradictionM arg=noth (x , refl))
                        append' x ys (FS i) = ys i
... | _ | (Just x) = map (append' x) recSplit
                  where recSplit = splitCases {tns = tns} (ps ∘ FS) (args ∘ FS)
                        append' : Fin tn → ((i : Fin n) → Σ (Maybe (Fin (tns ! i))) (λ arg → arg ≡ Nothing → ps (FS i) ≡ False))
                                         → (i : Fin (S n)) → Σ (Maybe (Fin ((tn :: tns) ! i))) (λ arg → arg ≡ Nothing → ps i ≡ False)
                        append' x ys FZ = (Just x) , (λ arg=noth → contradictionM arg=noth (x , refl))
                        append' x ys (FS i) = ys i
... | False with≡ eq | Nothing = map appendNothing recSplit
                  where recSplit = splitCases {tns = tns} (ps ∘ FS) (args ∘ FS)
                        appendNothing : ((i : Fin n) → Σ (Maybe (Fin (tns ! i))) (λ arg → arg ≡ Nothing → ps (FS i) ≡ False))
                                         → (i : Fin (S n)) → Σ (Maybe (Fin ((tn :: tns) ! i))) (λ arg → arg ≡ Nothing → ps i ≡ False)
                        appendNothing ys FZ = Nothing , (λ arg=noth → eq)
                        appendNothing ys (FS i) = ys i




apply2 : {n : ℕ} → {tns : Vect n ℕ} → {ps : Fin n → Bool} →
         (HList (map Fin (invImageNat tns ps)) → Float) →
         (args* : (i : Fin n) → Maybe (Fin (tns ! i))) →
         ((i : Fin n) → args* i ≡ Nothing → ps i ≡ False) → Float
apply2 {Z} f _ _       = f []
apply2 {S n} {tn :: tns} {ps} f args* prf with inspect (args* FZ) | inspect (ps FZ) | f
... | _                 | False with≡ eqF | f' rewrite (lala {n} {ps} {tn} {tns} eqF) = apply2 {tns = tns} f' (args* ∘ FS) (prf ∘ FS)
... | Nothing with≡ eqN | True with≡ eqT | _ = contradiction eqT (prf FZ eqN)
... | (Just x) with≡ eJ | True with≡ eqT | f' rewrite (lolo {n} {ps} {tn} {tns} eqT) = apply2 {tns = tns} (λ ys → f' (x ∷ ys)) (args* ∘ FS) (prf ∘ FS)







margProb2 : {n : ℕ} → {tns : Vect n ℕ} → BayesNet tns → ((i : Fin n) → Maybe (Fin (tns ! i))) → Float
margProb2 Nil _ = one
margProb2 {S n} {tn :: tns} (Node subNet .tn ps cpt) args with (args FZ)
...   | Nothing  = margProb2 subNet (args ∘ FS) 
...   | (Just x) = sum (map (λ args* → fullProb (proj₁ ∘ args*) (proj₂ ∘ args*)) (splitCases {n} {tns} ps (args ∘ FS)))
           where fullProb : (args' : (i : Fin n) → Maybe (Fin (tns ! i))) →
                            ((i : Fin n) → args' i ≡ Nothing → ps i ≡ False) → Float
                 fullProb args' prf = (apply2 (cpt x) args' prf) * margProb2 subNet args'
                    





                          
