module ListStuff where

open import Data.List
open import Agda.Primitive
open import Relation.Binary.Core
open import Equivalence



map-∘-cong : {k l m : Level} → {a : Set k} → {b : Set l} → {c : Set m} →
             (f : a → b) → (g : b → c) → (l : List a) → map g (map f l) ≡ map (g ∘ f) l
map-∘-cong _ _ [] = refl
map-∘-cong f g (x ∷ xs) = map g (map f (x ∷ xs))       =⟨ refl ⟩
                          g (f x) ∷ (map g (map f xs)) =⟨ map-∘-cong f g xs under (g (f x) ∷_) ⟩
                          g (f x) ∷ (map (g ∘ f) xs)   =⟨ refl ⟩
                          map (g ∘ f) (x ∷ xs) □=


data HList {l} : (ts : List (Set l)) → Set l where
  [] : HList []
  _∷_ : {t : Set l} → {ts : List (Set l)} → t → HList ts → HList (t ∷ ts)


hmap : {l1 l2 l3 : Level} → {α : Set l1} → {β : α → Set l2} →
       {γ : α → Set l3} → {as : List α} → ({a : α} → β a → γ a) → HList (map β as) → HList (map γ as)
hmap {as = []} f [] = []
hmap {as = a ∷ as} f (x ∷ ys) = f x ∷ (hmap f ys)



listΠ : {l : Level} → {ts : List (Set l)} → HList (map List ts) → List (HList ts) 
listΠ {ts = []}        []           = [] ∷ []
listΠ {ts = (t ∷ ts)} (xs ∷ yszs) = concat (map (λ x → map (x ∷_) (listΠ yszs)) xs) -- [ x :: yzs | x <- xs, yzs <- yszs ]


