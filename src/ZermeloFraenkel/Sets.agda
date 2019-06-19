
open import Logic
open import Relation.Binary.Core hiding ( _⇒_ ) 
open import Data.Product
open import Data.Sum
open import Equivalence

module Sets where


infix 11 _∈_
infix 11 _∉_
infix 11 _≐_
postulate
 ZFSet : Set
 _∈_ : ZFSet → ZFSet → Bool
 _≐_ : ZFSet → ZFSet → Bool
 ≐-intro : {x y : ZFSet} → x ≡ y → [ x ≐ y ]
 ≐-elim : {x y : ZFSet} → [ x ≐ y ] → x ≡ y 


_∉_ : ZFSet → ZFSet → Bool
x ∉ y = ¬ (x ∈ y) 

Pred : Set
Pred = ZFSet → Bool

¬' : Pred → Pred
¬' P x = ¬ P x

postulate
 ∀ll : Pred → Bool
 ∀ll-intro : {P : Pred} → ((x : ZFSet) → [ P x ]) → [ ∀ll P ]
 ∀ll-elim : {P : Pred} → [ ∀ll P ] → (x : ZFSet) → [ P x ]
 
∃x : Pred → Bool
∃x P = ¬ (∀ll (¬' P))

∃x-intro : {P : Pred} → Σ ZFSet (λ x → [ P x ]) → [ ∃x P ]
∃x-intro {P} (x , Px) = proofByContradiction₂ contradiction
                     where contradiction : [ ∀ll (¬' P) ] → [ ∃x P ]
                           contradiction ∀¬P = Px ↯ (∀ll-elim ∀¬P x)
{-
∃x-transport : {P Q : Pred} → (Σ ZFSet (λ x → [ P x ]) → Σ ZFSet (λ y → [ Q y ])) → [ ∃x P ] → [ ∃x Q ]
∃x-transport {P} {Q} f = contrapos transport1
     where transport1 : [ ∀ll (¬' Q) ] → [ ∀ll (¬' P) ]
           transport1 [∀¬Q] = ∀ll-intro transp11
              where transp12 : (x : ZFSet) → [ P x ] → [ ¬ P x ]
                    transp12 x [Px] with (f (x , [Px]))
                    ...              | (y , [Qy]) = [Qy] ↯ (∀ll-elim [∀¬Q] y)
                    transp11 : (x : ZFSet) → [ ¬ (P x) ]
                    transp11 x with (cases (P x)) 
                    ...         | (inj₁ [Px])  = transp12 x [Px] 
                    ...         | (inj₂ [¬Px]) = [¬Px]
-}                    

∃x-cong : {P : Pred} → {b : Bool} → ((x : ZFSet) → [ P x ] → [ b ]) → [ ∃x P ] → [ b ]
∃x-cong {P} {b} f = doubleNeg-elim ∘ (contrapos cong1)
                 where cong1 : [ ¬ b ] → [ ∀ll (¬' P) ]
                       cong1 ¬b = ∀ll-intro cong2
                        where cong2 : (x : ZFSet) → [ ¬ (P x) ]
                              cong2 x = proofByContradiction₂ cong3
                                where cong3 : [ P x ] → [ ¬ P x ]
                                      cong3 Px = (f x Px) ↯ ¬b
   


postulate
 chooseUnique : (P : Pred) → [ ∃x P ] → ((x y : ZFSet) → [ P x ] → [ P y ] → x ≡ y ) → Σ ZFSet (λ x → [ P x ])

postulate
 ZF1 : [ ∀ll (λ A → ∀ll (λ B → (A ≐ B ⇔ ∀ll (λ C → C ∈ A ⇔ C ∈ B)))) ]  -- extensionality of ∈


same∈ : (x y : ZFSet) → [ ∀ll (λ z → z ∈ x ⇔ z ∈ y) ] → x ≡ y
same∈ x y [∀z-z∈x⇔z∈y] = ≐-elim (⇒-elim (∧-elim₂ (∀ll-elim (∀ll-elim ZF1 x) y)) [∀z-z∈x⇔z∈y])

postulate
 ZF2 : [ ∃x (λ E → ∀ll (λ A → ¬ A ∈ E)) ]                               -- empty set

empty : Pred
empty x = ∀ll (λ y → ¬ y ∈ x)

empty-unique : (x y : ZFSet) → [ empty x ] → [ empty y ] → x ≡ y
empty-unique x y [emptx] [empty] = same∈ x y (∀ll-intro (λ z → ∧-intro (⇒-intro (x⊂y z)) (⇒-intro (y⊂x z))))
             where x⊂y : (z : ZFSet) → [ z ∈ x ] → [ z ∈ y ]
                   x⊂y z [z∈x] = [z∈x] ↯ (∀ll-elim [emptx] z)
                   y⊂x : (z : ZFSet) → [ z ∈ y ] → [ z ∈ x ]
                   y⊂x z [z∈y] = [z∈y] ↯ (∀ll-elim [empty] z)

emptySet : Σ ZFSet (λ x → [ empty x ])
emptySet = chooseUnique empty ZF2 empty-unique

∅ : ZFSet
∅ = proj₁ emptySet

∅-emtpy : (x : ZFSet) → [ ¬ x ∈ ∅ ]
∅-emtpy = ∀ll-elim (proj₂ emptySet) 


postulate
 ZF3 : [ ∀ll (λ A → ∀ll (λ B → ∃x (λ P → ∀ll (λ D → ((D ∈ P) ⇔ (D ≐ A) ∨ (D ≐ B)))))) ] -- pair set {A,B}

pairOf : ZFSet → ZFSet → Pred
pairOf x y z = ∀ll (λ w → (w ∈ z) ⇔ (w ≐ x) ∨ (w ≐ y))

pairOf-unique : (x y : ZFSet) → (z1 z2 : ZFSet) → [ pairOf x y z1 ] → [ pairOf x y z2 ] → z1 ≡ z2
pairOf-unique x y z1 z2 [z1=x&y] [z2=x&y] = same∈ z1 z2 (∀ll-intro (λ w → w ∈ z1            ⇔⟨ (∀ll-elim [z1=x&y]) w ⟩
                                                                          (w ≐ x) ∨ (w ≐ y) ⇔⟨ ⇔sym {w ∈ z2} ((∀ll-elim [z2=x&y]) w) ⟩
                                                                          w ∈ z2 □⇔))

pairSet : (x y : ZFSet) → Σ ZFSet (λ z → [ pairOf x y z ])
pairSet x y = chooseUnique (pairOf x y) (∀ll-elim (∀ll-elim ZF3 x) y) (pairOf-unique x y)

〚_&_〛 : ZFSet → ZFSet → ZFSet
〚 x & y 〛 = proj₁ (pairSet x y)


fstInPair : (x y : ZFSet) → [ x ∈ 〚 x & y 〛 ]
fstInPair x y = ⇒-elim (∧-elim₂ (∀ll-elim (proj₂ (pairSet x y)) x)) (∨-intro₁ (≐-intro refl))

sndInPair : (x y : ZFSet) → [ y ∈ 〚 x & y 〛 ]
sndInPair x y = ⇒-elim (∧-elim₂ {y ∈ 〚 x & y 〛 ⇒ (y ≐ x) ∨ (y ≐ y)} (∀ll-elim (proj₂ (pairSet x y)) y)) (∨-intro₂ (≐-intro {y} refl))


nothingElseInPair : (x y z : ZFSet) → [ ¬ z ≐ x ] → [ ¬ z ≐ y ] → [ ¬ z ∈ 〚 x & y 〛 ]
nothingElseInPair x y z z≠x z≠y with cases (z ∈ 〚 x & y 〛)
...                              | (inj₁ z∈[xy])  = z≐y∨z≐x ↯ ¬z≐y∨z≐x
                                           where ¬z≐y∨z≐x : [ ¬ ((z ≐ x) ∨ (z ≐ y)) ]
                                                 ¬z≐y∨z≐x = not-∧-not {z ≐ x} (∧-intro z≠x z≠y)
                                                 z≐y∨z≐x : [ (z ≐ x) ∨ (z ≐ y) ]
                                                 z≐y∨z≐x = ⇒-elim (∧-elim₁ (∀ll-elim (proj₂ (pairSet x y)) z)) z∈[xy]
...                              | (inj₂ ¬z∈[xy]) = ¬z∈[xy]

〚_〛 : ZFSet → ZFSet
〚 x 〛 = 〚 x & x 〛

inSingle : (x : ZFSet) → [ x ∈ 〚 x 〛 ]
inSingle x = fstInPair x x

notInSingle : (x y : ZFSet) → [ ¬ y ≐ x ] → [ y ∉ 〚 x 〛 ]
notInSingle x y x≠x = nothingElseInPair x x y x≠x x≠x  


postulate 
 ZF4 : [ ∀ll (λ A → ∃x (λ U → ∀ll (λ C → C ∈ U ⇔ ∃x (λ D → C ∈ D ∧ D ∈ A)))) ] -- union over a set of sets
 

unionOf : ZFSet → Pred
unionOf x u = ∀ll (λ y → y ∈ u ⇔ ∃x (λ z → y ∈ z ∧ z ∈ x)) 

unionOf-unique : (x : ZFSet) → (u1 u2 : ZFSet) → [ unionOf x u1 ] → [ unionOf x u2 ] → u1 ≡ u2
unionOf-unique x u1 u2 u1=Ux u2=Ux =  same∈ u1 u2 (∀ll-intro (λ y → y ∈ u1                     ⇔⟨ ∀ll-elim u1=Ux y ⟩
                                                                    (∃x (λ z → y ∈ z ∧ z ∈ x)) ⇔⟨ ⇔sym {y ∈ u2}(∀ll-elim u2=Ux y) ⟩
                                                                    y ∈ u2 □⇔))

unionSet : (x : ZFSet) → Σ ZFSet (λ u → [ unionOf x u ])
unionSet x = chooseUnique (unionOf x) (∀ll-elim ZF4 x) (unionOf-unique x)

⋃ : ZFSet → ZFSet
⋃ x = proj₁ (unionSet x)

inUnionBy : (x y z : ZFSet) → [ y ∈ z ] → [ z ∈ x ] → [ y ∈ ⋃ x ]
inUnionBy x y z y∈z z∈x = ⇒-elim (∧-elim₂ (∀ll-elim (proj₂ (unionSet x)) y)) (∃x-intro (z , ∧-intro y∈z z∈x))

notInUnion : (x y : ZFSet) → ((z : ZFSet) → [ z ∈ x ] → [ y ∉ z ]) → [ y ∉ ⋃ x ] 
notInUnion x y f = proofByContradiction₂ contradiction
                     where contradiction : [ y ∈ ⋃ x ] → [ y ∉ ⋃ x ]
                           contradiction y∈Ux = ∃x-cong repFunction (⇒-elim (∧-elim₁ (∀ll-elim (proj₂ (unionSet x)) y)) y∈Ux)
                            where repFunction : (z : ZFSet) → [ y ∈ z ∧ z ∈ x ] → [ ¬ (y ∈ ⋃ x) ]
                                  repFunction z y∈z∧z∈x with cases (z ∈ x)
                                  ...                     | (inj₁ z∈x) = ∧-elim₁ y∈z∧z∈x ↯ f z z∈x
                                  ...                     | (inj₂ z∉x) = ∧-elim₂ y∈z∧z∈x ↯ z∉x

infixr 15 _∪_

_∪_ : ZFSet → ZFSet → ZFSet
x ∪ y = ⋃ 〚 x & y 〛

inBinUnion₁ : (x y : ZFSet) → (z : ZFSet) → [ z ∈ x ] → [ z ∈ x ∪ y ]
inBinUnion₁ x y z z∈x = inUnionBy 〚 x & y 〛 z x z∈x (fstInPair x y)

inBinUnion₂ : (x y : ZFSet) → (z : ZFSet) → [ z ∈ y ] → [ z ∈ x ∪ y ]
inBinUnion₂ x y z z∈y = inUnionBy 〚 x & y 〛 z y z∈y (sndInPair x y)

notInBinUnion : (x y : ZFSet) → (z : ZFSet) → [ z ∉ x ] → [ z ∉ y ] → [ z ∉ (x ∪ y) ]
notInBinUnion x y z z∉x z∉y = notInUnion 〚 x & y 〛 z notInAnySet
                                    where notInAnySet : (w : ZFSet) → [ w ∈ 〚 x & y 〛 ] → [ z ∉ w ]
                                          notInAnySet w w∈[x&y] = proofByContradiction₂ (λ z∈w → z∈w→z∈x∨y z∈w ↯ not-∧-not {z ∈ x} (∧-intro z∉x z∉y))
                                            where w=x∨w=y : [ w ≐ x ∨ w ≐ y ]
                                                  w=x∨w=y = ⇒-elim (∧-elim₁ (∀ll-elim (proj₂ (pairSet x y)) w)) w∈[x&y]
                                                  z∈w→z∈x∨y : [ z ∈ w ] → [ z ∈ x ∨ z ∈ y ]
                                                  z∈w→z∈x∨y z∈w = ∨-elim {c = z ∈ x ∨ z ∈ y} w=x∨w=y
                                                                  (λ w=x → ∨-intro₁ {z ∈ x} [ =sym (≐-elim w=x) ]and[ z∈w ])
                                                                  (λ w=y → ∨-intro₂ {z ∈ x} [ =sym (≐-elim w=y) ]and[ z∈w ])

postulate
 ZF5 : [ ∃x (λ I → (∅ ∈ I ∧ ∀ll (λ A → A ∈ I ⇒ A ∪ 〚 A 〛 ∈ I))) ]  -- there is an infinite set (smallest is ℕ) 
 ZF6 : [ ∀ll (λ A → ∃x (λ P → (∀ll (λ B → B ∈ P ⇔ ∀ll (λ C → C ∈ B ⇒ C ∈ A))))) ] -- the power set
 ZF7 : [ ∀ll (λ A → ¬ (A ≐ ∅) ⇒ ∃x (λ B → B ∈ A ∧ ∀ll (λ C → ¬ (C ∈ A ∧ C ∈ B)))) ] -- foundation axiom
 ZF8 : (P : Pred) → [ ∀ll (λ A → ∃x (λ B → ∀ll (λ C → C ∈ B ⇔ C ∈ A ∧ P C)))] -- filter a set by a preicate 
 ZF9 : (F : ZFSet → ZFSet → Bool) → [ (∀ll (λ X → ∀ll (λ Y → ∀ll (λ Z → (F X Y) ∧ (F X Z) ⇒ Y ≐ Z)))) ⇒ ∀ll (λ A → ∃x (λ B → ∀ll (λ C → C ∈ B ⇔ ∃x (λ D → D ∈ A ∧ F D C)))) ]


