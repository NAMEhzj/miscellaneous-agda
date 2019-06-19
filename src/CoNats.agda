open import Agda.Primitive

module CoNats where

data Maybe {l} (a : Set l) : Set l where
     Nothing : Maybe a
     Just : a → Maybe a

fmap : {l k : Level} → {a : Set l} → {b : Set k} → (a  → b) → Maybe a → Maybe b
fmap f Nothing = Nothing
fmap f (Just x) = Just (f x)

record ℕ∞ : Set where
  coinductive
  field
    pred : Maybe ℕ∞

open ℕ∞

coZero : ℕ∞
pred coZero = Nothing

coOne : ℕ∞
pred coOne = Just coZero

coPlus : ℕ∞ → ℕ∞ → ℕ∞
pred (coPlus n m) with pred n
pred (coPlus n m) | Nothing   = Just m
pred (coPlus n m) | (Just n') = Just (coPlus n' m)

{-
coTimes : ℕ∞ → ℕ∞ → ℕ∞
pred (coTimes n m) with pred n
pred (coTimes n m) | Nothing = Nothing
pred (coTimes n m) | (Just n') with pred m
pred (coTimes n m) | (Just n') | Nothing   = Nothing
pred (coTimes n m) | (Just n') | (Just m') = Just (coPlus (coTimes n' m) m')
-}


coTimesPlus : ℕ∞ → ℕ∞ → ℕ∞ → ℕ∞ 
pred (coTimesPlus n m k) with pred n
pred (coTimesPlus n m k) | Nothing = Just k
pred (coTimesPlus n m k) | (Just n') with pred m
pred (coTimesPlus n m k) | (Just n') | Nothing = Just k
pred (coTimesPlus n m k) | (Just n') | (Just m') = Just (coTimesPlus n' m' (coPlus m' k))

coTimes : ℕ∞ → ℕ∞ → ℕ∞
coTimes n m = coTimesPlus n m coZero



{- powHelper gets a, q, n and c as input, and computes 
  a*Sum[k = 0 to n](q^k) + c
 if a = a' + 1, q = q' + 1, n = n' + 1 that means that
 powHelper a q n c 
 = a*Sum[k = 0 to n](q^k) + c = a**Sum[k = 0 to n'](q^k) + a*q^n + c
 = a*Sum[k = 0 to n'](q^k) + a*(q^n - 1) + (a' + 1)  + c
 = a*Sum[k = 0 to n'](q^k) + a*(q - 1)Sum[k = 0 to n'](q^k) + (a' + c) + 1
 = (a*q)*Sum[k = 0 to n'](q^k) + (a' + c) + 1
 = (powHelper (a * q) q n' (a' + c)) + 1 
 and that means the predecessor of the result can be expressed with 1 recursive call at the outside -}

powHelper : ℕ∞ → ℕ∞ → ℕ∞ → ℕ∞ → ℕ∞
pred (powHelper a q n c) with pred a
pred (powHelper a q n c) | Nothing = pred c
pred (powHelper a q n c) | (Just a') with pred n
pred (powHelper a q n c) | (Just a') | Nothing = Just (coPlus a' c)
pred (powHelper a q n c) | (Just a') | (Just n') = Just (powHelper (coTimes a q) q n' (coPlus a' c))


coPow : ℕ∞ → ℕ∞ → ℕ∞
pred (coPow a b) with pred b
pred (coPow a b) | Nothing = Just coOne
pred (coPow a b) | (Just b') with pred a
pred (coPow a b) | (Just b') | Nothing = Just coZero 
pred (coPow a b) | (Just b') | (Just a') = Just (powHelper a' a b' coZero)
