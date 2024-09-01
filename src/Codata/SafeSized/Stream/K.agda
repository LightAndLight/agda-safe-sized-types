{-# OPTIONS --safe --erasure --with-K #-}
module Codata.SafeSized.Stream.K where

open import Data.Nat using (ℕ; zero; suc; _*_)
open import Data.Product using (_×_; _,_)

open import Codata.SafeSized.Stream using (Stream; stream; get)
open import Codata.SafeSized.Thunk using (delay)
open import Equality.Erased using (_≡_; refl)

-- Sized Types by Lars Pareto (Equation 2.9)
merge : {A : Set} {@0 i : ℕ} → Stream A i → Stream A i → Stream A (i * 2)
merge {A} {i} s1 s2 =
  stream (delay λ{ {j1} prf1 →
    inner (pred-i*2 i j1 prf1)
  })
  where
    open import Data.Product using (Σ-syntax)

    @0 pred-i*2 : (i j : ℕ) → (i * 2) ≡ suc j → Σ[ k ∈ ℕ ] ((i ≡ suc k) × (j ≡ suc (k * 2)))
    pred-i*2 zero j ()
    pred-i*2 (suc i) j refl = i , refl , refl

    -- Requires UIP to pattern match on erased proof `i ≡ suc k`
    inner : {@0 j1 : ℕ} → @0 Σ[ k ∈ ℕ ] ((i ≡ suc k) × (j1 ≡ suc (k * 2))) → A × Stream A j1
    inner (k , refl , refl) =
      let h1 , t1 = get s1 in
      h1
      ,
      stream (delay λ{ {j2} refl →
        let h2 , t2 = get s2 in
        h2
        ,
        merge {i = k} t1 t2
      })
