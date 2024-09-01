{-# OPTIONS --safe --erasure #-}
module Codata.SafeSized.List where

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (case_of_)

import Equality.Erased as Erased
open import Codata.SafeSized.Thunk using (■; delay)

data Colist (A : Set) (@0 i : ℕ) : Set where
  nil : Colist A i
  cons : ■ (λ j → A × Colist A j) i → Colist A i

unfold : {A S : Set} {@0 i : ℕ} → (S → Maybe (A × S)) → S → Colist A i
unfold f s = 
  case f s of λ{
    nothing → nil ;
    (just (a , s')) → cons (delay λ{ Erased.refl → a , unfold f s' })
  }

repeat : {A : Set} → (i : ℕ) → A → Colist A i
repeat 0 x = nil
repeat (suc n) x = cons (delay λ{ Erased.refl → x , repeat n x })

repeat-∞ : {A : Set} {@0 i : ℕ} → A → Colist A i
repeat-∞ x = cons (delay λ{ Erased.refl → x , repeat-∞ x })
