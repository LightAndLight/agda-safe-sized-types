{-# OPTIONS --safe --erasure #-}
module Codata.SafeSized.Stream where

open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

open import Codata.SafeSized.Thunk using (■; delay; undelay)
import Equality.Erased as Erased

data Stream (A : Set) (@0 i : ℕ) : Set where
  stream :
    ■ (λ j → A × Stream A j) i →
    Stream A i

cons : {A : Set} {@0 i : ℕ} → A → ({@0 j : ℕ} → i Erased.≡ suc j → Stream A j) → Stream A i
cons h t = stream (delay λ prf → h , t prf)

guard : {A : Set} {@0 i : ℕ} → ({@0 j : ℕ} → i Erased.≡ suc j → A × Stream A j) → Stream A i
guard f = stream (delay f)

unstream : {A : Set} {@0 i : ℕ} → Stream A i → ■ (λ j → A × Stream A j) i
unstream (stream f) = f

get' : {A : Set} {@0 i : ℕ} → Stream A i → {@0 j : ℕ} → i Erased.≡ suc j → A × Stream A j
get' s = undelay (unstream s)

get : {A : Set} {@0 i : ℕ} → Stream A (suc i) → A × Stream A i
get s = get' s Erased.refl

head' : {A : Set} {@0 i : ℕ} → Stream A i → {@0 j : ℕ} → i Erased.≡ suc j → A
head' s prf = proj₁ (get' s prf)

head : {A : Set} {@0 i : ℕ} → Stream A (suc i) → A
head s = head' s Erased.refl

tail' : {A : Set} {@0 i : ℕ} → Stream A i → {@0 j : ℕ} → i Erased.≡ suc j → Stream A j
tail' s prf = proj₂ (get' s prf)

tail : {A : Set} {@0 i : ℕ} → Stream A (suc i) → Stream A i
tail s = tail' s Erased.refl

unfold : {A S : Set} {@0 i : ℕ} → (S → A × S) → S → Stream A i
unfold f s =
  let a , s' = f s in
  cons a λ{ {j} Erased.refl →
    unfold {i = j} f s'
  }

repeat : {A : Set} {@0 i : ℕ} → A → Stream A i
repeat = unfold λ x → x , x

take : {A : Set} {@0 i : ℕ} → (n : ℕ) → Stream A (n + i) → Vec A n × Stream A i
take zero s = [] , s
take (suc n) s with take n (tail s)
... | xs , s' = head s ∷ xs , s'

map : {A B : Set} {@0 i : ℕ} → (A → B) → Stream A i → Stream B i
map f s =
  guard λ{ Erased.refl →
    let h , t = get s in
    f h , map f t
  }

zipWith : {A B C : Set} {@0 i : ℕ} → (A → B → C) → Stream A i → Stream B i → Stream C i
zipWith f s1 s2 =
  guard λ{ Erased.refl →
    let a , s1' = get s1 in
    let b , s2' = get s2 in
    f a b , zipWith f s1' s2'
  }

weaken : {A : Set} {@0 i : ℕ} → Stream A (suc i) → Stream A i
weaken s =
  guard λ{ {j} Erased.refl →
    let h , t = get s in
    h , weaken {i = j} t
  }

data Stream-∞ (A : Set) : Set where
  stream-∞ : ({@0 i : ℕ} → Stream A i) → Stream-∞ A

to-∞ : {A : Set} → ({@0 i : ℕ} → Stream A i) → Stream-∞ A
to-∞ = stream-∞

from-∞ : {A : Set} → Stream-∞ A → ({@0 i : ℕ} → Stream A i)
from-∞ (stream-∞ f) = f

head-∞ : {A : Set} → Stream-∞ A → A
head-∞ s = head (from-∞ s {i = 1})

tail-∞ : {A : Set} → Stream-∞ A → Stream-∞ A
tail-∞ s = to-∞ (tail (from-∞ s))

merge-∞ : {A : Set} → Stream-∞ A → Stream-∞ A → Stream-∞ A
merge-∞ s1 s2 = stream-∞ (unfold (λ (a , b) → head-∞ a , (b , tail-∞ a)) (s1 , s2))

module _ {A : Set} where
  data Stream-All {@0 i : ℕ} (R : A → A → Set) (s s' : Stream A i) : Set where
    Stream-all :
      ({@0 j : ℕ} → (prf : i Erased.≡ suc j) →
        R (head' s prf) (head' s' prf)
        ×
        Stream-All R (tail' s {j} prf) (tail' s' {j} prf)
      ) →
      Stream-All R s s'

  -- Intuition from <https://www.joachim-breitner.de/blog/727-How_is_coinduction_the_dual_of_induction_>
  Stream-All-unfold :
    {Q : {@0 i : ℕ} → Stream A i → Stream A i → Set} {R : A → A → Set} →
    ({@0 i : ℕ} {a b : Stream A (suc i)} → Q a b → R (head a) (head b) × Q (tail a) (tail b)) →
    {@0 i : ℕ} {a b : Stream A i} →
    Q a b → Stream-All R a b
  Stream-All-unfold {Q} {R} f s =
    Stream-all λ{ Erased.refl →
      let h , t = f s in
      h , Stream-All-unfold {Q} {R} f t
    }

  _Stream-≡_ : {@0 i : ℕ} → (s s' : Stream A i) → Set
  _Stream-≡_ = Stream-All _≡_

  Stream-≡-refl : {@0 i : ℕ} {a : Stream A i} → a Stream-≡ a
  Stream-≡-refl {i} {a} =
    Stream-all
      (λ{ {j} Erased.refl →
        refl
        ,
        Stream-≡-refl {j} {a = tail' a Erased.refl}
      })

  Stream-≡-trans :
    {@0 i : ℕ} {a b c : Stream A i} →
    a Stream-≡ b →
    b Stream-≡ c →
    a Stream-≡ c
  Stream-≡-trans {A} {i} (Stream-all prf1) (Stream-all prf2) =
    Stream-all
      (λ{ {j} Erased.refl →
        let
          head≡head'-1 = proj₁ (prf1 {j} Erased.refl)
          head≡head'-2 = proj₁ (prf2 {j} Erased.refl)
          tail≡tail'-1 = proj₂ (prf1 {j} Erased.refl)
          tail≡tail'-2 = proj₂ (prf2 {j} Erased.refl)
        in
        Eq.trans head≡head'-1 head≡head'-2
        ,
        Stream-≡-trans tail≡tail'-1 tail≡tail'-2
      })

  Stream-≡-sym :
    {@0 i : ℕ} {a b : Stream A i} →
    a Stream-≡ b →
    b Stream-≡ a
  Stream-≡-sym (Stream-all prf) =
    Stream-all
      (λ{ {j} Erased.refl →
        let
          head≡head' = proj₁ (prf {j} Erased.refl)
          tail≡tail' = proj₂ (prf {j} Erased.refl)
        in
        Eq.sym head≡head'
        ,
        Stream-≡-sym tail≡tail'
      })

  Stream-≡-cong-tail :
    {@0 i : ℕ} {a b : Stream A i} →
    a Stream-≡ b →
    {j : ℕ} → (prf : i Erased.≡ suc j) → tail' a prf Stream-≡ tail' b prf
  Stream-≡-cong-tail (Stream-all prf) {j} prf' = proj₂ (prf {j} prf')

  module Stream-≡-Reasoning {@0 i : ℕ} where
    open import Relation.Binary.Reasoning.Syntax using (forward; backward)
    open import Function using (id)

    module Stream-≡-syntax where
      infixr 2 step-≡-⟩  step-≡-∣ step-≡-⟨
      step-≡-⟩ = forward (_Stream-≡_ {i}) _Stream-≡_ Stream-≡-trans

      step-≡-∣ : ∀ x {y} → _Stream-≡_ {i} x y → x Stream-≡ y
      step-≡-∣ x xRy = xRy

      step-≡-⟨ = backward (_Stream-≡_ {i}) _Stream-≡_ Stream-≡-trans Stream-≡-sym

      syntax step-≡-⟩ x yRz x≡y = x ≡⟨ x≡y ⟩ yRz
      syntax step-≡-∣ x xRy     = x ≡⟨⟩ xRy
      syntax step-≡-⟨ x yRz y≡x = x ≡⟨ y≡x ⟨ yRz

    open Relation.Binary.Reasoning.Syntax.begin-syntax {A = Stream A i} _Stream-≡_ id public
    open Stream-≡-syntax public
    open Relation.Binary.Reasoning.Syntax.end-syntax {A = Stream A i} _Stream-≡_ Stream-≡-refl public

from-to-∞ : {A : Set} → (s : {@0 i : ℕ} → Stream A i) → {@0 i : ℕ} → from-∞ (to-∞ s) {i} Stream-≡ s {i}
from-to-∞ s = Stream-≡-refl

to-from-∞ : {A : Set} → (s : Stream-∞ A) → to-∞ (from-∞ s) ≡ s
to-from-∞ (stream-∞ s) = refl

module Example where
  {-
  Hughes, J., Pareto, L., & Sabry, A. (1996, January).
  Proving the correctness of reactive systems using sized types.
  In Proceedings of the 23rd ACM SIGPLAN-SIGACT symposium on Principles of programming languages (pp. 410-423).
  -}

  open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _/_)

  fib : {@0 i : ℕ} → Stream ℕ i
  fib =
    cons 0 λ{ Erased.refl →
      cons 1 λ{ Erased.refl →
        zipWith _+_ fib (tail fib)
      }
    }

  avg : ℕ → ℕ → ℕ
  avg m n = (m + n) / 2

  fil : {@0 i : ℕ} → Stream ℕ (i * 2) → Stream ℕ i
  fil s =
    guard λ{ {j} Erased.refl →
      let x1 , s' = get' s {j = suc (j * 2)} Erased.refl in
      let x2 , s'' = get' s' {j = j * 2} Erased.refl in
      avg x1 x2 , fil s''
    }
