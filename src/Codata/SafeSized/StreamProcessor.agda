{- Adaptation of:

Altenkirch, T., & Danielsson, N. A. (2010, July).
Termination Checking in the Presence of Nested Inductive and Coinductive Types.
In PAR@ ITP (pp. 101-106).

-}

{-# OPTIONS --safe --erasure #-}
module Codata.SafeSized.StreamProcessor where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Product using (_×_; _,_)

open import Codata.SafeSized.Stream as Stream using (Stream; stream; Stream-∞; head-∞; tail-∞)
open import Codata.SafeSized.Thunk using (delay)
import Equality.Erased as Erased

data SP (A B : Set) (@0 i j : ℕ) : Set where
  get : {@0 i' : ℕ} → i Erased.≡ suc i' → (A → SP A B i' j) → SP A B i j
  put : ({@0 j' : ℕ} → j Erased.≡ suc j' → B × SP A B i j') → SP A B i j

⟦_⟧ : {A B : Set} {@0 i j : ℕ} → SP A B i j → Stream A i → Stream B j
⟦ get i≡suc-i' f ⟧ s = let head , tail = Stream.get s i≡suc-i' in ⟦ f head ⟧ tail
⟦ put rest ⟧ s = stream (delay λ j≡suc-j' → let b , rest' = rest j≡suc-j' in b , ⟦ rest' ⟧ s)

_>>>?_ : {A B C : Set} {@0 i j k : ℕ} → SP A B i j → SP B C j k → SP A C i k
get i≡suc-i' f >>>? g = get i≡suc-i' (λ a → f a >>>? g)
put f >>>? get j≡suc-i' g = let b , f' = f j≡suc-i' in f' >>>? g b
put f >>>? put g = put λ k≡suc-j' → let c , g' = g k≡suc-j' in c , {!!}

_>>>!_ : {A B C : Set} {@0 i j k : ℕ} → SP A B i j → SP B C j k → SP A C i k
f >>>! put rest = put {!!}
get i≡suc-i' f >>>! get j≡suc-i'' g = get i≡suc-i' (λ a → f a >>>! get j≡suc-i'' g)
put rest >>>! get j≡suc-i' g = {!!}

map : {A B : Set} {@0 i : ℕ} → (A → B) → SP A B (suc i) (suc i)
map f = get Erased.refl (λ a → put λ{ {j'} Erased.refl → f a , {!!} })

{-
data SP (A B : Set) (@0 i : ℕ) : Set where
  get : (A → SP A B i) → SP A B i
  put : B → ({@0 j : ℕ} → i Erased.≡ suc j → SP A B j) → SP A B i

⟦_⟧ : {A B : Set} {@0 i : ℕ} → SP A B i → Stream-∞ A → Stream B i
⟦ get f ⟧ s =
  let
    head = head-∞ s
    tail = tail-∞ s
  in
    ⟦ f head ⟧ tail
⟦ put b rest ⟧ s = stream (delay λ j≡suc-j' → b , ⟦ rest j≡suc-j' ⟧ s)

_>>>?_ : {A B C : Set} → ({@0 i : ℕ} → SP A B i) → ({@0 i : ℕ} → SP B C i) → ({@0 i : ℕ} → SP A C i)
_>>>?_ f g {i} with f {i}
... | get k = get (λ a → let ka = k a in {!!} >>>? g)
... | put b rest = {!!}

-}

module Reducer where
  data Reducer (A B : Set) : @0 ℕ → Set where
    done : B → Reducer A B zero
    more : {@0 i : ℕ} → (A → Reducer A B i) → Reducer A B (suc i)

  reduce : {A B : Set} {@0 i j : ℕ} → Reducer A B i → Stream A (i + j) → B × Stream A j
  reduce (done b) s = b , s
  reduce (more k) s = let head , tail = Stream.get s Erased.refl in reduce (k head) tail

  id : {A : Set} → Reducer A A 1
  id = more done

module Transformer where
  open Reducer using (Reducer; more; done; reduce)

  transform : {A B : Set} {@0 n : ℕ} → Reducer A B n → {@0 i : ℕ} → Stream A (i * n) → Stream B i
  transform {A} {B} {n} t s =
    stream (delay λ{ {j} Erased.refl →
      let b , s' = reduce {i = n} {j = j * n} t s in
      b , transform t s'
    })
