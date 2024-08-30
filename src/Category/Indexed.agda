-- Category theory for indexed families of types

{-# OPTIONS --safe --erasure #-}
module Category.Indexed {I : Set} where

open import Data.Nat using (ℕ)

_⇒_ : (@0 I → Set) → (@0 I → Set) → (@0 I → Set)
_⇒_ A B i = A i → B i

infixr 50 _⇒_

∀[_] : (@0 I → Set) → Set
∀[ A ] = {@0 i : I} → A i

id : {A : @0 I → Set} → ∀[ A ⇒ A ]
id x = x

_∘_ : {A B C : @0 I → Set} → ∀[ B ⇒ C ] → ∀[ A ⇒ B ] → ∀[ A ⇒ C ]
_∘_ f g x = f (g x)

module _ (F : (@0 I → Set) → (@0 I → Set)) where
  record IFunctor : Set1 where
    field
      ifmap :
        {A B : @0 I → Set} →
        ∀[ A ⇒ B ] →
        ∀[ F A ⇒ F B ]

  record IFunctorEquiv {F-IFunctor : IFunctor} : Set1 where
    field
      Equiv :
        {A : @0 I → Set} →
        ({@0 i : I} → A i → A i → Set) →
        {@0 i : I} →
        F A i → F A i → Set
