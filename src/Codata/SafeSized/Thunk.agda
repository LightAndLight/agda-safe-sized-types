{-# OPTIONS --safe --erasure #-}
module Codata.SafeSized.Thunk where

open import Data.Nat using (ℕ; suc)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

open import Category.Indexed using (∀[_]; _⇒_; IFunctor)
import Equality.Erased as Erased

data ■ (A : @0 ℕ → Set) (@0 i : ℕ) : Set where
  delay : ({@0 j : ℕ} → i Erased.≡ suc j → A j) → ■ A i

undelay : {A : @0 ℕ → Set} {@0 i : ℕ} → ■ A i → {@0 j : ℕ} → i Erased.≡ suc j → A j
undelay (delay f) = f

force : {A : @0 ℕ → Set} {@0 i : ℕ} → ■ A (suc i) → A i
force (delay f) = f Erased.refl

map : {A B : @0 ℕ → Set} → ∀[ ■ (A ⇒ B) ⇒ (■ A ⇒ ■ B) ]
map f g = delay λ{ {j} Erased.refl → force f (force g) }

ifmap : {A B : @0 ℕ → Set} → ∀[ A ⇒ B ] → ∀[ ■ A ⇒ ■ B ]
ifmap f g = delay λ{ {j} Erased.refl → f (force g) }

■-IFunctor : IFunctor ■
■-IFunctor = record { ifmap = ifmap }

module LeftAdjoint where
  data ◆ (A : @0 ℕ → Set) (@0 j : ℕ) : Set where
    pack : {@0 i : ℕ} → i Erased.≡ suc j → A i → ◆ A j

  ■-intro :
    {Γ A : @0 ℕ → Set} →
    ({@0 i : ℕ} → ◆ Γ i → A i) →
    {@0 i : ℕ} → Γ i → ■ A i
  ■-intro f Γi = delay λ{ prf → f (pack prf Γi) }

  delay-undelay-id : {A : @0 ℕ → Set} {@0 i : ℕ} {x : ■ A i} → delay (undelay x) ≡ x
  delay-undelay-id {x = delay _} = refl

  ■-elim :
    {Γ A : @0 ℕ → Set} →
    ({@0 i : ℕ} → Γ i → ■ A i) →
    {@0 i : ℕ} → ◆ Γ i → A i
  ■-elim f (pack prf Γsuci) = undelay (f Γsuci) prf

  ■-intro-elim-id :
    {A Γ : @0 ℕ → Set} →
    (f : {@0 i : ℕ} → Γ i → ■ A i) →
    {@0 i : ℕ} → (x : Γ i) →
    ■-intro (■-elim f) x ≡ f x
  ■-intro-elim-id f x = 
    begin
      ■-intro (■-elim f) x
    ≡⟨⟩
      delay (λ{ prf → ■-elim f (pack prf x) })
    ≡⟨⟩
      delay (λ{ prf → ■-elim f (pack prf x) })
    ≡⟨⟩
      delay (λ{ prf → undelay (f x) prf })
    ≡⟨⟩
      delay (undelay (f x))
    ≡⟨ delay-undelay-id ⟩
      f x
    ∎
    where
      open Eq.≡-Reasoning

  ■-elim-intro-id :
    {A Γ : @0 ℕ → Set} →
    (f : {@0 i : ℕ} → ◆ Γ i → A i) →
    {@0 i : ℕ} → (x : ◆ Γ i) →
    ■-elim (■-intro f) x ≡ f x
  ■-elim-intro-id f (pack prf Γsuci) = 
    begin
      ■-elim (■-intro f) (pack prf Γsuci)
    ≡⟨⟩
      undelay (■-intro f Γsuci) prf
    ≡⟨⟩
      undelay (delay λ{ prf → f (pack prf Γsuci) }) prf
    ≡⟨⟩
      f (pack prf Γsuci)
    ∎
    where
      open Eq.≡-Reasoning
