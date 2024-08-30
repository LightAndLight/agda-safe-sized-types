-- Coalgebraic semantics for sized coinductive streams

{-# OPTIONS --safe --erasure #-}
module Codata.SafeSized.Stream.Coalgebra where

open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

open import Category.Indexed using (∀[_]; _⇒_; IFunctor; IFunctorEquiv)
open import Codata.SafeSized.Thunk using (■; delay; undelay)
import Equality.Erased as Erased

data StreamF (A : Set) (X : @0 ℕ → Set) (@0 i : ℕ) : Set where
  streamF : ■ (λ j → A × X j) i → StreamF A X i

unstreamF : {A : Set} {X : @0 ℕ → Set} {@0 i : ℕ} → StreamF A X i → ■ (λ j → A × X j) i
unstreamF (streamF f) = f

getF : {A : Set} {X : @0 ℕ → Set} {@0 i : ℕ} → StreamF A X i → {@0 j : ℕ} → i Erased.≡ suc j → A × X j
getF s = undelay (unstreamF s)

get-headF : {A : Set} {X : @0 ℕ → Set} {@0 i : ℕ} → StreamF A X i → {@0 j : ℕ} → i Erased.≡ suc j → A
get-headF s prf = proj₁ (getF s prf)

get-tailF : {A : Set} {X : @0 ℕ → Set} {@0 i : ℕ} → StreamF A X i → {@0 j : ℕ} → i Erased.≡ suc j → X j
get-tailF s prf = proj₂ (getF s prf)

StreamF-map :
  {A : Set} {X Y : @0 ℕ → Set} {@0 i : ℕ} →
  ({@0 j : ℕ} → i Erased.≡ suc j → X j → Y j) →
  StreamF A X i →
  StreamF A Y i
StreamF-map {i = i} f s =
  streamF (delay λ{ {j} Erased.refl →
    let h , t = getF s Erased.refl in
    h , f Erased.refl t
  })

StreamF-ifmap : {A : Set} {X Y : @0 ℕ → Set} → ∀[ X ⇒ Y ] → ∀[ StreamF A X ⇒ StreamF A Y ]
StreamF-ifmap {X = X} f {i} s = StreamF-map {X = X} {i = i} (λ{ {j} Erased.refl → f {j} }) s

StreamF-IFunctor : {A : Set} → IFunctor (StreamF A)
StreamF-IFunctor {A} =
  record {
    ifmap = StreamF-ifmap
  }

module _ {A : Set} {X : @0 ℕ → Set} {X-Equiv : {@0 i : ℕ} → X i → X i → Set} where
  data _StreamF-≡_ {@0 i : ℕ} (s s' : StreamF A X i) : Set where
    StreamF-refl :
      (
        {@0 j : ℕ} →
        (prf : i Erased.≡ suc j) →
        get-headF s prf ≡ get-headF s' prf ×
        X-Equiv (get-tailF s {j} prf) (get-tailF s' {j} prf)
      ) →
      s StreamF-≡ s'

  StreamF-≡-cong-head :
    {@0 i : ℕ} {a b : StreamF A X i} →
    a StreamF-≡ b →
    {@0 j : ℕ} →
    (prf : i Erased.≡ suc j) →
    get-headF a prf ≡ get-headF b prf
  StreamF-≡-cong-head (StreamF-refl f) prf = proj₁ (f prf)

  StreamF-≡-cong-tail :
    {@0 i : ℕ} {a b : StreamF A X i} →
    a StreamF-≡ b →
    {@0 j : ℕ} →
    (prf : i Erased.≡ suc j) →
    X-Equiv (get-tailF a prf) (get-tailF b prf)
  StreamF-≡-cong-tail (StreamF-refl f) prf = proj₂ (f prf)

  StreamF-≡-trans :
    {@0 i : ℕ} →
    ({a b c : X i} → X-Equiv a b → X-Equiv b c → X-Equiv a c) →
    {a b c : StreamF A X (suc i)} →
    a StreamF-≡ b →
    b StreamF-≡ c →
    a StreamF-≡ c
  StreamF-≡-trans X-Equiv-trans s1 s2 = 
    StreamF-refl λ{ {j} Erased.refl →
      let h1 = StreamF-≡-cong-head s1 Erased.refl in
      let h2 = StreamF-≡-cong-head s2 Erased.refl in
      let t1 = StreamF-≡-cong-tail s1 Erased.refl in
      let t2 = StreamF-≡-cong-tail s2 Erased.refl in
      Eq.trans h1 h2
      ,
      X-Equiv-trans t1 t2
    }

StreamF-IFunctorEquiv : {A : Set} → IFunctorEquiv (StreamF A) {F-IFunctor = StreamF-IFunctor}
StreamF-IFunctorEquiv =
  record {
    Equiv = λ {A} A-Equiv → _StreamF-≡_ {X = A} {X-Equiv = A-Equiv}
  }

open import Codata.SafeSized.Stream using (Stream; unstream; get-head; get-tail)
open Stream

stream-wrap : {A : Set} {@0 i : ℕ} → StreamF A (Stream A) i → Stream A i
stream-wrap s = stream (unstreamF s)

stream-unwrap : {A : Set} {@0 i : ℕ} → Stream A i → StreamF A (Stream A) i
stream-unwrap s = streamF (unstream s)

stream-unfold : {A : Set} {S : @0 ℕ → Set} → ∀[ S ⇒ StreamF A S ] → ∀[ S ⇒ Stream A ]
stream-unfold {A} {S} f {i} s =
  stream-wrap (StreamF-map (λ{ {j} Erased.refl → stream-unfold f {j}}) (f s))

module _ {A : Set} where
  open import Data.Product using (_,_)

  open import Coalgebra.Indexed using (ICoalgebra; ICoalgebraArrow; ITerminal)
  open import Codata.SafeSized.Stream using (Stream-All; _Stream-≡_)
  open Stream-All

  Stream-coalgebra :
    ICoalgebra
      (StreamF A)
      {F-IFunctor = StreamF-IFunctor}
      {F-IFunctorEquiv = StreamF-IFunctorEquiv}
  Stream-coalgebra =
    record
    { Carrier = Stream A
    ; coalgebra = stream-unwrap
    ; Equiv = _Stream-≡_
    }

  Stream-coalgebra-terminal : ITerminal (StreamF A) Stream-coalgebra
  Stream-coalgebra-terminal x = term , f≡g
    where
      X : @0 ℕ → Set
      X = ICoalgebra.Carrier x

      step-X : ∀[ X ⇒ StreamF A X ]
      step-X = ICoalgebra.apply x

      to-stream : ∀[ X ⇒ Stream A ]
      to-stream s = stream-unfold step-X s

      term : ICoalgebraArrow (StreamF A) x Stream-coalgebra
      term =
        record {
          f = to-stream;
          correct = to-stream-correct
        }
        where
          open IFunctor StreamF-IFunctor

          to-stream-correct :
            {@0 i : ℕ} →
            (arg : X i) →
            _StreamF-≡_ {X-Equiv = _Stream-≡_}
              (ifmap to-stream (step-X arg))
              (ICoalgebra.apply Stream-coalgebra (to-stream arg))
          to-stream-correct {i} arg =
            StreamF-refl λ{ {j} Erased.refl →
              refl
              ,
              let open Codata.SafeSized.Stream.Stream-≡-Reasoning in
              begin
                get-tailF (ifmap to-stream (step-X arg)) Erased.refl
              ≡⟨⟩ -- inline definition of `to-stream`
                get-tailF (ifmap (stream-unfold step-X) (step-X arg)) Erased.refl
              ≡⟨⟩ -- anti-inline definition of `stream-unfold`
                get-tail (stream-unfold step-X arg) Erased.refl
              ≡⟨⟩ -- anti-inline definition of `to-stream`
                get-tail (to-stream arg) Erased.refl
              ≡⟨⟩ -- `get-tail ≡ get-tailF ∘ stream-unwrap`
                get-tailF (stream-unwrap (to-stream arg)) Erased.refl
              ≡⟨⟩ -- anti-inline definition of `ICoalgebra.apply Stream-coalgebra`
                get-tailF (ICoalgebra.apply Stream-coalgebra (to-stream arg)) Erased.refl
              ∎
            }

      f≡g :
        (g : ICoalgebraArrow (StreamF A) x Stream-coalgebra) →
        (let to-stream' = ICoalgebraArrow.f g) →
        {@0 i : ℕ} →
        (arg : X i) →
        to-stream arg Stream-≡ to-stream' arg
      f≡g g arg =
        let
          to-stream' : ∀[ X ⇒ Stream A ]
          to-stream' = ICoalgebraArrow.f g

          to-stream'-correct :
            {@0 i : ℕ} →
            (arg : X i) →
            _StreamF-≡_
              {X-Equiv = _Stream-≡_}
              (StreamF-ifmap to-stream' (step-X arg))
              (stream-unwrap (to-stream' arg))
          to-stream'-correct = ICoalgebraArrow.correct g

        in
        Stream-all λ{ {j} Erased.refl →
          (let open Eq.≡-Reasoning in
          begin
            get-head (to-stream arg) Erased.refl
          ≡⟨⟩ -- inline definition of `to-stream`
            get-head (stream-unfold step-X arg) Erased.refl
          ≡⟨⟩ -- `get-head ∘ stream-unfold f ≡ get-headF ∘ f`
            get-headF (step-X arg) Erased.refl
          ≡⟨⟩ -- `get-headF ≡ get-headF ∘ Stream-ifmap f`
            get-headF (StreamF-ifmap to-stream' (step-X arg)) Erased.refl
          ≡⟨ StreamF-≡-cong-head (to-stream'-correct arg) Erased.refl ⟩
            get-headF (stream-unwrap (to-stream' arg)) Erased.refl
          ≡⟨⟩ -- `get-head ≡ get-headF ∘ stream-unwrap`
            get-head (to-stream' arg) Erased.refl
          ∎)
          ,
          let open Codata.SafeSized.Stream.Stream-≡-Reasoning in
          begin
            get-tail (to-stream arg) Erased.refl
          ≡⟨⟩ -- inline definition of `to-stream`
            get-tail (stream-unfold step-X arg) Erased.refl
          ≡⟨⟩ -- `get-tail ∘ stream-unfold f ≡ stream-unfold f ∘ get-tailF ∘ f`
            stream-unfold step-X (get-tailF (step-X arg) Erased.refl)
          ≡⟨⟩ -- anti-inline definition of `to-stream`
            to-stream (get-tailF (step-X arg) Erased.refl)
          ≡⟨ f≡g g (get-tailF (step-X arg) Erased.refl) ⟩
            to-stream' (get-tailF (step-X arg) Erased.refl)
          ≡⟨⟩ -- f ∘ get-tailF ≡ get-tailF ∘ StreamF-ifmap f
            get-tailF (StreamF-ifmap to-stream' (step-X arg)) Erased.refl
          ≡⟨ StreamF-≡-cong-tail (to-stream'-correct arg) Erased.refl ⟩
            get-tailF (stream-unwrap (to-stream' arg)) Erased.refl
          ≡⟨⟩ -- `get-tail ≡ get-tailF ∘ stream-unwrap`
            get-tail (to-stream' arg) Erased.refl
          ∎
        }


