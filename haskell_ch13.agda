module haskell_ch13 where

-- for "Programming Haskell" chapter 13.

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.List hiding (replicate)

data Nat : Set where
  Zero : Nat
  Succ  : Nat → Nat
 
add : Nat → Nat → Nat
add Zero    m = m
add (Succ n) m = Succ (add n m)

n+zero≡n : {n : Nat} → add n Zero ≡ n
n+zero≡n {Zero}   = refl
n+zero≡n {Succ x} = begin
      add (Succ x) Zero
    ≡⟨ refl ⟩
      Succ (add x Zero)
    ≡⟨ cong (λ e → Succ e) for-x ⟩
      Succ x
    ∎
  where for-x : add x Zero ≡ x
        for-x = n+zero≡n {x}

assoc-+ : {x y z : Nat} → add x (add y z) ≡ add (add x y) z
assoc-+ {Zero} {y} {z}   = begin
      add Zero (add y z)
    ≡⟨ refl ⟩
      add y z
    ≡⟨ sym refl ⟩
      add (add Zero y) z
    ∎
assoc-+ {Succ x} {y} {z} = begin
      add (Succ x) (add y z)
    ≡⟨ refl ⟩
      Succ (add x (add y z))
    ≡⟨ cong (λ e → Succ e) (assoc-+ {x}) ⟩
      Succ (add (add x y) z)
    ≡⟨ sym refl ⟩
      add (Succ (add x y)) z
    ≡⟨ sym refl ⟩
      add (add (Succ x) y) z
    ∎

replicate : ∀{l}{A : Set l} → Nat → A → List A
replicate Zero     _ = []
replicate (Succ n) c = c ∷ (replicate n c)

