module t_p_p_16 where

open import Data.Nat
open import Data.Fin hiding (_<_)
open import Data.Vec
open import Data.Product
open import Data.Sum
open import Data.String
open import Data.Maybe.Base

open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥ ; ⊥-elim)

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

record kvec {l} (A : Set l) : (Set l) where
  field
    k : ℕ
    vec : Vec A k

-- ========================================
--   Lemma
-- ========================================
-- Remove nth from vector-type
remove-nth : ∀{a n} {A : Set a} → Fin (suc n) → Vec A (suc n) → Vec A n
remove-nth zero    (x ∷ xs) = xs
remove-nth {n = zero} (suc ())
remove-nth {n = suc m} (suc n) (x ∷ xs) = x ∷ (remove-nth {n = m} n xs)

-- Delete j-th from kvec-type
delete : ∀{l} {A : Set l} → (kv : kvec A) → (j : Fin (kvec.k kv)) → kvec A
delete (record {k = zero; vec = vec}) ()
delete {l} (record {k = suc k; vec = vec}) j =
                 record { k = k
                        ; vec = remove-nth {l} j vec
                        }

suc-deleted-lemma : ∀{l} {A : Set l} → (x : kvec A) → (j : Fin (kvec.k x)) →
                     suc (kvec.k (delete x j)) ≡ kvec.k x
suc-deleted-lemma (record {k = zero; vec = vec}) ()
suc-deleted-lemma (record {k = suc k; vec = vec}) j = refl

contra : ∀{l n}{P : Set l} → {R : Set n} → P → ¬ P → R
contra p ¬p = ⊥-elim (¬p p)

suc≢zero : {n : ℕ} → {a : Fin n} → Data.Fin.suc a ≢ zero
suc≢zero ()

sym≢ : {A : Set}{x y : A} → x ≢ y → y ≢ x
sym≢ neq eq = neq (sym eq)

≡-suc : {n : ℕ} → {c d : Fin n} → c ≡ d → Data.Fin.suc c ≡ suc d
≡-suc {c = c} {d = d} eq = begin
          suc c
         ≡⟨ cong (λ x → suc x) eq ⟩
          suc d
         ∎

suc-≡ : {n : ℕ} → {c d : Fin n} → Data.Fin.suc c ≡ suc d → c ≡ d --pred
suc-≡ refl = refl

suc-≢ : {n : ℕ} → {a b : Fin n} → Data.Fin.suc a ≢ suc b → a ≢ b
suc-≢ neq p = contra (≡-suc p) neq

≢-suc : {n : ℕ} → {a b : Fin n} → a ≢ b → Data.Fin.suc a ≢ suc b
≢-suc neq p = contra (suc-≡ p) neq

-- ========================================
--   remove-lst
-- ========================================
remove-lst : ∀{l} {A : Set l} → {m : ℕ} → (lst : Vec (kvec A) m) →
             (i : Fin m) → (j : Fin (kvec.k (lookup i lst))) → Vec (kvec A) m
remove-lst [] ()
remove-lst (x ∷ xs) zero j = (delete x j) ∷ xs
remove-lst (x ∷ xs) (suc i) j = x ∷ (remove-lst xs i j)

-- length-proof for remove-lst
private
  ith-pf : ∀{l} {A : Set l} → {m : ℕ} → (lst : Vec (kvec A) m) →
           (i : Fin m) → (j : Fin (kvec.k (lookup i lst))) →
           suc (kvec.k (lookup i (remove-lst lst i j))) ≡ kvec.k (lookup i lst)
  ith-pf {m = zero} [] ()
  ith-pf {m = suc m} (x ∷ xs) zero j = suc-deleted-lemma x j
  ith-pf {m = suc m} (x ∷ xs) (suc i) j = ith-pf {m = m} xs i j

  others-pf : ∀{l} {A : Set l} → {m : ℕ} → (lst : Vec (kvec A) m) →
                    (n : Fin m) → (i : Fin m) → (j : Fin (kvec.k (lookup i lst))) →
                    n ≢ i → kvec.k (lookup n (remove-lst lst i j)) ≡ kvec.k (lookup n lst)
  others-pf {m = zero} lst ()
  others-pf {m = suc m} (x ∷ xs) zero zero j n≢i = contra refl n≢i
  others-pf {m = suc m} (x ∷ xs) zero (suc i) j n≢i = refl
  others-pf {m = suc m} (x ∷ xs) (suc n) zero j n≢i = refl
  others-pf {m = suc m} (x ∷ xs) (suc n) (suc i) j n≢i = others-pf xs n i j (suc-≢ n≢i)

length-proof1 : ∀{a} {A : Set a} → {m : ℕ} → (lst : Vec (kvec A) m) →
                (i : Fin m) → (j : Fin (kvec.k (lookup i lst))) →
                (n : Fin m) →
                (n ≡ i → suc (kvec.k (lookup n (remove-lst lst i j))) ≡ kvec.k (lookup n lst)) ×
                (n ≢ i → kvec.k (lookup n (remove-lst lst i j)) ≡ kvec.k (lookup n lst))
length-proof1 {m = m} lst i j n = (λ n≡i → begin
                    suc (kvec.k (lookup n (removed-lst)))
                   ≡⟨ cong (λ x → suc (kvec.k (lookup x (removed-lst)))) n≡i ⟩
                    suc (kvec.k (lookup i removed-lst))
                   ≡⟨ ith-pf lst i j ⟩
                    kvec.k (lookup i lst)
                   ≡⟨ cong (λ x → kvec.k (lookup x lst)) (sym n≡i) ⟩
                    kvec.k (lookup n lst)
                   ∎) , (λ n≢i → begin
                    kvec.k (lookup n (remove-lst lst i j))
                   ≡⟨ others-pf {m = m} lst n i j n≢i ⟩
                    kvec.k (lookup n lst)
                   ∎)
  where removed-lst = remove-lst lst i j

-- ========================================
--   remove-lst-with-proof
-- ========================================
record remove-lst-with-proof {l m} (A : Set l) (lst : Vec (kvec A) m)
       (i : Fin m) (j : Fin (kvec.k (lookup i lst))) : (Set l) where
  field
    y : Vec (kvec A) m
    equality-proof : (n : Fin m) →
                     (n ≡ i → lookup n y ≡ delete (lookup i lst) j) ×
                     (n ≢ i → lookup n y ≡ lookup n lst)
    length-proof : (n : Fin m) →
                   (n ≡ i → suc (kvec.k (lookup n y)) ≡ kvec.k (lookup n lst)) ×
                   (n ≢ i → kvec.k (lookup n y) ≡ kvec.k (lookup n lst))
    unique-proof : (y′ : Vec (kvec A) m) →
                   ((n : Fin m) →
                    (n ≡ i → lookup n y′ ≡ delete (lookup i lst) j) ×
                    (n ≢ i → lookup n y′ ≡ lookup n lst)) →
                   ((n : Fin m) →
                    (n ≡ i → suc (kvec.k (lookup n y′)) ≡ kvec.k (lookup n lst)) ×
                    (n ≢ i → kvec.k (lookup n y′) ≡ kvec.k (lookup n lst))) →
                   y ≡ y′

-- Any nth element of list1 and list2 are equal, then list1 ≡ list2
vec-eq-main : ∀{l}{A : Set l} → {n : ℕ} → {l1 l2 : Vec A n} →
              ((m : Fin n) → lookup m l1 ≡ lookup m l2) → l1 ≡ l2
vec-eq-main {n = zero} {l1 = []} {l2 = []} fun = refl
vec-eq-main {n = suc n} {l1 = x ∷ xs} {l2 = y ∷ ys} fun = vec-eq (fun zero) xs≡ys
  where fun2 : (a : Fin n) → lookup a xs ≡ lookup a ys
        fun2 a = begin
             lookup a xs
            ≡⟨ sym refl ⟩
             lookup (suc a) (x ∷ xs)
            ≡⟨ p ⟩
             lookup (suc a) (y ∷ ys)
            ≡⟨ refl ⟩
             lookup a ys
            ∎
          where p : lookup (suc a) (x ∷ xs) ≡ lookup (suc a) (y ∷ ys)
                p = fun (suc a)
        xs≡ys : xs ≡ ys
        xs≡ys = vec-eq-main {n = n} {l1 = xs} {l2 = ys} fun2
        vec-eq : ∀{l}{A : Set l} → {a b : A} → {n : ℕ} → {l1 l2 : Vec A n} →
                 (a ≡ b) → (l1 ≡ l2) → (a ∷ l1 ≡ b ∷ l2)
        vec-eq {_}{_} {a}{b} {_} {l1} {l2} eq1 eq2 = begin
              a ∷ l1
            ≡⟨ cong (λ x → a ∷ x) eq2 ⟩
              a ∷ l2
            ≡⟨ cong (λ x → x ∷ l2) eq1 ⟩
              b ∷ l2
            ∎

-- Returns a ≡ b, otherwise a ≢ b
_≡f_ : {n : ℕ} → (a b : Fin n) → a ≡ b ⊎ a ≢ b
_≡f_ {zero} ()
_≡f_ zero zero = inj₁ refl
_≡f_ (suc a) zero = inj₂ (suc≢zero{a = a})
_≡f_ zero (suc b) = inj₂ (sym≢ (suc≢zero{a = b}))
_≡f_ (suc a) (suc b) with a ≡f b
... | inj₁ eq = inj₁ (≡-suc eq)
... | inj₂ neq = inj₂ (≢-suc neq)

≡-trans : ∀{l}{A : Set l} → {x y z : A} → x ≡ y → y ≡ z → x ≡ z
≡-trans {_}{_} {x} {y} {z} x≡y y≡z = begin
          x
        ≡⟨ x≡y ⟩
          y
        ≡⟨ y≡z ⟩
          z
        ∎

anyN-trans≡ : ∀{l}{A : Set l} → {m : ℕ} → (lst y y′ : Vec (kvec A) m) →
        {i : Fin m} → {j : Fin (kvec.k (lookup i lst))} →
        ((n : Fin m) →
                 (n ≡ i → lookup n y ≡ delete (lookup i lst) j) ×
                 (n ≢ i → lookup n y ≡ lookup n lst)) →
        ((n : Fin m) →
                 (n ≡ i → lookup n y′ ≡ delete (lookup i lst) j) ×
                 (n ≢ i → lookup n y′ ≡ lookup n lst)) →
        (n2 : Fin m) → lookup n2 y ≡ lookup n2 y′
anyN-trans≡ lst y y′ {i} {j} fun-y fun-y′ n2 with n2 ≡f i
... | inj₁ n2≡i = ≡-trans for-y (sym for-y′)
    where for-y : lookup n2 y ≡ delete (lookup i lst) j
          for-y = proj₁ (fun-y n2) n2≡i
          for-y′ : lookup n2 y′ ≡ delete (lookup i lst) j
          for-y′ = proj₁ (fun-y′ n2) n2≡i
... | inj₂ n2≢i = ≡-trans for-y (sym for-y′)
    where for-y : lookup n2 y ≡ lookup n2 lst
          for-y = proj₂ (fun-y n2) n2≢i
          for-y′ : lookup n2 y′ ≡ lookup n2 lst
          for-y′ = proj₂ (fun-y′ n2) n2≢i

private
  head-deleted-lemma : ∀{l} {A : Set l} → {m : ℕ} → (x : kvec A) → (xs : Vec (kvec A) m) →
                        (n : Fin (suc m)) → {j : Fin (kvec.k x)} →
                        n ≢ zero → lookup n ((delete x j) ∷ xs) ≡ lookup n (x ∷ xs)
  head-deleted-lemma x xs zero n≢z = contra refl n≢z
  head-deleted-lemma {m = zero} x [] (suc ())
  head-deleted-lemma {m = suc m} x (x′ ∷ xs) (suc n) n≢z = refl

remove-lst-internal : ∀{l}{A : Set l} → {m : ℕ} → (lst : Vec (kvec A) m) →
                      {i : Fin m} → {j : Fin (kvec.k (lookup i lst))} → remove-lst-with-proof A lst i j
remove-lst-internal {m = zero} [] {()}
remove-lst-internal {A = A} {suc m′} (x ∷ xs) {zero} {j} =
  record { y = y
         ; equality-proof = equality-pf
         ; length-proof = length-pf
         ; unique-proof = unique-pf
         }
    where y : Vec (kvec A) (suc m′)
          y = (delete x j) ∷ xs
          equality-pf : (n : Fin (suc m′)) →
                        (n ≡ zero → lookup n y ≡ delete (lookup zero (x ∷ xs)) j) ×
                        (n ≢ zero → lookup n y ≡ lookup n (x ∷ xs))
          equality-pf n = (λ n≡z → begin
                 lookup n ((delete x j) ∷ xs)
                ≡⟨ cong (λ h → lookup h ((delete x j) ∷ xs)) n≡z ⟩
                 lookup zero ((delete x j) ∷ xs)
                ≡⟨ refl ⟩
                 delete x j
                ∎) , (λ n≢z →
                 lookup n ((delete x j) ∷ xs)
                ≡⟨ head-deleted-lemma x xs n n≢z ⟩
                 lookup n (x ∷ xs)
                ∎)
          length-pf : (n : Fin (suc m′)) →
                      (n ≡ zero → suc (kvec.k (lookup n y)) ≡ kvec.k (lookup n (x ∷ xs))) ×
                      (n ≢ zero → kvec.k (lookup n y) ≡ kvec.k (lookup n (x ∷ xs)))
          length-pf n = (λ n≡z → begin
                suc (kvec.k (lookup n y))
               ≡⟨ cong (λ h → suc (kvec.k (lookup h y))) n≡z ⟩
                suc (kvec.k (lookup zero y))
               ≡⟨ suc-deleted-lemma x j ⟩
                kvec.k x
               ≡⟨ refl ⟩
                kvec.k (lookup zero (x ∷ xs))
               ≡⟨ cong (λ h → kvec.k (lookup h (x ∷ xs))) (sym n≡z) ⟩
                kvec.k (lookup n (x ∷ xs))
               ∎) , (λ n≢z → begin
                kvec.k (lookup n y)
               ≡⟨ (cong λ h → kvec.k h) (head-deleted-lemma x xs n n≢z) ⟩
                kvec.k (lookup n (x ∷ xs))
               ∎)
          {-
          -- ※ equality-pf を用いた場合の length-pf
          length-pf : (n : Fin (suc m′)) →
                      (n ≡ zero → suc (kvec.k (lookup n y)) ≡ kvec.k (lookup n (x ∷ xs))) ×
                      (n ≢ zero → kvec.k (lookup n y) ≡ kvec.k (lookup n (x ∷ xs)))
          length-pf n = (λ n≡z → begin
                suc (kvec.k (lookup n y))
               ≡⟨ cong (λ h → suc (kvec.k h)) (proj₁ (equality-pf n) n≡z) ⟩
                suc (kvec.k (delete (lookup zero (x ∷ xs)) j))
               ≡⟨ suc-deleted-lemma x j ⟩
                kvec.k x
               ≡⟨ refl ⟩
                kvec.k (lookup zero (x ∷ xs))
               ≡⟨ cong (λ h → kvec.k (lookup h (x ∷ xs))) (sym n≡z) ⟩
                kvec.k (lookup n (x ∷ xs))
               ∎) , (λ n≢z → begin
                kvec.k (lookup n y)
               ≡⟨ cong (λ h → kvec.k h) (proj₂ (equality-pf n) n≢z) ⟩
                kvec.k (lookup n (x ∷ xs))
               ∎) -}
          unique-pf : (y′ : Vec (kvec A) (suc m′)) →
                      ((n : Fin (suc m′)) →
                       (n ≡ zero → lookup n y′ ≡ delete (lookup zero (x ∷ xs)) j) ×
                       (n ≢ zero → lookup n y′ ≡ lookup n (x ∷ xs))) →
                      ((n : Fin (suc m′)) →
                       (n ≡ zero → suc (kvec.k (lookup n y′)) ≡ kvec.k (lookup n (x ∷ xs))) ×
                       (n ≢ zero → kvec.k (lookup n y′) ≡ kvec.k (lookup n (x ∷ xs)))) →
                      y ≡ y′
          unique-pf y′ eq-y′ _ = vec-eq-main (anyN-trans≡ (x ∷ xs) y y′ equality-pf eq-y′)
remove-lst-internal {l} {A} {suc m′} (x ∷ xs) {suc i} {j} =
  record { y = y
         ; equality-proof = equality-pf
         ; length-proof = length-pf
         ; unique-proof = unique-pf
         }
    where recur : remove-lst-with-proof A xs i j
          recur = remove-lst-internal {m = m′} xs {i} {j}
          recur-y : Vec (kvec A) m′
          recur-y = remove-lst-with-proof.y recur
          y : Vec (kvec A) (suc m′)
          y = x ∷ recur-y
          equality-pf′ : (n : Fin m′) →
                         (n ≡ i → lookup n recur-y ≡ delete (lookup i xs) j) ×
                         (n ≢ i → lookup n recur-y ≡ lookup n xs)
          equality-pf′ = remove-lst-with-proof.equality-proof recur
          equality-pf : (n : Fin (suc m′)) →
                        (n ≡ suc i → lookup n y ≡ delete (lookup (suc i) (x ∷ xs)) j) ×
                        (n ≢ suc i → lookup n y ≡ lookup n (x ∷ xs))
          equality-pf zero = (λ z≡suci → contra z≡suci (sym≢ (suc≢zero {a = i}))) , (λ z≢suci → begin
              lookup zero y
             ≡⟨ refl ⟩
              x
             ≡⟨ sym refl ⟩
              lookup zero (x ∷ xs)
             ∎)
          equality-pf (suc n) = (λ sucn≡suci → proj₁ (equality-pf′ n) (suc-≡ (sucn≡suci))) ,
                                (λ sucn≢suci → proj₂ (equality-pf′ n) (suc-≢ (sucn≢suci)))
          length-pf′ : (n : Fin m′) →
                       (n ≡ i → suc (kvec.k (lookup n recur-y)) ≡ kvec.k (lookup n xs)) ×
                       (n ≢ i → kvec.k (lookup n recur-y) ≡ kvec.k (lookup n xs))
          length-pf′ = remove-lst-with-proof.length-proof recur
          length-pf : (n : Fin (suc m′)) →
                      (n ≡ suc i → suc (kvec.k (lookup n y)) ≡ kvec.k (lookup n (x ∷ xs))) ×
                      (n ≢ suc i → kvec.k (lookup n y) ≡ kvec.k (lookup n (x ∷ xs)))
          length-pf zero = (λ z≡suci → contra z≡suci (sym≢ (suc≢zero {a = i}))) , (λ z≢suci → refl)
          length-pf (suc n) = (λ sucn≡suci → proj₁ (length-pf′ n) (suc-≡ (sucn≡suci))) ,
                              (λ sucn≢suci → proj₂ (length-pf′ n) (suc-≢ (sucn≢suci)))
          unique-pf : (y′ : Vec (kvec A) (suc m′)) →
                  ((n : Fin (suc m′)) →
                    (n ≡ suc i → lookup n y′ ≡ delete (lookup (suc i) (x ∷ xs)) j) ×
                    (n ≢ suc i → lookup n y′ ≡ lookup n (x ∷ xs))) →
                  ((n : Fin (suc m′)) →
                    (n ≡ suc i → suc (kvec.k (lookup n y′)) ≡ kvec.k (lookup n (x ∷ xs))) ×
                    (n ≢ suc i → kvec.k (lookup n y′) ≡ kvec.k (lookup n (x ∷ xs)))) →
                  y ≡ y′
          unique-pf y′ eq-y′ _ = vec-eq-main (anyN-trans≡ (x ∷ xs) y y′ equality-pf eq-y′)

-- ========================================
--   Test
-- ========================================
len : ℕ
len = suc (suc (suc (zero)))

kv1 : kvec String
kv1 = record { k = suc (suc (suc (suc (suc zero))))
             ; vec = "a" ∷ "b" ∷ "c" ∷ "d" ∷ "e" ∷ []
             }

kv2 : kvec String
kv2 = record { k = suc (suc (suc (suc zero)))
             ; vec = "1" ∷ "2" ∷ "3" ∷ "4" ∷ []
             }

kv3 : kvec String
kv3 = record { k = suc (suc zero)
             ; vec = "m" ∷ "l" ∷ []
             }

t1 : Vec (kvec String) len
t1 = kv1 ∷ kv2 ∷ kv3 ∷ []

make-fin : (m n : ℕ) → m < n → Fin n
make-fin zero zero ()
make-fin zero (suc n) p = zero
make-fin (suc m) zero ()
make-fin (suc m) (suc n) p = Data.Fin.suc (make-fin m n (suc-suc-<{m}{n} p))
  where suc-suc-< : {m n : ℕ} → (suc m) < (suc n) → m < n
        suc-suc-<{m}{n} (s≤s m≤n) = m≤n

test-n0 : Fin len
test-n0 = make-fin 0 len (s≤s z≤n)

test-n1 : Fin len
test-n1 = make-fin 1 len (s≤s (s≤s z≤n))

test-n2 : Fin len
test-n2 = make-fin 2 len (s≤s (s≤s (s≤s z≤n)))

test-i : Fin len
test-i = make-fin 0 len (s≤s z≤n)

test-k : ℕ
test-k = kvec.k (lookup test-i t1) -- 5

j<k : 1 < 5
j<k = s≤s (s≤s (z≤n{3}))

test-j : Fin test-k
test-j = make-fin 1 test-k j<k

-- 1. remove-lst
removed-t1 : Vec (kvec String) len
removed-t1 = remove-lst t1 test-i test-j

-- 1.1) length proof
removed-t1-lnpf : (n : Fin len) →
                  (n ≡ test-i → suc (kvec.k (lookup n removed-t1)) ≡ kvec.k (lookup n t1)) ×
                  (n ≢ test-i → kvec.k (lookup n removed-t1) ≡ kvec.k (lookup n t1))
removed-t1-lnpf = length-proof1 t1 test-i test-j

exp1 : suc (kvec.k (lookup test-n0 removed-t1)) ≡ kvec.k (lookup test-n0 t1)
exp1 = proj₁ (removed-t1-lnpf test-n0) refl

exp2 : kvec.k (lookup test-n1 removed-t1) ≡ kvec.k (lookup test-n1 t1)
exp2 = proj₂ (removed-t1-lnpf test-n1) n1≢i
       where n1≢i : test-n1 ≢ test-i
             n1≢i = suc≢zero

-- 2. remove-lst-internal
removed-t1-with-pf : remove-lst-with-proof String t1 test-i test-j
removed-t1-with-pf = remove-lst-internal t1

t1-y : Vec (kvec String) len
t1-y = remove-lst-with-proof.y removed-t1-with-pf

-- 2.1) equality
removed-t1-with-pf-eqpf : (n : Fin len) →
                          (n ≡ test-i → lookup n t1-y ≡ delete (lookup test-i t1) test-j) ×
                          (n ≢ test-i → lookup n t1-y ≡ lookup n t1)
removed-t1-with-pf-eqpf = remove-lst-with-proof.equality-proof removed-t1-with-pf

-- 2.2) length
removed-t1-with-pf-lnpf : (n : Fin len) →
                          (n ≡ test-i → suc (kvec.k (lookup n t1-y)) ≡ kvec.k (lookup n t1)) ×
                          (n ≢ test-i → kvec.k (lookup n t1-y) ≡ kvec.k (lookup n t1))
removed-t1-with-pf-lnpf = remove-lst-with-proof.length-proof removed-t1-with-pf

exp1′ : lookup test-n0 t1-y ≡ delete (lookup test-n0 t1) test-j
exp1′ = proj₁ (removed-t1-with-pf-eqpf test-n0) refl

exp2′ : lookup test-n1 t1-y ≡ lookup test-n1 t1
exp2′ = proj₂ (removed-t1-with-pf-eqpf test-n1) n1≢i
       where n1≢i : test-n1 ≢ test-i
             n1≢i = suc≢zero

-- 2.3) unique
removed-t1-with-pf-unipf : (y′ : Vec (kvec String) len) →
                           ((n : Fin len) →
                            (n ≡ test-i → lookup n y′ ≡ delete (lookup test-i t1) test-j) ×
                            (n ≢ test-i → lookup n y′ ≡ lookup n t1)) →
                           ((n : Fin len) →
                            (n ≡ test-i → suc (kvec.k (lookup n y′)) ≡ kvec.k (lookup n t1)) ×
                            (n ≢ test-i → kvec.k (lookup n y′) ≡ kvec.k (lookup n t1))) →
                           t1-y ≡ y′
removed-t1-with-pf-unipf = remove-lst-with-proof.unique-proof removed-t1-with-pf


