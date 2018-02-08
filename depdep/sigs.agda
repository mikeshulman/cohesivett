{-# OPTIONS --no-positivity-check #-}
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Data.List
open import Data.List.Properties
open import Data.Product hiding (map)
open import Function

postulate ext : ∀ {l1 l2} -> Extensionality l1 l2

-- The Agda membership uses setoid equality, yuck
data _∈_ {A : Set} : A -> List A -> Set where
  here  : ∀ {x xs} -> x ∈ (x ∷ xs)
  there : ∀ {x y xs} -> (d : x ∈ xs) → x ∈ (y ∷ xs)

merge : {A : Set} -> {x : A} -> {l : List A} -> (a b : x ∈ l) -> List A
merge {l = []} () ()
merge {l = x ∷ l} here here = x ∷ l
merge {l = x ∷ l} here (there b) = l
merge {l = x ∷ l} (there a) here = l
merge {l = x ∷ l} (there a) (there b) = x ∷ merge a b

in-merge : {A : Set} -> {x y : A} -> {l : List A} -> (a b : x ∈ l) -> y ∈ l -> (y ∈ merge a b)
in-merge here here i = i
in-merge here (there b) here = b
in-merge (there a) here here = a
in-merge (there a) (there b) here = here
in-merge here (there b) (there i) = i
in-merge (there a) here (there i) = i
in-merge (there a) (there b) (there i) = there (in-merge a b i)

in-merge-eq : {A : Set} -> {x : A} -> {l : List A} -> (a b : x ∈ l) -> (in-merge a b a ≡ in-merge a b b)
in-merge-eq {l = []} () ()
in-merge-eq {l = x₁ ∷ l} here here = refl
in-merge-eq {l = x₁ ∷ l} here (there b) = refl
in-merge-eq {l = x₁ ∷ l} (there a) here = refl
in-merge-eq {l = x₁ ∷ l} (there a) (there b) = cong there (in-merge-eq a b)

in-append-first : {A : Set} -> {x : A} -> {l l' : List A} -> (i : x ∈ l) -> x ∈ (l ++ l')
in-append-first {l = []} ()
in-append-first {l = x ∷ l} here = here
in-append-first {l = x₁ ∷ l} (there i) = there (in-append-first i)

in-append-second : {A : Set} -> {x : A} -> {l l' : List A} -> (i : x ∈ l') -> x ∈ (l ++ l')
in-append-second {l = []} i = i
in-append-second {l = x ∷ l} i = there (in-append-second {l = l} i)

in-map : {A B : Set} -> {l : List A} -> (f : A -> B) -> {x : A} -> x ∈ l -> (f x ∈ map f l)
in-map f here = here
in-map f (there e) = there (in-map f e)

-- Test positivity with inductive definition
ListSub : {A : Set} (a b : List A) -> Set
ListSub a b = ∀ x -> (x ∈ a -> x ∈ b)

sub-wk : {A : Set} {x : A} {dl1 dl2 : List A} -> ListSub dl1 dl2 -> ListSub dl1 (x ∷ dl2)
sub-wk l x i = there (l x i)

sub-wkl : {A : Set} {x : A} {dl1 dl2 : List A} -> ListSub (x ∷ dl1) dl2 -> ListSub dl1 dl2
sub-wkl l x i = l x (there i)

sub-id : {A : Set} {dl1 : List A} -> ListSub dl1 dl1
sub-id x i = i

eq-to-sub : {A : Set} {dl1 dl2 : List A} -> dl1 ≡ dl2 -> ListSub dl1 dl2
eq-to-sub refl x i = i

eq-to-sub-comp : {A : Set} {dl1 dl2 dl3 : List A} -> (p : dl1 ≡ dl2) → (q : dl2 ≡ dl3) -> ({x : A} → eq-to-sub q x ∘ eq-to-sub p x ≗ eq-to-sub (trans p q) x)
eq-to-sub-comp refl refl x = refl

sub-eq : {A : Set} {dl1 dl2 : List A} -> {s s' : ListSub dl1 dl2} -> ({x : A} -> s x ≗ s' x) -> s ≡ s'
sub-eq f = ext (λ x → ext f)

sub-append-first : {A : Set} -> (l l' : List A) -> ListSub l (l ++ l')
sub-append-first [] l' x ()
sub-append-first (x ∷ l) l' .x here = here
sub-append-first (x ∷ l) l' x₁ (there i) = there (sub-append-first _ _ _ i)

sub-append-second : {A : Set} -> (l l' : List A) -> ListSub l' (l ++ l')
sub-append-second [] l' = sub-id
sub-append-second (x ∷ l) l' x' i = there (sub-append-second l l' x' i)

sub-map : {A B : Set} -> (f : A → B) -> {l l' : List A} -> (s : ListSub l l') -> ListSub (map f l) (map f l')
sub-map f {l = []}  s x ()
sub-map f {l = x ∷ l} s .(f x) here = in-map f (s x here)
sub-map f {l = x ∷ l} s x₁ (there i) = sub-map f (sub-wkl s) x₁ i

pushout-list : {A : Set} {a b b' : List A} -> ListSub a b -> ListSub a b' -> List A
inl-list : {A : Set} {a b b' : List A} -> ( s1 : ListSub a b ) -> ( s2 : ListSub a b' ) -> ListSub b (pushout-list s1 s2)
inr-list : {A : Set} {a b b' : List A} -> ( s1 : ListSub a b ) -> ( s2 : ListSub a b' ) -> ListSub b' (pushout-list s1 s2)

pushout-list {a = []} {b} {b'} s s' = b ++ b'
pushout-list {a = x ∷ a} s s' = merge (inl-list (sub-wkl s) (sub-wkl s') x (s x here)) (inr-list (sub-wkl s) (sub-wkl s') x (s' x here))

inl-list {a = []} {b} {b'} s1 s2 x i = sub-append-first b b' x i
inl-list {a = x ∷ a} s1 s2 x' i = in-merge _ _ (inl-list (sub-wkl s1) (sub-wkl s2) x' i)

inr-list {a = []} {b} {b'} s1 s2 x i = sub-append-second b b' x i
inr-list {a = x ∷ a} s1 s2 x' i = in-merge _ _ (inr-list (sub-wkl s1) (sub-wkl s2) x' i)

pushout-prop-list : {A : Set} {a b b' : List A} -> (s1 : ListSub a b ) -> ( s2 : ListSub a b' ) -> ({x : A} → inl-list s1 s2 x ∘ s1 x ≗ inr-list s1 s2 x ∘ s2 x)
pushout-prop-list {a = []} s1 s2 ()
pushout-prop-list {a = x ∷ a} s1 s2 here
  = in-merge-eq
      (inl-list (sub-wkl s1) (sub-wkl s2) x (s1 x here))
      (inr-list (sub-wkl s1) (sub-wkl s2) x (s2 x here))
pushout-prop-list {a = x ∷ a} s1 s2 {x'} (there i) = cong (in-merge _ _) (pushout-prop-list (sub-wkl s1) (sub-wkl s2) i)


data Con : Set
data Ty : Con → Set
data Squig : {γ : Con} → Ty γ → Ty γ → Set

-- -- data Tm : {γ : Con} → Ty γ → Set

data Con where
  · : Con
  _,_ : (γ : Con) → Ty γ → Con

_&_ : {γ : Con} → {α β δ : Ty γ} → Squig α β → Squig β δ → Squig α δ

data Ty where
  · : Ty ·
  _,_ : ∀ {γ α} β -> List (Squig α β) → Ty (γ , α)

data Squig where
  · : Squig · ·
  _,_ : {γ : Con} → {α β δ : Ty γ} → (σ : Squig α β) → {dl1 : List (Squig δ α)} → {dl2 : List (Squig δ β)} → ListSub (map (λ x → x & σ) dl1) dl2 → Squig (α , dl1) (β , dl2)


fix-map : {γ : Con} → {α β δ : Ty γ} → {σ σ' : Squig α β} → {dl1 : List (Squig δ α)} → σ ≡ σ' → map (λ x → x & σ) dl1 ≡ map (λ x → x & σ') dl1
fix-map refl = refl

adjust-postcomp : {γ : Con} → {α β δ : Ty γ} → {σ σ' : Squig α β} → {dl1 : List (Squig δ α)} → {dl2 : List (Squig δ β)} → σ ≡ σ' → ListSub (map (λ x → x & σ') dl1) dl2 → ListSub (map (λ x → x & σ) dl1) dl2
adjust-postcomp p s x = s x ∘ eq-to-sub (fix-map p) x

squig-eq : {γ : Con} → {α β δ : Ty γ} → {σ σ' : Squig α β} → {dl1 : List (Squig δ α)} → {dl2 : List (Squig δ β)} → {s : ListSub (map (λ x → x & σ) dl1) dl2} -> {s' : ListSub (map (λ x → x & σ') dl1) dl2} -> (p : σ ≡ σ') → s ≡ adjust-postcomp p s' → _≡_ {A = Squig (α , dl1) (β , dl2)} (σ , s) (σ' , s')
squig-eq {σ = σ} {s' = s'} refl p = cong (λ y -> σ , y) p

squig-assoc : ∀ {γ : Con} → {α β δ ε : Ty γ} → {σ : Squig α β} {τ : Squig β δ} {θ : Squig δ ε} → (σ & τ) & θ ≡ σ & (τ & θ)
squig-id : {γ : Con} → {α : Ty γ} → Squig α α
squig-right-unit : ∀ {γ : Con} → {α β : Ty γ} → {σ : Squig α β} → σ & squig-id ≡ σ

abstract
  &-lemma : {γ : Con} → {θ α β δ : Ty γ} → {σ : Squig α β} → {τ : Squig β δ} -> {dl1 : List (Squig θ α)} -> map (λ x₁ → x₁ & (σ & τ)) dl1 ≡ map (λ y → y & τ) (map (λ x₁ → x₁ & σ) dl1)
  &-lemma {σ = σ} {τ} {dl1} = begin
                 map (λ x₁ → x₁ & (σ & τ)) dl1
               ≡⟨ sym (map-cong (λ x → squig-assoc) dl1) ⟩
                 map (λ x₁ → (x₁ & σ) & τ) dl1
               ≡⟨ map-compose dl1 ⟩
                 map (λ y → y & τ) (map (λ x₁ → x₁ & σ) dl1)
               ∎

_&_ {·} {·} {·} · · = ·
(σ , s) & (τ , s') = (σ & τ) , (λ x → s' x ∘ sub-map (λ y → y & τ) s x ∘ eq-to-sub &-lemma x)


squig-id {α = ·} = ·
squig-id {α = α₁ , l} = squig-id , eq-to-sub path
  where
    abstract path : map (λ x → x & squig-id) l ≡ l
             path = begin
                    map (λ x → x & squig-id) l
                 ≡⟨ map-cong (λ x → squig-right-unit) l ⟩
                   map (λ x → x) l
                 ≡⟨ map-id l ⟩
                   l
                 ∎

squig-right-unit {·} {σ = ·} = refl
squig-right-unit {γ , x} {σ = σ , s} = squig-eq squig-right-unit (sub-eq (λ x₂ → {!!}))

squig-assoc {·} {·} {·} {·} {·} {σ = ·} {·} {·} = refl
squig-assoc {γ , α} {σ = σ , s1} {τ , s2} {θ , s3} = squig-eq squig-assoc (sub-eq (λ {x} i → cong (λ y → s3 x y) {!!}))

pushout : {γ : Con} → {α β β' : Ty γ} → (σ : Squig α β) → (σ' : Squig α β') → Ty γ
inl : {γ : Con} → {α β β' : Ty γ} → (σ : Squig α β) → (σ' : Squig α β') → Squig β (pushout σ σ')
inr : {γ : Con} → {α β β' : Ty γ} → (σ : Squig α β) → (σ' : Squig α β') → Squig β' (pushout σ σ')
pushout-prop : {γ : Con} → {α β β' : Ty γ} → (σ : Squig α β) → (σ' : Squig α β') -> (σ & inl σ σ') ≡ (σ' & inr σ σ')

pushout-lemma : {γ : Con} → {α β β' δ : Ty γ} → (σ : Squig α β) → (σ' : Squig α β') -> (l : List (Squig δ α)) -> map (λ x → x & inl σ σ') (map (λ x → x & σ) l) ≡  map (λ x → x & inr σ σ') (map (λ x → x & σ') l)
pushout-lemma {α = α} {β} {β'} {δ} σ σ' l = begin
    map (λ x → x & inl σ σ') (map (λ x → x & σ) l)
  ≡⟨ sym &-lemma ⟩
    map (λ x → x & (σ & inl σ σ')) l
  ≡⟨ map-cong (λ x → cong (λ y → x & y) (pushout-prop σ σ')) l ⟩
    map (λ x → x & (σ' & inr σ σ')) l
  ≡⟨ &-lemma ⟩
    map (λ x → x & inr σ σ') (map (λ x → x & σ') l)
  ∎

pushout {·} σ σ' = ·
pushout {γ , δ} {α , αl} {β , βl} {β' , βl'} (σ , s) (σ' , s') = (pushout σ σ') , (pushout-list newβl transpβl')
  where newβl  = sub-map (λ x → x & inl σ σ') s
        newβl' = sub-map (λ x → x & inr σ σ') s'

        transpβl' : ListSub (map (λ x → x & inl σ σ') (map (λ x → x & σ) αl)) (map (λ x → x & inr σ σ') βl')
        transpβl' i = newβl' i ∘ eq-to-sub (pushout-lemma σ σ' αl) i

inl {·} {β = ·} σ σ' = ·
inl {γ , δ} {β = β₁ , βl} (_,_ σ {dl1 = dl1} s) (_,_ σ' {dl2 = dl2'} s') = (inl _ _) , inl-list (sub-map (λ x → x & inl σ σ') s) rsub
  where rsub : ListSub (map (λ x → x & inl σ σ') (map (λ x → x & σ) dl1)) (map (λ x → x & inr σ σ') dl2')
        rsub i = sub-map (λ x → x & inr σ σ') s' i ∘ eq-to-sub (pushout-lemma σ σ' dl1) i

inr {·} {β' = ·} σ σ' = ·
inr {γ , δ} {β = β' , βl'} (_,_ σ {dl1 = dl1}  s) (_,_ σ' {dl2 = dl2'} s') = (inr _ _) , inr-list (sub-map (λ x → x & inl σ σ') s) rsub
  where rsub : ListSub (map (λ x → x & inl σ σ') (map (λ x → x & σ) dl1)) (map (λ x → x & inr σ σ') dl2')
        rsub i = sub-map (λ x → x & inr σ σ') s' i ∘ eq-to-sub (pushout-lemma σ σ' dl1) i

pushout-prop-lemma : {γ : Con} → {α β β' δ : Ty γ} → (σ : Squig α β) → (σ' : Squig α β') ->
                     {dl1 : List (Squig δ α)} -> {dl2 : List (Squig δ β')} -> {dl3 : List (Squig δ β)} ->
                     {s : ListSub (map (λ y → y & σ) dl1) dl3} -> {s' : ListSub (map (λ y → y & σ') dl1) dl2} ->
                     {x : Squig δ (pushout σ σ')} -> (x₁ : x ∈ map (λ x₂ → x₂ & (σ & inl σ σ')) dl1) →
      inl-list (sub-map (λ x₂ → x₂ & inl σ σ') s)
      (λ i x₂ →
         sub-map (λ x₃ → x₃ & inr σ σ') s' i
         (eq-to-sub (pushout-lemma σ σ' dl1) i x₂))
      x (sub-map (λ y → y & inl σ σ') s x (eq-to-sub &-lemma x x₁))
      ≡
      inr-list (sub-map (λ x₂ → x₂ & inl σ σ') s)
      (λ i x₂ →
         sub-map (λ x₃ → x₃ & inr σ σ') s' i
         (eq-to-sub (pushout-lemma σ σ' dl1) i x₂))
      x
      (sub-map (λ y → y & inr σ σ') s' x
       (eq-to-sub &-lemma x
        (eq-to-sub (fix-map (pushout-prop σ σ')) x x₁)))
pushout-prop-lemma σ σ' {dl1 = dl1} {s = s} {s'} {x} x₁
  = begin
      inl-list (sub-map (λ x₂ → x₂ & inl σ σ') s)
               (λ i x₂ → sub-map (λ x₃ → x₃ & inr σ σ') s' i (eq-to-sub (pushout-lemma σ σ' dl1) i x₂))
               x
               (sub-map (λ y → y & inl σ σ') s x (eq-to-sub &-lemma x x₁))
    ≡⟨ pushout-prop-list (sub-map (λ x₂ → x₂ & inl σ σ') s)
                         (λ i x₂ → sub-map (λ x₃ → x₃ & inr σ σ') s' i (eq-to-sub (pushout-lemma σ σ' dl1) i x₂))
                         (eq-to-sub &-lemma x x₁) ⟩
      inr-list _
               ((λ i x₂ → sub-map (λ x₃ → x₃ & inr σ σ') s' i (eq-to-sub (pushout-lemma σ σ' dl1) i x₂)))
               x
               ((sub-map (λ x₃ → x₃ & inr σ σ') s' x (eq-to-sub (pushout-lemma σ σ' dl1) x (eq-to-sub &-lemma x x₁))))
    ≡⟨ cong (λ x₂ → inr-list (sub-map (λ x₂ → x₂ & inl σ σ') s)
                             _
                             x
                             (sub-map (λ x₃ → x₃ & inr σ σ') s' x x₂)) t ⟩
      inr-list (sub-map (λ x₂ → x₂ & inl σ σ') s)
               (λ i x₂ → sub-map (λ x₃ → x₃ & inr σ σ') s' i (eq-to-sub (pushout-lemma σ σ' dl1) i x₂))
               x
               (sub-map (λ y → y & inr σ σ') s' x
                 (eq-to-sub &-lemma x (eq-to-sub (fix-map (pushout-prop σ σ')) x x₁)))
    ∎
  where t : (eq-to-sub (pushout-lemma σ σ' dl1) x (eq-to-sub &-lemma x x₁))
            ≡
            (eq-to-sub &-lemma x (eq-to-sub (fix-map (pushout-prop σ σ')) x x₁))
        t = begin
              eq-to-sub (pushout-lemma σ σ' dl1) x (eq-to-sub &-lemma x x₁)
            ≡⟨ eq-to-sub-comp &-lemma (pushout-lemma σ σ' dl1) x₁ ⟩
              eq-to-sub (trans &-lemma (pushout-lemma σ σ' dl1)) x x₁
            ≡⟨ cong (λ y -> eq-to-sub y x x₁) (proof-irrelevance (trans &-lemma (pushout-lemma σ σ' dl1))
                                              (trans (fix-map (pushout-prop σ σ')) &-lemma)) ⟩
              eq-to-sub (trans (fix-map (pushout-prop σ σ')) &-lemma) x x₁
            ≡⟨ sym (eq-to-sub-comp (fix-map (pushout-prop σ σ')) &-lemma x₁) ⟩
              eq-to-sub &-lemma x (eq-to-sub (fix-map (pushout-prop σ σ')) x x₁)
            ∎

pushout-prop {·} · · = refl
pushout-prop {γ , δ} (_,_ σ {dl1} s) (σ' , s') = squig-eq (pushout-prop σ σ') (sub-eq (pushout-prop-lemma σ σ'))
