open import Relation.Binary.PropositionalEquality
open import Data.List

-- The Agda membership uses setoid equality, yuck
data _∈_ {A : Set} : A -> List A -> Set where
  here  : ∀ {x xs} -> x ∈ (x ∷ xs)
  there : ∀ {x y xs} -> (d : x ∈ xs) → x ∈ (y ∷ xs)

delete : {A : Set} -> {x : A} -> {l : List A} -> (a : x ∈ l) -> List A
delete {l = []} ()
delete {l = x ∷ l} here = l
delete {l = y ∷ l} (there a') = y ∷ delete a'

merge : {A : Set} -> {x : A} -> {l : List A} -> (a b : x ∈ l) -> List A
merge {l = []} () ()
merge {l = x ∷ l} here here = x ∷ l
merge {l = x ∷ l} here (there b) = x ∷ delete b
merge {l = x ∷ l} (there a) here = l
merge {l = x ∷ l} (there a) (there b) = x ∷ merge a b

merged : {A : Set} -> {x : A} -> {l : List A} -> (a b : x ∈ l) -> (x ∈ merge a b)
merged {l = []} () ()
merged {l = x ∷ l} here here = here
merged {l = x ∷ l} here (there b) = here
merged {l = x ∷ l} (there a) here = a
merged {l = x ∷ l} (there a) (there b) = there (merged a b)

data Con : Set
data Ty : Con → Set
data Squig : {γ : Con} → Ty γ → Ty γ → Set
data ListSub : {γ : Con} → {α β δ : Ty γ} → Squig α β → List (Squig δ α) → List (Squig δ β) → Set
-- data Tm : {γ : Con} → Ty γ → Set

data Con where
  · : Con
  _,_ : (γ : Con) → Ty γ → Con

_&_ : {γ : Con} → {α β δ : Ty γ} → Squig α β → Squig β δ → Squig α δ

data ListSub where
  · : {γ : Con} → {α β δ : Ty γ} → {dl' : List (Squig δ β)} → {σ : Squig α β} → ListSub σ [] dl'
  _,_ : {γ : Con} {α β δ : Ty γ} {dl : List (Squig δ α)} {dl' : List (Squig δ β)} {σ : Squig α β} {τ : Squig δ α} -> ListSub σ dl dl' -> (τ & σ) ∈ dl' -> ListSub σ (τ ∷ dl) dl'

wk-sub : {γ : Con} → {α β δ : Ty γ} → {σ : Squig α β} → {dl1 : List (Squig δ α)} → {dl2 : List (Squig δ β)} -> {w : Squig δ β} → ListSub σ dl1 dl2 -> ListSub σ dl1 (w ∷ dl2)
wk-sub {dl1 = []} · = ·
wk-sub {dl1 = x ∷ dl1} (l , d) = (wk-sub l) , (there d)

data Ty where
  · : Ty ·
  _,_ : ∀ {γ α} → (β : Ty γ) -> List (Squig α β) → Ty (γ , α)

data Squig where
  · : Squig · ·
  _,_ : {γ : Con} → {α β δ : Ty γ} → (σ : Squig α β) → {dl1 : List (Squig δ α)} → {dl2 : List (Squig δ β)} → ListSub σ dl1 dl2 → Squig (α , dl1) (β , dl2)

_&&_ : {γ : Con} → {α β δ ε : Ty γ} {σ : Squig α β} {τ : Squig β ε} {dl1 : List (Squig δ α) } {dl2 : List (Squig δ β) } {dl3 : List (Squig δ ε)} → ListSub σ dl1 dl2 -> ListSub τ dl2 dl3 -> ListSub (σ & τ) dl1 dl3

transp-sub : {γ : Con} → {α β δ : Ty γ} → (σ : Squig β δ) -> (dl1 : List (Squig α β)) → ListSub σ dl1 (map (λ x → x & σ) dl1)
transp-sub σ [] = ·
transp-sub σ (x ∷ dl1) = wk-sub (transp-sub σ dl1) , here

pushforward-dep : {γ : Con} -> {α β δ : Ty γ} -> {σ : Squig α β} {τ : Squig δ α} {dl1 : List (Squig δ α)} -> {dl2 : List (Squig δ β)} -> ListSub σ dl1 dl2 -> τ ∈ dl1 -> (τ & σ) ∈ dl2
pushforward-dep (ls , x) here = x
pushforward-dep (ls , x) (there d) = pushforward-dep ls d

_&_ {·} {·} {·} · · = ·
_&_ (σ , dl1) (τ , dl2) = (σ & τ) , (dl1 && dl2)

· && dl2 = ·
(dl1 , x) && dl2 = (dl1 && dl2) , {!assoc of & and then pushforward-dep!}

pushout : {γ : Con} → {α β β' : Ty γ} → (σ : Squig α β) → (σ' : Squig α β') → Ty γ
inl : {γ : Con} → {α β β' : Ty γ} → (σ : Squig α β) → (σ' : Squig α β') → Squig β (pushout σ σ')
inr : {γ : Con} → {α β β' : Ty γ} → (σ : Squig α β) → (σ' : Squig α β') → Squig β' (pushout σ σ')

pushout {α = ·} · · = ·
pushout {α = α , []} {β , l} {β' , l'} (σ , ·) (σ' , ·)
  = (pushout σ σ') , ((map (λ x → x & inl σ σ') l) ++ (map (λ x → x & inr σ σ') l'))
pushout {α = α , (τ ∷ dl)} {β , l} {β' , l'} (σ , (s , d)) (σ' , (s' , d'))
        with (pushout (σ , s) (σ' , s'))
...     | p , lp = p , merge leftdep rightdep
  where leftdep  = pushforward-dep (transp-sub {!inl σ σ'!} {!l!}) {!d!}
        rightdep = pushforward-dep (transp-sub {!inr σ σ'!} {!l'!}) {!d'!}
-- And the equation σ ; inl == σ' ; inr

inl = {!!}
inr = {!!}

-- data Tm where
--   var : {γ : Con} → {α : Ty γ} → Var γ α → Tm α
--   u : {γ : Con} → {α β : Ty γ} → Squig α β → Tm α
