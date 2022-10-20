{-# OPTIONS --without-K #-}

import Relation.Binary.PropositionalEquality as Eq 
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl) 

open import Level renaming (zero to lzero; suc to lsuc)

open import Relation.Binary using (IsEquivalence; Setoid)

open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ )

{- 

Mostly inspired by https://github.com/agda/agda-categories, by Jacques
Carette. 

Instead of using the glorious library, I decided to reinvention of a
wheel to learn Agda and Category theory. I borrowed some ideas and
code from the library when I get stuck in the development. Hence, this
small piece of code is a derived work from the above library.

Here is the LICENSE of the original code.

MIT License

Copyright (c) 2019 Agda Github Community

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

 -}


record Category ℓ ℓₕ ℓₑ : Set (lsuc (ℓ ⊔ ℓₕ ⊔ ℓₑ)) where
  infix 4 _≈_ 
  infixr 6 _∘_ 
  field
    obj  : Set ℓ 
    hom  : obj -> obj -> Set ℓₕ
    _∘_ : {A B C : obj} -> hom B C -> hom A B -> hom A C
    _≈_ : {A B : obj} -> hom A B -> hom A B -> Set ℓₑ

    id   : {a : obj} -> hom a a 
    ∘-assoc : {A B C D : obj}
              -> (f : hom C D) (g : hom B C) (h : hom A B)
              -> f ∘ (g ∘ h) ≈ (f ∘ g) ∘ h
    ∘-identityʳ : {A B : obj} (f : hom A B) -> f ∘ id ≈ f 
    ∘-identityˡ : {A B : obj} (f : hom A B) -> id ∘ f ≈ f 

    ≈-is-equivalence : ∀ {A B} -> IsEquivalence (_≈_ {A} {B})
    ∘-respect-≈ : {A B C : obj} {f f' : hom B C} {g g' : hom A B} -> f ≈ f' -> g ≈ g' -> f ∘ g ≈ f' ∘ g'  

  ≈refl : {A B : obj} {f : hom A B} -> f ≈ f 
  ≈refl = IsEquivalence.refl ≈-is-equivalence

  ≈sym : {A B : obj} -> Relation.Binary.Symmetric (_≈_ {A} {B})
  ≈sym {A} {B} = IsEquivalence.sym (≈-is-equivalence)

  ≈trans : {A B : obj} -> Relation.Binary.Transitive (_≈_ {A} {B})
  ≈trans {A} {B} = IsEquivalence.trans (≈-is-equivalence)


  hom-setoid : {A B : obj} -> Setoid _ _ 
  Setoid.Carrier (hom-setoid  {A} {B}) = hom A B
  Setoid._≈_ hom-setoid = _≈_
  Setoid.isEquivalence hom-setoid = ≈-is-equivalence 

module _ (ℓ ℓₑ : Level) where 
  open Category 
  open import Function.Equality using (_⟶_ ; _⇨_ ; cong; _⟨$⟩_ ) renaming (_∘_ to _∘ₕ_) 
  import Function.Equality
  

  CSetoid : Category (lsuc ℓ ⊔ lsuc ℓₑ) (ℓ ⊔ ℓₑ) (ℓ ⊔ ℓₑ )
  obj CSetoid = Setoid ℓ ℓₑ
  hom CSetoid X Y = X ⟶ Y
  _∘_ CSetoid f g = f ∘ₕ g
  _≈_ CSetoid {A} {B} = Setoid._≈_ (A ⇨ B)
  id CSetoid =  Function.Equality.id
  ∘-assoc CSetoid {D = D} f g h x≈y =  cong f (cong g (cong h x≈y))
  ∘-identityʳ CSetoid f x≈y = cong f x≈y
  ∘-identityˡ CSetoid f x≈y = cong f x≈y
  ≈-is-equivalence CSetoid {A} {B} = Setoid.isEquivalence (A ⇨ B)
  ∘-respect-≈ CSetoid f≈f' g≈g' x≈y = f≈f' (g≈g' x≈y)

module _ {ℓ ℓₕ ℓₑ : Level} (cat : Category ℓ ℓₕ ℓₑ) where 
  open Category cat 

  op : Category ℓ ℓₕ ℓₑ
  obj op = obj
  hom op = λ A -> λ B -> hom B A
  _∘_ op = λ f -> λ g -> g ∘ f 
  _≈_ op = _≈_ 
  id op = id
  ∘-assoc op = λ f g h ->  IsEquivalence.sym (≈-is-equivalence)  (∘-assoc h g f) 
  ∘-identityʳ op = λ f ->  ∘-identityˡ f  
  ∘-identityˡ op = λ f ->  ∘-identityʳ f 
  ≈-is-equivalence op =  ≈-is-equivalence
  ∘-respect-≈ op eq₁ eq₂ = ∘-respect-≈ eq₂ eq₁ 
  
module _ {ℓ ℓₕ ℓₑ ℓ' ℓₕ' ℓₑ'  : Level} (C₁ : Category ℓ ℓₕ ℓₑ) (C₂ : Category ℓ' ℓₕ' ℓₑ') where 
  open Category 
  open Category C₁ renaming (obj to obj₁ ; hom to hom₁ ; _∘_ to _∘₁_; _≈_ to _≈₁_ ; id to id₁)
  open Category C₂ renaming (obj to obj₂ ; hom to hom₂ ; _∘_ to _∘₂_; _≈_ to _≈₂_ ; id to id₂)

  prod : Category (ℓ ⊔ ℓ') (ℓₕ ⊔ ℓₕ') (ℓₑ ⊔ ℓₑ') 
  obj prod = obj₁ × obj₂
  hom prod (A₁ , A₂) (B₁ , B₂) = hom₁ A₁ B₁ × hom₂ A₂ B₂
  _∘_ prod (f₁ , f₂) (g₁ , g₂) =  f₁ ∘₁ g₁ , f₂ ∘₂ g₂
  _≈_ prod (f₁ , f₂) (g₁ , g₂) = f₁ ≈₁ g₁ × f₂ ≈₂ g₂
  id prod = id₁ , id₂
  ∘-assoc prod  (f₁ , f₂) (g₁ , g₂) (h₁ , h₂) = ∘-assoc C₁ f₁ g₁ h₁ , ∘-assoc C₂ f₂ g₂ h₂
  ∘-identityʳ prod (f₁ , f₂) = ∘-identityʳ C₁ f₁ , ∘-identityʳ C₂ f₂
  ∘-identityˡ prod (f₁ , f₂) = ∘-identityˡ C₁ f₁ , ∘-identityˡ C₂ f₂
  IsEquivalence.refl (≈-is-equivalence prod) = IsEquivalence.refl (≈-is-equivalence C₁) , IsEquivalence.refl (≈-is-equivalence C₂) 
  IsEquivalence.sym (≈-is-equivalence prod) (eq₁ , eq₂) = IsEquivalence.sym (≈-is-equivalence C₁) eq₁ , IsEquivalence.sym (≈-is-equivalence C₂) eq₂
  IsEquivalence.trans (≈-is-equivalence prod) (eq₁ , eq₂) (eq₁' , eq₂') = 
    IsEquivalence.trans (≈-is-equivalence C₁) eq₁ eq₁' , IsEquivalence.trans (≈-is-equivalence C₂) eq₂ eq₂'
  ∘-respect-≈ prod (eq₁ , eq₂) (eq₁' , eq₂') = ∘-respect-≈ C₁ eq₁ eq₁' , ∘-respect-≈ C₂ eq₂ eq₂'

module Functor where 

  record Functor {ℓ ℓₕ ℓₑ ℓ' ℓₕ' ℓₑ'} (C : Category ℓ ℓₕ ℓₑ) (D : Category ℓ' ℓₕ' ℓₑ') : Set (ℓ ⊔ ℓ' ⊔ ℓₕ ⊔ ℓₕ' ⊔ ℓₑ ⊔ ℓₑ')  where
    open Category hiding (_≈_)
    open Category D using (_≈_)
    field 
      objMap : obj C -> obj D 
      arrMap : {A B : obj C} -> hom C A B -> hom D (objMap A) (objMap B)

      preserve-id : {A : obj C} -> arrMap (id C {A}) ≈ id D
      preserve-comp : 
        {X Y Z : obj C} ->  
        (f : hom C X Y) (g : hom C Y Z) -> 
        arrMap (_∘_ C g f) ≈ _∘_ D (arrMap g) (arrMap f)

  open Functor public 
  open Category 

  Identity : {ℓ ℓₕ ℓₑ : Level} (C : Category ℓ ℓₕ ℓₑ) -> Functor C C 
  objMap (Identity C) X = X
  arrMap (Identity C) f = f
  preserve-id (Identity C) = IsEquivalence.refl (≈-is-equivalence C) 
  preserve-comp (Identity C) f g = IsEquivalence.refl (≈-is-equivalence C) 

open Functor hiding (Identity) 

module Nat where
  open Category hiding (_∘_ ; _≈_) 
  record Nat {ℓ ℓₕ ℓₑ} {ℓ' ℓₕ' ℓₑ'} {C : Category ℓ ℓₕ ℓₑ} {D : Category ℓ' ℓₕ' ℓₑ'} (F : Functor C D) (G : Functor C D) : Set  (ℓ ⊔ ℓ' ⊔ ℓₕ ⊔ ℓₕ' ⊔ ℓₑ ⊔ ℓₑ') where 
    open Category D using (_∘_; _≈_)
    field 
      η : (X : obj C) -> hom D (objMap F X) (objMap G X)

      -- F X --> G X 
      --  |       |
      --  v       v
      -- F Y --> G Y 
      η-commute : {X Y : C .obj} (f : C .hom X Y) -> arrMap G f ∘ η X ≈ η Y ∘ arrMap F f
  open Nat public
              
  module _ {ℓ ℓₕ ℓₑ ℓ' ℓₕ' ℓₑ' : Level} {C : Category ℓ ℓₕ ℓₑ} {D : Category ℓ'  ℓₕ' ℓₑ'} (F : Functor C D) where 
    open Category D using (_∘_) renaming (≈-is-equivalence to ≈-equiv)

    Identity : Nat F F 
    η (Identity) X = id D
    η-commute (Identity) f = IsEquivalence.trans ≈-equiv (∘-identityʳ D (arrMap F f)) (IsEquivalence.sym ≈-equiv (∘-identityˡ D _))

open Nat hiding (Identity) 

module _ {ℓ ℓₕ ℓₑ ℓ' ℓₕ' ℓₑ' : Level} (C : Category ℓ ℓₕ ℓₑ) (D : Category ℓ' ℓₕ' ℓₑ') where
  open Category hiding (≈refl ; ≈sym)
  open Category C renaming (_∘_ to _∘₁_ ; _≈_ to _≈₁_) hiding (≈refl ; ≈sym)
  open Category D renaming (_∘_ to _∘₂_ ; _≈_ to _≈₂_)
  [_⇒_] : Category (ℓ ⊔ ℓ' ⊔ ℓₕ ⊔ ℓₕ' ⊔ ℓₑ ⊔ ℓₑ') (ℓ ⊔ ℓ' ⊔ ℓₕ ⊔ ℓₕ' ⊔ ℓₑ ⊔ ℓₑ') (ℓ ⊔ ℓₑ')
  obj [_⇒_] = Functor C D
  hom [_⇒_] F G = Nat F G
  η (_∘_ [_⇒_] {F} {G} {H} N₁ N₂) = λ X -> η N₁ X ∘₂ η N₂ X
  η-commute (_∘_ [_⇒_] {F} {G} {H} N₁ N₂) {X} {Y} f = 
    begin
      arrMap H f ∘₂ η N₁ X ∘₂ η N₂ X 
    ≈⟨  ∘-assoc D _ _ _ ⟩
      (arrMap H f ∘₂ η N₁ X) ∘₂ η N₂ X 
    ≈⟨ ∘-respect-≈ D (η-commute N₁ f) ≈refl ⟩ 
      (η N₁ Y ∘₂ arrMap G f) ∘₂ η N₂ X 
    ≈⟨ ≈sym (∘-assoc D _ _ _) ⟩ 
      η N₁ Y ∘₂ (arrMap G f ∘₂ η N₂ X)    
    ≈⟨  ∘-respect-≈ D ≈refl (η-commute N₂ f)  ⟩ 
      η N₁ Y ∘₂ (η N₂ Y ∘₂ arrMap F f)    
    ≈⟨ ∘-assoc D _ _ _ ⟩ 
      (η N₁ Y ∘₂ η N₂ Y) ∘₂ arrMap F f
    ∎
    where
      open import Relation.Binary.Reasoning.Setoid (Category.hom-setoid D {objMap F X} {objMap H Y})      


  _≈_ [_⇒_] N₁ N₂ = ∀ X -> η N₁ X ≈₂ η N₂ X 
  η (id [_⇒_]) _ = id D
  η-commute (id [_⇒_]) f =  IsEquivalence.trans (≈-is-equivalence D) (∘-identityʳ D _) (IsEquivalence.sym (≈-is-equivalence D) (∘-identityˡ D _))
  ∘-assoc [_⇒_] N₁ N₂ N₃ = λ X -> ∘-assoc D _ _ _
  ∘-identityʳ [_⇒_] N = λ X -> ∘-identityʳ D _
  ∘-identityˡ [_⇒_] N = λ X -> ∘-identityˡ D _
  IsEquivalence.refl (≈-is-equivalence [_⇒_]) = λ X -> IsEquivalence.refl (≈-is-equivalence D)
  IsEquivalence.sym (≈-is-equivalence [_⇒_]) = λ hEq X -> IsEquivalence.sym (≈-is-equivalence D) (hEq X)
  IsEquivalence.trans (≈-is-equivalence [_⇒_]) = λ hEq₁ hEq₂ X -> IsEquivalence.trans (≈-is-equivalence D) (hEq₁ X) (hEq₂ X)
  ∘-respect-≈ [_⇒_] heq heq' = λ X -> ∘-respect-≈ D (heq X) (heq' X)

Profunctor : {ℓ ℓₕ ℓₑ : Level} (o e : Level) (C : Category ℓ ℓₕ ℓₑ) -> Set (ℓ ⊔ ℓₕ ⊔ ℓₑ ⊔ lsuc o ⊔ lsuc e)
Profunctor {ℓ} {ℓₕ} {ℓₑ} o e C = Functor (prod (op C) C) (CSetoid o e)
