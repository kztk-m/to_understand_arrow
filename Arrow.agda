{-# OPTIONS --without-K #-}

{-
MIT License

Copyright (c) 2022 Kazutaka Matsuda

Permission is hereby granted, free of charge, to any person obtaining
a copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be
included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

-}

open import Level renaming (zero to lzero; suc to lsuc)

open import Relation.Binary using (IsEquivalence; Setoid)

open import Category 
open Category.Functor
open Category.Nat


open import Function.Equality using (_⟶_)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ )
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (_×ₛ_)
open import Data.Product.Function.NonDependent.Setoid renaming (_×-⟶_ to _×ₛ⃑_)

-- To understand Proposition 4.2 in the paper: 
-- "Categorical semantics for arrows" by B. Jacobs, C. Heunen, and I. Hasuo.

variable 
  ℓ ℓₕ ℓₑ : Level

module _ (C : Category ℓ ℓₕ ℓₑ) where 
  open Category.Category C
  import Function.Equality 

  Hom : Profunctor ℓₕ ℓₑ C 
  objMap Hom (X , Y) = hom-setoid {X} {Y}
  arrMap Hom (f , g) = record { _⟨$⟩_ = λ h → g ∘ h ∘ f ; cong =  λ i≈j -> ∘-respect-≈ ≈refl (∘-respect-≈ i≈j ≈refl) } 

  preserve-id Hom {A , B} {h} {k} h≈k = 
    begin 
      id ∘ h ∘ id 
    ≈⟨ ∘-identityˡ _  ⟩ 
      h ∘ id 
    ≈⟨ ∘-identityʳ _ ⟩ 
      h 
    ≈⟨ h≈k ⟩ 
      k 
    ∎
    where
      open import Relation.Binary.Reasoning.Setoid (hom-setoid {A} {B})      
    
  preserve-comp Hom {X} {Y} {Z} (f₁ , f₂) (g₁ , g₂) {h} {k} h≈k = 
   begin 
    (g₂ ∘ f₂) ∘ h ∘ f₁ ∘ g₁ 
   ≈⟨  ≈sym (∘-assoc g₂ _ _) ⟩ 
     g₂ ∘ (f₂ ∘ h ∘ f₁ ∘ g₁)
   ≈⟨ ∘-respect-≈ ≈refl (∘-respect-≈ ≈refl (∘-assoc _ _ _)) ⟩ 
     g₂ ∘ f₂ ∘ (h ∘ f₁) ∘ g₁
   ≈⟨ ∘-respect-≈ ≈refl (∘-assoc _ _ _) ⟩ 
     g₂ ∘ (f₂ ∘ h ∘ f₁) ∘ g₁
   ≈⟨ ∘-respect-≈ ≈refl (∘-respect-≈ ( Function.Equality.cong (arrMap Hom (f₁ , f₂)) h≈k) ≈refl) ⟩
     g₂ ∘ (f₂ ∘ k ∘ f₁) ∘ g₁
   ∎ 
    where
      open import Relation.Binary.Reasoning.Setoid (hom-setoid {proj₁ Z} {proj₂ Z})      

×ₛ-assoc : {a b : Level} {S T U : Setoid a b} -> (S ×ₛ T) ×ₛ U ⟶ S ×ₛ (T ×ₛ U)
×ₛ-assoc = record { _⟨$⟩_ = λ { ((s , t) , u) -> (s , (t , u))}  ; cong =  λ { ((eq₁ , eq₂) , eq₃) -> (eq₁ , (eq₂ , eq₃)) } } 


record Arrow {ℓ} {ℓₕ} {ℓₑ} (C : Category ℓ ℓₕ ℓₑ) : Set (ℓ ⊔ lsuc (ℓₕ ⊔ ℓₑ))  where 
  open Category.Category C
  open Function.Equality using (_⟨$⟩_ ; Π )  

  open Category.Category (CSetoid ℓₕ ℓₑ) using () renaming (id to idₕ ; _≈_ to _≈ₕ_ ; _∘_ to _∘ₕ_) 

  field 
    ArrF : Profunctor ℓₕ ℓₑ C 
    I : Nat (Hom C) ArrF

  Arr : (X Y : obj) -> Setoid ℓₕ ℓₑ
  Arr = λ (X Y : obj) -> objMap ArrF (X , Y)

  ArrMap : {X X' Y Y' : obj} -> hom X' X -> hom Y Y' -> Arr X Y ⟶ Arr X' Y'
  ArrMap f g = arrMap ArrF (f , g) 

  ArrMap$ : {X X' Y Y' : obj} -> hom X' X -> hom Y Y' -> Setoid.Carrier (Arr X Y) -> Setoid.Carrier (Arr X' Y') 
  ArrMap$ f g h = arrMap ArrF (f , g) ⟨$⟩ h 

  field 
    comp : ∀ {X Y Z : obj} -> (Arr X Y ×ₛ Arr Y Z) ⟶ (Arr X Z)

  _>>>_ : ∀ {X Y Z : obj} -> Setoid.Carrier (Arr X Y) -> Setoid.Carrier (Arr Y Z) -> Setoid.Carrier (Arr X Z) 
  _>>>_ arr1 arr2 = comp ⟨$⟩ (arr1 , arr2) 

  arr :  {X Y : obj} -> hom-setoid {X} {Y} ⟶ Arr X Y 
  arr {X} {Y} = η I (X , Y)

  arr$ : {X Y : obj} -> Setoid.Carrier (hom-setoid {X} {Y}) -> Setoid.Carrier (Arr X Y)
  arr$ h = arr ⟨$⟩ h

  right-id-inv : {X Y : obj} -> Arr X Y ⟶ Arr X Y ×ₛ Arr Y Y 
  right-id-inv = record { _⟨$⟩_ = λ h -> h , arr$ id ; cong = λ i≈j → i≈j , Setoid.refl (Arr _ _) }

  left-id-inv : {X Y : obj} -> Arr X Y ⟶ Arr X X ×ₛ Arr X Y 
  left-id-inv = record { _⟨$⟩_ = λ h -> arr$ id , h  ; cong = λ i≈j → Setoid.refl (Arr _ _) , i≈j }


  field 
    monoid-assoc : 
      {X Y Z W : obj}
      -> comp {X} {Z} {W} ∘ₕ (comp {X} {Y} {Z} ×ₛ⃑ idₕ) 
         ≈ₕ comp ∘ₕ (idₕ ×ₛ⃑ comp) ∘ₕ ×ₛ-assoc 
    monoid-identityʳ : {X Y : obj} -> comp {X} {Y} {Y} ∘ₕ right-id-inv ≈ₕ idₕ
    monoid-identityˡ : {X Y : obj} -> comp {X} {X} {Y} ∘ₕ left-id-inv ≈ₕ idₕ 

  field 
    comp-natural₁ : 
      {X X' Y Z : obj} 
      -> (f : hom X' X) 
      -> comp {X'} {Y} {Z} ∘ₕ ArrMap f id ×ₛ⃑ idₕ ≈ₕ ArrMap f id ∘ₕ comp

    comp-natural₂ : 
      {X Y Z Z' : obj}
      -> (f : hom Z Z') 
      -> comp {X} {Y} {Z'} ∘ₕ idₕ ×ₛ⃑ ArrMap id f ≈ₕ ArrMap id f ∘ₕ comp

    comp-dinatural :
      {X Y Y' Z : obj}
      -> (f : hom Y Y') 
      -> comp {X} {Y'} {Z} ∘ₕ ArrMap id f ×ₛ⃑ idₕ 
         ≈ₕ comp {X} {Y} {Z} ∘ₕ idₕ ×ₛ⃑ ArrMap f id 

  infix 4 _≈ₐ_
  _≈ₐ_ : {X Y : obj} -> Setoid.Carrier (Arr X Y) -> Setoid.Carrier (Arr X Y) -> Set _ 
  _≈ₐ_ {X} {Y} = Setoid._≈_ (Arr X Y) 

  module Properties where 
    >>>-natural₁ :
      {X X' Y Z : obj} 
      -> (a₁ : Setoid.Carrier (Arr X Y)) (a₂ : Setoid.Carrier (Arr Y Z))
      -> (f : hom X' X) 
      -> ArrMap$ f id a₁ >>> a₂ ≈ₐ ArrMap$ f id (a₁ >>> a₂)
    >>>-natural₁ {X} {X'} {Y} {Z} a₁ a₂ f = 
        comp-natural₁ f {a₁ , a₂} {a₁ , a₂} (Setoid.refl (Arr X Y ×ₛ Arr Y Z))

    >>>-natural₂ : 
      {X Y Z Z' : obj}
      -> (a₁ : Setoid.Carrier (Arr X Y)) (a₂ : Setoid.Carrier (Arr Y Z))
      -> (f : hom Z Z') 
      -> a₁ >>> ArrMap$ id f a₂ ≈ₐ ArrMap$ id f (a₁ >>> a₂)
    >>>-natural₂ {X} {Y} {Z} {Z'} a₁ a₂ f = 
      comp-natural₂ f {a₁ , a₂} {a₁ , a₂} (Setoid.refl (Arr X Y ×ₛ Arr Y Z))

    >>>-dinatural : 
      {X Y Y' Z : obj}
      -> (a₁ : Setoid.Carrier (Arr X Y)) (a₂ : Setoid.Carrier (Arr Y' Z))
      -> (f : hom Y Y') 
      -> ArrMap$ id f a₁ >>> a₂ ≈ₐ (a₁ >>> ArrMap$ f id a₂)
    >>>-dinatural {X} {Y} {Y'} {Z} a₁ a₂ f = 
      comp-dinatural f {a₁ , a₂} {a₁ , a₂} (Setoid.refl (Arr X Y ×ₛ Arr Y' Z))

    >>>-assoc : 
      {X Y Z W : obj} 
      -> (a : Setoid.Carrier (Arr X Y))
      -> (b : Setoid.Carrier (Arr Y Z))
      -> (c : Setoid.Carrier (Arr Z W))
      -> (a >>> b) >>> c ≈ₐ a >>> (b >>> c) 
    >>>-assoc a b c =  monoid-assoc {_} {_} {_} {_} {(a , b) , c} {(a , b) , c} (Setoid.refl ((Arr _ _ ×ₛ Arr _ _) ×ₛ Arr _ _))

    >>>-identityˡ : 
      {X Y : obj}
      -> (a : Setoid.Carrier (Arr X Y))
      -> arr$ id >>> a ≈ₐ a 
    >>>-identityˡ a =  monoid-identityˡ a≈a 
      where
        a≈a : a ≈ₐ a
        a≈a = Setoid.refl (Arr _ _)

    >>>-identityʳ : 
      {X Y : obj}
      -> (a : Setoid.Carrier (Arr X Y))
      -> a >>> arr$ id ≈ₐ a
    >>>-identityʳ a =  monoid-identityʳ a≈a 
      where
        a≈a : a ≈ₐ a
        a≈a = Setoid.refl (Arr _ _)

    >>>-respect-≈ₐ :
      {X Y Z : obj} 
      -> {a a' : Setoid.Carrier (Arr X Y)}
      -> {b b' : Setoid.Carrier (Arr Y Z)}
      -> a ≈ₐ a' 
      -> b ≈ₐ b' 
      -> a >>> b ≈ₐ a' >>> b' 
    >>>-respect-≈ₐ a≈a' b≈b' = Π.cong comp (a≈a' , b≈b') 

    arr-natural : 
      {X X' Y Y' : obj}
      -> (f : hom X' X) 
      -> (g : hom Y Y')
      -> (h : hom X Y) 
      -> ArrMap$ f g (arr$ h) ≈ₐ arr$ (g ∘ h ∘ f) 
    arr-natural f g h =  
      let h≈h : h ≈ h 
          h≈h = Setoid.refl (hom-setoid) 
      in η-commute I (f , g) h≈h  

      

    arr-functorial :
      {X Y Z : obj} 
      -> (f : hom X Y) 
      -> (g : hom Y Z) 
      -> arr$ (g ∘ f) ≈ₐ arr$ f >>> arr$ g 
    {-
    arr f >>> arr g 
    = { naturality of arr }
      A(id, f) (arr id) >>> arr g 
    = { dinaturality of >>> }
      arr id >>> A(f, id) (arr g)
    = { arr id >>> a = a }
      A(f, id) (arr g)
    = { naturality of arr }
      arr (id . g . f) 
    = { id }
      arr (g . f)
    -}
    arr-functorial {X} {Y} {Z} f g =  
      begin
        arr$ (g ∘ f) 
      ≈⟨ arr-respect-≈ (≈sym (∘-identityˡ _)) ⟩ 
        arr$ (id ∘ g ∘ f) 
      ≈⟨ Setoid.sym (Arr _ _) (arr-natural f id g) ⟩ 
        ArrMap$ f id (arr$ g) 
      ≈⟨ Setoid.sym (Arr _ _) (>>>-identityˡ _) ⟩ 
        arr$ id >>> ArrMap$ f id (arr$ g)
      ≈⟨ Setoid.sym (Arr _ _) (>>>-dinatural _ _ f) ⟩ 
        ArrMap$ id f (arr$ id) >>> arr$ g
      ≈⟨  >>>-respect-≈ₐ (arr-natural id f id) (Setoid.refl (Arr _ _)) ⟩ 
        arr$ (f ∘ id ∘ id) >>> arr$ g 
      ≈⟨ >>>-respect-≈ₐ (arr-respect-≈ (≈trans (∘-respect-≈ ≈refl (∘-identityʳ id)) (∘-identityʳ f))) (Setoid.refl (Arr _ _)) ⟩ 
        arr$ f >>> arr$ g 
      ∎    
      where
        open import Relation.Binary.Reasoning.Setoid (Arr X Z)

        arr-respect-≈ : 
          {X Y : obj} 
          -> {g h : hom X Y} 
          -> g ≈ h -> arr$ g ≈ₐ arr$ h 
        arr-respect-≈ g≈h = Π.cong arr g≈h
    
