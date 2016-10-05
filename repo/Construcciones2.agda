open import Categories

module Construcciones2 where

open import Library hiding (_×_ ; swap; _+_)

open import Categories.Products
open import Categories.Terminal
open import Categories.Iso
open import Categories.Initial
open import Categories.Coproducts
open import Construcciones

--------------------------------------------------

module SetsStructure {l : Level} where

 open import Categories.Sets


 {- Probar que la categoría Sets tiene objeto inicial y coproductos -}
 ZeroSet : Initial Sets ⊥
 ZeroSet = init (λ {X} → λ ()) (ext (λ ()))

 data Either {l : Level} (A B : Set l) : Set l  where
   Left : A → Either A B
   Right : B → Either A B

 case : ∀{l} {A B C : Set l} → (A → C) → (B → C) → Either A B → C
 case f g (Left x) = f x
 case f g (Right x) = g x

 

 SetsHasCoproducts : ∀{l} → Coproducts (Sets {l})
 SetsHasCoproducts = coproduct Either 
                               Left
                               Right 
                               case 
                               refl 
                               refl 
                               (λ {A} {B} {C} {f} {g} {h} hf hg → ext (λ { (Left x) → cong-app hf x ; (Right y) → cong-app hg y }))



--------------------------------------------------
module InitialIso {a}{b}(C : Cat {a}{b}) where

 open Cat C
 open Initial

 {- el morfismo universal del objeto inicial a sí mismo es la identidad -}

 init-iden : (I : Obj){init : Initial C I}
           → i init {I} ≅ iden {I}
 init-iden I {init = init₁} = law init₁


--------------------------------------------------
 {- Probar que un objeto terminal es inicial en la categoría dual y viceversa -}
 TerminalInitialDuality : {X : Obj} → Terminal C X → Initial (C Op) X
 TerminalInitialDuality (term t law) = init t law

 InitialTerminalDuality : {X : Obj} → Initial C X → Terminal (C Op) X
 InitialTerminalDuality (init i law) = term i law

--------------------------------------------------

 open TerminalIso
 
 {- Probar que dos objetos iniciales son necesariamente isomorfos *usando dualidad* -}
 InitialIso : (I I' : Obj)
            → (p : Initial C I)
            → (q : Initial C I')
            → Iso C (i p {I'})
 InitialIso I I' p q = iso-op (TerminalIso (C Op) 
                                           I 
                                           I' 
                                           (InitialTerminalDuality p) 
                                           (InitialTerminalDuality q))  
                 
                

--------------------------------------------------------
-- Probar que los coproductos son productos en la categoría dual
ProductCoproductDuality : ∀{a}{b}{C : Cat {a}{b}}
                        → Products C
                        → Coproducts (C Op)
ProductCoproductDuality (prod _×_ 
                              π₁ π₂
                              ⟨_,_⟩ 
                              law1 
                              law2 
                              law3) = coproduct _×_ 
                                                π₁ 
                                                π₂ 
                                                ⟨_,_⟩ 
                                                law1 
                                                law2 
                                                law3

CoproductProductDuality : ∀{a}{b}{C : Cat {a}{b}}
                        → Coproducts C
                        → Products (C Op)
CoproductProductDuality (coproduct _+_ inl inr [_,_] law1 law2 law3) = prod _+_ inl inr [_,_] law1 law2 law3

--------------------------------------------------
module CoproductIso {a}{b}(C : Cat {a}{b})  where

  open Coproducts

  open Cat C

  open ProductIso (C Op) renaming (ProductIso to piso)

  {- Probar que los coproductos son únicos hasta un isomorfismo *usando dualidad* -}
  CoproductIso : ∀{A B}(X Y : Coproducts C) → Iso C ([_,_] X {A} {B} (inl Y) (inr Y))
  CoproductIso X Y = iso-op (piso (CoproductProductDuality X) (CoproductProductDuality Y))

--------------------------------------------------

module CoproductMorphisms {a}{b}{C : Cat {a}{b}}{cp : Coproducts C} where

  open Cat C
  open Coproducts cp

  {- Definir el siguiente morfismo -}
  plus : ∀{A B C D}(f : Hom A B)(g : Hom C D) → Hom (A + C) (B + D)
  plus f g = [(inl ∙ f) , (inr ∙ g)]

  {- Probar las siguentes propiedades -}

  idplus : ∀{A B} → plus (iden {A}) (iden {B}) ≅ iden {A + B}
  idplus {A} {B} = proof plus iden iden 
                        ≅⟨ refl ⟩
                        [(inl ∙ iden) , (inr ∙ iden)]
                        ≅⟨ cong₂ [_,_] idr idr ⟩
                        [ inl , inr ]
                        ≅⟨ sym (law3 idl idl) ⟩
                        iden ∎

  idcomp :  ∀{A B C D E F}
         → (f : Hom B C)(g : Hom A B)
         → (h : Hom E F)(i : Hom D E)
         → plus (f ∙ g) (h ∙ i) ≅ plus f h ∙ plus g i
  idcomp  f g h i = proof plus (f ∙ g) (h ∙ i) 
                          ≅⟨ refl ⟩
                          [(inl ∙ (f ∙ g)) , (inr ∙ (h ∙ i))] 
                          ≅⟨ sym (law3 
                                 (proof 
                                 ([ inl ∙ f , inr ∙ h ] ∙ [ inl ∙ g , inr ∙ i ]) ∙ inl 
                                 ≅⟨ ass ⟩
                                 [ inl ∙ f , inr ∙ h ] ∙ ([ inl ∙ g , inr ∙ i ] ∙ inl)
                                 ≅⟨ cong₂ _∙_ refl law1 ⟩
                                 [ inl ∙ f , inr ∙ h ] ∙ inl ∙ g
                                 ≅⟨ sym ass ⟩
                                 ([ inl ∙ f , inr ∙ h ] ∙ inl) ∙ g
                                 ≅⟨ cong₂ _∙_ law1 refl ⟩
                                 (inl ∙ f) ∙ g
                                 ≅⟨ ass ⟩
                                 inl ∙ f ∙ g ∎) 
                                 (proof 
                                 ([ inl ∙ f , inr ∙ h ] ∙ [ inl ∙ g , inr ∙ i ]) ∙ inr 
                                 ≅⟨ ass ⟩
                                 [ inl ∙ f , inr ∙ h ] ∙ [ inl ∙ g , inr ∙ i ] ∙ inr
                                 ≅⟨ cong₂ _∙_ refl law2 ⟩
                                 [ inl ∙ f , inr ∙ h ] ∙ inr ∙ i
                                 ≅⟨ sym ass ⟩
                                 ([ inl ∙ f , inr ∙ h ] ∙ inr) ∙ i
                                 ≅⟨ cong₂ _∙_ law2 refl ⟩
                                 (inr ∙ h) ∙ i
                                 ≅⟨ ass ⟩
                                 inr ∙ h ∙ i ∎)) ⟩
                          [(inl ∙ f) , (inr ∙ h)] ∙ [(inl ∙ g) , (inr ∙ i)]
                          ≅⟨ refl ⟩
                          plus f h ∙ plus g i ∎

   {- Probar que _+_ junto con plus definen unFunctor C xC C → C -}

  open import Functors
  open import Categories.ProductCat

  plusCoProdIsFunctor : Fun (C ×C C) C
  plusCoProdIsFunctor = functor (λ {(x , y) → x + y}) 
                                (λ {(f , g) → plus f g}) 
                                idplus 
                                (λ { {X} {Y} {Z} {(f , g)} {(h , i)} → idcomp f h g i }) 

module Intercambio {a}{b}{C : Cat {a}{b}}{cp : Coproducts C}{p : Products C} where

  open Cat C
  open Coproducts cp
  open Products p renaming (law1 to lawp1 ; law2 to lawp2 ; law3 to lawp3)


   {- intercambio entre poducto y coproducto -}

  intercambio : ∀{A B C D}
         → (f : Hom A C)(g : Hom B C)
         → (h : Hom A D)(k : Hom B D)
         → ⟨ [ f , g ] , [ h , k ] ⟩ ≅ [ ⟨ f , h ⟩ , ⟨ g , k ⟩ ]
  intercambio f g h k = proof ⟨ [ f , g ] , [ h , k ] ⟩ 
                              ≅⟨  law3 (lawp3 (proof π₁ ∙ ⟨ [ f , g ] , [ h , k ] ⟩ ∙ inl 
                                                     ≅⟨ sym ass ⟩
                                                     (π₁ ∙ ⟨ [ f , g ] , [ h , k ] ⟩) ∙ inl
                                                     ≅⟨ cong₂ _∙_ lawp1 refl ⟩
                                                     [ f , g ] ∙ inl
                                                     ≅⟨ law1 ⟩
                                                     f ∎) 
                                              (proof π₂ ∙ ⟨ [ f , g ] , [ h , k ] ⟩ ∙ inl 
                                                     ≅⟨ sym ass ⟩
                                                     (π₂ ∙ ⟨ [ f , g ] , [ h , k ] ⟩) ∙ inl
                                                     ≅⟨ cong₂ _∙_ lawp2 refl ⟩
                                                     [ h , k ] ∙ inl
                                                     ≅⟨ law1 ⟩
                                                     h ∎)) 
                                       (lawp3 (proof π₁ ∙ ⟨ [ f , g ] , [ h , k ] ⟩ ∙ inr 
                                                     ≅⟨ sym ass ⟩
                                                     (π₁ ∙ ⟨ [ f , g ] , [ h , k ] ⟩) ∙ inr
                                                     ≅⟨ cong₂ _∙_ lawp1 refl ⟩
                                                     [ f , g ] ∙ inr
                                                     ≅⟨ law2 ⟩
                                                     g ∎) 
                                              (proof π₂ ∙ ⟨ [ f , g ] , [ h , k ] ⟩ ∙ inr
                                                     ≅⟨ sym ass ⟩
                                                      (π₂ ∙ ⟨ [ f , g ] , [ h , k ] ⟩) ∙ inr
                                                     ≅⟨ cong₂ _∙_ lawp2 refl ⟩
                                                     [ h , k ] ∙ inr
                                                     ≅⟨ law2 ⟩
                                                     k ∎)) ⟩
                              [ ⟨ f , h ⟩ , ⟨ g , k ⟩ ] ∎
