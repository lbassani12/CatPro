open import Categories
open import Categories.Products
open import Categories.Coproducts
open import Categories.Initial
open import Categories.Terminal

module Conditional {a}{b}{C : Cat {a}{b}}
                         (hasProducts : Products C)
                         (hasCoproducts : Coproducts C)
                         (I : Cat.Obj C)
                         (hasInitial : Initial C I)
                         (T : Cat.Obj C)
                         (hasTerminal : Terminal C T)
      where

open import Library hiding (_×_ ; swap; _+_)


open import Categories.Distributive hasProducts hasCoproducts I hasInitial

open Cat C

open Coproducts hasCoproducts
open import Categories.Coproducts.Properties hasCoproducts

open Products hasProducts
open import Categories.Products.Properties hasProducts

open Initial hasInitial

Bool = T + T

true : Hom T Bool
true = inl

false : Hom T Bool
false = inr

not : Hom Bool Bool
not = [ false , true ]

unit : ∀{A} → Hom (A × T) A
unit = π₁

module CisDistributive (isDistr : Distributive)  where  

 open Distributive isDistr

 cond : ∀{A} → Hom A Bool → Hom A (A + A) 
 cond p = copair unit unit ∙ distr ∙ ⟨ iden , p ⟩
 _⇒_,_ : ∀{A B} → Hom A Bool → Hom A B → Hom A B → Hom A B 
 p ⇒ f , g = [ f , g ] ∙ cond p

 leftDistr : ∀{A B D} → (p : Hom A Bool) → (f : Hom A B) → (g : Hom A B) → (h : Hom B D) → h ∙ (p ⇒ f , g) ≅ p ⇒ (h ∙ f) , (h ∙ g)
 leftDistr p f g h = proof h ∙ (p ⇒ f , g)
                           ≅⟨ sym ass ⟩
                           (h ∙ [ f , g ]) ∙ cond p
                           ≅⟨ congl fusionCo ⟩
                           [ h ∙ f , h ∙ g ] ∙ cond p
                           ≅⟨ refl ⟩ 
                           (p ⇒ h ∙ f , (h ∙ g)) ∎

 rightDistr : ∀{A B D} → (p : Hom A Bool) → (f : Hom A B) → (g : Hom A B) → (h : Hom D A) → (p ⇒ f , g) ∙ h ≅ (p ∙ h) ⇒ (f ∙ h) , (g ∙ h)
 rightDistr p f g h = proof p ⇒ f , g ∙ h
                            ≅⟨ ass ⟩
                            [ f , g ] ∙ cond p ∙ h
                            ≅⟨ congr (ass) ⟩
                            [ f , g ] ∙ copair unit unit ∙ (distr ∙ ⟨ iden , p ⟩) ∙ h
                            ≅⟨ congr (congr ass) ⟩
                            [ f , g ] ∙ copair unit unit ∙ distr ∙ ⟨ iden , p ⟩ ∙ h
                            ≅⟨ congr (congr (congr fusion)) ⟩
                            [ f , g ] ∙ copair unit unit ∙ distr ∙ ⟨ iden ∙ h , p ∙ h ⟩
                            ≅⟨ congr (congr (congr (cong₂ ⟨_,_⟩ (symIden h) (sym idl)))) ⟩
                            [ f , g ] ∙ copair unit unit ∙ distr ∙ ⟨ h ∙ iden , iden ∙ p ∙ h ⟩
                            ≅⟨ congr (congr (congr (sym fusion-pair))) ⟩
                            [ f , g ] ∙
                              copair unit unit ∙ distr ∙ pair h iden ∙ ⟨ iden , p ∙ h ⟩ 
                            ≅⟨ congr (congr (congr (congl (cong₂ pair refl (sym iden-cop))))) ⟩
                            [ f , g ] ∙
                              copair unit unit ∙
                              distr ∙ pair h (copair iden iden) ∙ ⟨ iden , p ∙ h ⟩
                            ≅⟨ congr (congr (sym ass)) ⟩
                            [ f , g ] ∙
                              copair unit unit ∙
                              (distr ∙ pair h (copair iden iden)) ∙ ⟨ iden , p ∙ h ⟩
                            ≅⟨ congr (congr (congl (natDistr h iden iden))) ⟩
                            [ f , g ] ∙
                              copair unit unit ∙
                              (copair (pair h iden) (pair h iden) ∙ distr) ∙ ⟨ iden , p ∙ h ⟩
                            ≅⟨ congr (sym ass) ⟩
                            [ f , g ] ∙
                              (copair unit unit ∙ copair (pair h iden) (pair h iden) ∙ distr) ∙
                              ⟨ iden , p ∙ h ⟩
                            ≅⟨ congr (congl (sym ass)) ⟩
                            [ f , g ] ∙
                              ((copair unit unit ∙ copair (pair h iden) (pair h iden)) ∙ distr) ∙
                              ⟨ iden , p ∙ h ⟩
                            ≅⟨ congr (congl (congl (sym comp-cop))) ⟩
                            [ f , g ] ∙
                              (copair (unit ∙ pair h iden) (unit ∙ pair h iden) ∙ distr) ∙
                              ⟨ iden , p ∙ h ⟩
                            ≅⟨ congr (congl (congl (cong₂ copair π₁-pair π₁-pair))) ⟩
                            [ f , g ] ∙ (copair (h ∙ unit) (h ∙ unit) ∙ distr) ∙ ⟨ iden , p ∙ h ⟩
                            ≅⟨ congr (congl (congl comp-cop)) ⟩
                            [ f , g ] ∙
                              ((copair h h ∙ copair unit unit) ∙ distr) ∙ ⟨ iden , p ∙ h ⟩
                            ≅⟨ congr (congl ass) ⟩
                            [ f , g ] ∙
                              (copair h h ∙ copair unit unit ∙ distr) ∙ ⟨ iden , p ∙ h ⟩
                            ≅⟨ congr ass ⟩
                            [ f , g ] ∙
                              copair h h ∙ (copair unit unit ∙ distr) ∙ ⟨ iden , p ∙ h ⟩
                            ≅⟨ congr (congr ass) ⟩
                            [ f , g ] ∙
                              copair h h ∙ copair unit unit ∙ distr ∙ ⟨ iden , p ∙ h ⟩
                            ≅⟨ congr (congr refl) ⟩
                            [ f , g ] ∙
                              copair h h ∙ cond (p ∙ h)
                            ≅⟨ sym ass ⟩
                            ([ f , g ] ∙ copair h h) ∙ cond (p ∙ h)
                            ≅⟨ congl fusion-cop ⟩
                            [ f ∙ h , g ∙ h ] ∙ cond (p ∙ h)

                            ≅⟨ refl ⟩
                            (p ∙ h) ⇒ f ∙ h , (g ∙ h) ∎

 lemma1 : [ iden , iden ] ∙ distr ≅ iden
 lemma1 = proof [ iden , iden ] ∙ distr
                ≅⟨ {!!} ⟩
                {!!}
                ≅⟨ {!!} ⟩
                {!!}
                ≅⟨ {!!} ⟩
                {!!}
                ≅⟨ {!!} ⟩
                iden ∎
 same : ∀{A B} → (p : Hom A Bool) → (f : Hom A B) → p ⇒ f , f ≅ f
 same p f = proof p ⇒ f , f
                  ≅⟨ refl ⟩
                  [ f , f ] ∙ cond p
                  ≅⟨ sym ass ⟩
                  ([ f , f ] ∙ copair unit unit) ∙ distr ∙ ⟨ iden , p ⟩
                  ≅⟨ congl fusion-cop ⟩
                  [ f ∙ unit , f ∙ unit ] ∙ distr ∙ ⟨ iden , p ⟩
                  ≅⟨ congl (cong₂ [_,_] (sym π₁-pair) (sym π₁-pair)) ⟩
                  [ unit ∙ pair f iden , unit ∙ pair f iden ] ∙ distr ∙ ⟨ iden , p ⟩
                  ≅⟨ congl (sym fusionCo) ⟩
                  (unit ∙ [ pair f iden , pair f iden ]) ∙ distr ∙ ⟨ iden , p ⟩
                  ≅⟨ ass ⟩
                  unit ∙ [ pair f iden , pair f iden ] ∙ distr ∙ ⟨ iden , p ⟩
                  ≅⟨ congr (congl (cong₂ [_,_] (sym idl) (sym idl))) ⟩
                  unit ∙
                    [ iden ∙ pair f iden , iden ∙ pair f iden ] ∙ distr ∙ ⟨ iden , p ⟩
                  ≅⟨ congr (congl (sym fusion-cop)) ⟩
                  unit ∙
                    ([ iden , iden ] ∙ copair (pair f iden) (pair f iden)) ∙
                    distr ∙ ⟨ iden , p ⟩
                  ≅⟨ congr ass ⟩
                  unit ∙
                    [ iden , iden ] ∙
                    copair (pair f iden) (pair f iden) ∙ distr ∙ ⟨ iden , p ⟩
                  ≅⟨ congr (congr (sym ass)) ⟩
                  unit ∙
                    [ iden , iden ] ∙
                    (copair (pair f iden) (pair f iden) ∙ distr) ∙ ⟨ iden , p ⟩
                  ≅⟨ congr (congr (congl (sym (natDistr f iden iden)))) ⟩
                  unit ∙
                    [ iden , iden ] ∙
                    (distr ∙ pair f (copair iden iden)) ∙ ⟨ iden , p ⟩
                  ≅⟨ congr (congr (congl (congr (cong₂ pair refl iden-cop)))) ⟩
                  unit ∙ [ iden , iden ] ∙ (distr ∙ pair f iden) ∙ ⟨ iden , p ⟩
                  ≅⟨ congr (congr ass) ⟩
                  unit ∙ [ iden , iden ] ∙ distr ∙ pair f iden ∙ ⟨ iden , p ⟩
                  ≅⟨ congr (sym ass) ⟩
                  unit ∙ ([ iden , iden ] ∙ distr) ∙ pair f iden ∙ ⟨ iden , p ⟩
                  ≅⟨ {!!} ⟩
                  {!!}
                  ≅⟨ {!!} ⟩ 
                  f ∎ 
