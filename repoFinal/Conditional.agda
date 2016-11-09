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

 