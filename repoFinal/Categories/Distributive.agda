open import Categories
open import Categories.Products
open import Categories.Coproducts
open import Categories.Initial

module Categories.Distributive {a}{b}{C : Cat {a}{b}}
                               (hasProducts : Products C)
                               (hasCoproducts : Coproducts C)
                               (I : Cat.Obj C)
                               (hasInitial : Initial C I)
       where

open import Library hiding (_×_ ; _+_)
open import Categories.Iso public

open Cat C

open Coproducts hasCoproducts
open import Categories.Coproducts.Properties hasCoproducts

open Products hasProducts
open import Categories.Products.Properties hasProducts

open Initial hasInitial

--------------------------------------------------

undistr : ∀{X Y Z} → Hom (X × Y + X × Z) (X × (Y + Z))
undistr = [ pair iden inl , pair iden inr ]

-- natUnDistR : pair f (copair g h) ∙ undistr ≅ undistr ∙ copair (pair f g) (pair f h)

--copair : ∀{X Y Z W}(f : Hom X Z)(g : Hom Y W) → Hom (X + Y) (Z + W)
--copair f g = [ inl ∙ f , inr ∙ g ]

--pair : ∀{A B C D}(f : Hom A B)(g : Hom C D) → Hom (A × C) (B × D)
--pair f g = ⟨ f ∙ π₁ , g ∙ π₂ ⟩

natUnDistr : ∀{A B D X Y Z}(f : Hom A X)(g : Hom B Y)(h : Hom D Z) → (pair f (copair g h)) ∙ undistr ≅ undistr ∙ (copair (pair f g) (pair f h))
natUnDistr {A} {B} {D} {X} {Y} {Z} f g h = proof
                   pair f (copair g h) ∙ undistr
                   ≅⟨ refl ⟩
                    pair f (copair g h) ∙ [ pair iden inl , pair iden inr ]
                   ≅⟨ fusionCo ⟩
                   [ pair f (copair g h) ∙ pair iden inl ,
                     pair f (copair g h) ∙ pair iden inr ]
                   ≅⟨ cong₂ [_,_] (proof pair f (copair g h) ∙ pair iden inl
                                         ≅⟨ refl ⟩
                                          pair f (copair g h) ∙ ⟨ iden ∙ π₁ , inl ∙ π₂ ⟩
                                         ≅⟨ congr (cong₂ ⟨_,_⟩ idl refl) ⟩
                                         pair f (copair g h) ∙ ⟨ π₁ , inl ∙ π₂ ⟩
                                         ≅⟨ fusion-pair ⟩
                                         ⟨ f ∙ π₁ , copair g h ∙ inl ∙ π₂ ⟩
                                         ≅⟨ cong₂ ⟨_,_⟩ refl (sym ass) ⟩
                                         ⟨ f ∙ π₁ , (copair g h ∙ inl) ∙ π₂ ⟩
                                         ≅⟨ cong₂ ⟨_,_⟩ refl (congl inl-cop) ⟩
                                         ⟨ f ∙ π₁ , (inl ∙ g) ∙ π₂ ⟩
                                         ≅⟨ refl ⟩
                                         pair f (inl ∙ g)
                                         ≅⟨ cong₂ pair (sym idl) refl ⟩
                                         pair (iden ∙ f) (inl ∙ g)
                                         ≅⟨ comp-pair ⟩
                                         pair iden inl ∙ pair f g ∎

                                  )
                                  (proof pair f (copair g h) ∙ pair iden inr
                                         ≅⟨ refl ⟩
                                         pair f (copair g h) ∙ ⟨ iden ∙ π₁ , inr ∙ π₂ ⟩
                                         ≅⟨ congr (cong₂ ⟨_,_⟩ idl refl) ⟩
                                         pair f (copair g h) ∙ ⟨ π₁ , inr ∙ π₂ ⟩
                                         ≅⟨ fusion-pair ⟩
                                         ⟨ f ∙ π₁ , copair g h ∙ inr ∙ π₂ ⟩
                                         ≅⟨ cong₂ ⟨_,_⟩ refl (sym ass) ⟩
                                         ⟨ f ∙ π₁ , (copair g h ∙ inr) ∙ π₂ ⟩
                                         ≅⟨ cong₂ ⟨_,_⟩ refl (congl inr-cop) ⟩
                                         ⟨ f ∙ π₁ , (inr ∙ h) ∙ π₂ ⟩
                                         ≅⟨ refl ⟩
                                         pair f (inr ∙ h)
                                         ≅⟨ cong₂ pair (sym idl) refl ⟩
                                         pair (iden ∙ f) (inr ∙ h)
                                         ≅⟨ comp-pair ⟩
                                         pair iden inr ∙ pair f h ∎) ⟩
                   [ pair iden inl ∙ pair f g , pair iden inr ∙ pair f h ]
                   ≅⟨ sym fusion-cop ⟩
                   undistr ∙ copair (pair f g) (pair f h) ∎


unnull : ∀{X} → Hom I (X × I)
unnull = i

record Distributive : Set (a ⊔ b) where
  field
    distribute : ∀{X Y Z} → Iso C (undistr {X} {Y} {Z})
    nullify    : ∀{X} → Iso C (unnull {X})

  distr : ∀{X Y Z} → Hom (X × (Y + Z)) (X × Y + X × Z)
  distr {X}{Y}{Z} = Iso.inv (distribute {X} {Y} {Z})

  natDistr : ∀{A B D X Y Z}(f : Hom A X)(g : Hom B Y)(h : Hom D Z) → distr ∙ (pair f (copair g h)) ≅ (copair (pair f g) (pair f h)) ∙ distr
  natDistr f g h = proof distr ∙ pair f (copair g h)
                         ≅⟨ sym idr ⟩
                         (distr ∙ pair f (copair g h)) ∙ iden
                         ≅⟨ congr (sym (Iso.rinv distribute)) ⟩
                         (distr ∙ pair f (copair g h)) ∙ undistr ∙ distr
                         ≅⟨ sym ass ⟩
                         ((distr ∙ pair f (copair g h)) ∙ undistr) ∙ distr
                         ≅⟨ congl ass ⟩
                         (distr ∙ (pair f (copair g h) ∙ undistr)) ∙ distr
                         ≅⟨ congl (congr (natUnDistr f g h)) ⟩
                         (distr ∙ undistr ∙ copair (pair f g) (pair f h)) ∙ distr
                         ≅⟨ congl (sym ass) ⟩
                         ((distr ∙ undistr) ∙ copair (pair f g) (pair f h)) ∙ distr
                         ≅⟨ congl (congl (Iso.linv distribute)) ⟩
                         (iden ∙ copair (pair f g) (pair f h)) ∙ distr
                         ≅⟨ congl idl ⟩
                         copair (pair f g) (pair f h) ∙ distr ∎
