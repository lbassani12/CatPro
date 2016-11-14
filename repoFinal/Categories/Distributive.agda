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
-- Vamos a definir categorías distributivas, estas son las categorías que teniendo productos y coproductos se pueden definir los siguientes isomorfismos naturales
-- A x (B + C) \cong (A x B) + (A x C)
-- A x 0 \cong 0
-- Pero para ello necesitamos que existan los morfismos
-- undistr: (A x B) + (A x C) \-> A x (B + C)
-- distr:   A x (B + C) \-> (A x B) + (A x C) 
-- unnull:  0 \-> A x 0
-- null:    A x 0 -> 0

-- y que undistr \. distr \cong distr \. undistr \cong id lo mismo con null y unnull

-- Defino undistr y unnull ya que son mas simples.

-- Para recordar definiciones:

--copair : ∀{X Y Z W}(f : Hom X Z)(g : Hom Y W) → Hom (X + Y) (Z + W)
--copair f g = [ inl ∙ f , inr ∙ g ]

--pair : ∀{A B C D}(f : Hom A B)(g : Hom C D) → Hom (A × C) (B × D)
--pair f g = ⟨ f ∙ π₁ , g ∙ π₂ ⟩

undistr : ∀{X Y Z} → Hom (X × Y + X × Z) (X × (Y + Z))
undistr = [ pair iden inl , pair iden inr ]

-- Con esta definición podemos probar que para cualquier flechas 
-- f: A -> X, 
-- g: B -> Y, 
-- h: D -> Z
-- (f x (g + h)) . undistr = undistr . ((f x g) + (f x h))

natUnDistr : ∀{A B D X Y Z}(f : Hom A X)(g : Hom B Y)(h : Hom D Z) → (pair f (copair g h)) ∙ undistr ≅ undistr ∙ (copair (pair f g) (pair f h))
natUnDistr {A} {B} {D} {X} {Y} {Z} f g h = proof
                   pair f (copair g h) ∙ undistr
                   ≅⟨ refl ⟩      -- definición de undistr
                    pair f (copair g h) ∙ [ pair iden inl , pair iden inr ]
                   ≅⟨ fusionCo ⟩  -- h ∙ [ f , g ] ≅ [ h ∙ f , h ∙ g ]
                   [ pair f (copair g h) ∙ pair iden inl ,
                     pair f (copair g h) ∙ pair iden inr ]
                   ≅⟨ cong₂ [_,_] (proof pair f (copair g h) ∙ pair iden inl  -- prueba (f x (g + h)) . (id x inl) = (id x inl) (f x g)
                                         ≅⟨ refl ⟩  -- def pair
                                          pair f (copair g h) ∙ ⟨ iden ∙ π₁ , inl ∙ π₂ ⟩
                                         ≅⟨ congr (cong₂ ⟨_,_⟩ idl refl) ⟩ -- id . f = f 
                                         pair f (copair g h) ∙ ⟨ π₁ , inl ∙ π₂ ⟩
                                         ≅⟨ fusion-pair ⟩  --  (f x g) ∙ ⟨ h , i ⟩ ≅ ⟨ f ∙ h , g ∙ i ⟩
                                         ⟨ f ∙ π₁ , copair g h ∙ inl ∙ π₂ ⟩
                                         ≅⟨ cong₂ ⟨_,_⟩ refl (sym ass) ⟩
                                         ⟨ f ∙ π₁ , (copair g h ∙ inl) ∙ π₂ ⟩
                                         ≅⟨ cong₂ ⟨_,_⟩ refl (congl inl-cop) ⟩  -- (g + h) . inl = inl . g
                                         ⟨ f ∙ π₁ , (inl ∙ g) ∙ π₂ ⟩
                                         ≅⟨ refl ⟩  -- def pair
                                         pair f (inl ∙ g) 
                                         ≅⟨ cong₂ pair (sym idl) refl ⟩ -- f = f . id
                                         pair (iden ∙ f) (inl ∙ g)
                                         ≅⟨ comp-pair ⟩  -- (f . g) x (h . j) = f x h . g x j
                                         pair iden inl ∙ pair f g ∎

                                  )
                                  (proof pair f (copair g h) ∙ pair iden inr  -- prueba (f x (g + h)) . (id x inr) = (id x inr) . (f x h)
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
                   ≅⟨ sym fusion-cop ⟩ -- usando [ h , i ] ∙ (f + g) ≅ [ h ∙ f , i ∙ g ]
                                       -- nos queda [id x inl, id x inr] . ((f x g) + (f x h)) y por la def de undistr
                                       -- undistr . ((f x g) + (f x h))
                   undistr ∙ copair (pair f g) (pair f h) ∎

-- definimos unnull
unnull : ∀{X} → Hom I (X × I)
unnull = i


-- Luego definimos null y distr como isomorfimos de unnull y undistr respectivamente

record Distributive : Set (a ⊔ b) where
  field
    distribute : ∀{X Y Z} → Iso C (undistr {X} {Y} {Z})
    nullify    : ∀{X} → Iso C (unnull {X})

  distr : ∀{X Y Z} → Hom (X × (Y + Z)) (X × Y + X × Z)
  distr {X}{Y}{Z} = Iso.inv (distribute {X} {Y} {Z})

-- Probamos la naturalidad de distr con ayuda de la naturalidad de undistr ya que nos va a servir luego.

  natDistr : ∀{A B D X Y Z}(f : Hom A X)(g : Hom B Y)(h : Hom D Z) → distr ∙ (pair f (copair g h)) ≅ (copair (pair f g) (pair f h)) ∙ distr
  natDistr f g h = proof distr ∙ pair f (copair g h)
                         ≅⟨ sym idr ⟩      -- hacemos aparecer una iden a la derecha
                         (distr ∙ pair f (copair g h)) ∙ iden
                         ≅⟨ congr (sym (Iso.rinv distribute)) ⟩  -- undistr \. distr = id
                         (distr ∙ pair f (copair g h)) ∙ undistr ∙ distr
                         ≅⟨ sym ass ⟩
                         ((distr ∙ pair f (copair g h)) ∙ undistr) ∙ distr
                         ≅⟨ congl ass ⟩
                         (distr ∙ (pair f (copair g h) ∙ undistr)) ∙ distr
                         ≅⟨ congl (congr (natUnDistr f g h)) ⟩    -- Usamos la naturalidad de undistr anteriormente probada
                         (distr ∙ undistr ∙ copair (pair f g) (pair f h)) ∙ distr
                         ≅⟨ congl (sym ass) ⟩
                         ((distr ∙ undistr) ∙ copair (pair f g) (pair f h)) ∙ distr
                         ≅⟨ congl (congl (Iso.linv distribute)) ⟩  -- distr \. undistr = id    
                         (iden ∙ copair (pair f g) (pair f h)) ∙ distr
                         ≅⟨ congl idl ⟩
                         copair (pair f g) (pair f h) ∙ distr ∎
