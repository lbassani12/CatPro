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

-- Ahora en una categoría distributiva podemos definir una función condicional
-- Definimos el tipo Bool como:
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

-- El condicional se forma a partir de una flecha p: A →  Bool la cual nos permite definir la siguiente flecha:
 cond : ∀{A} → Hom A Bool → Hom A (A + A) 
 cond p = copair unit unit ∙ distr ∙ ⟨ iden , p ⟩
 
 -- Se puede ver como el siguiente diagrama conmuta:
 --                  ⟨ id, p ⟩
 --         A ----------------------> A x Bool (T + T)
 --         |                           |
 -- cond p  |                           | distr
 --         |                           |
 --         v                           v
 --       A + A <------------------- A × T + A × T
 
 
 -- Entonces definimos la función condicional que dependiendo de p, elige f o g como resultado
 _⇒_,_ : ∀{A B} → Hom A Bool → Hom A B → Hom A B → Hom A B 
 p ⇒ f , g = [ f , g ] ∙ cond p

 -- Y podemos probar algunas propiedades como:
 -- Es distributiva a izquierda
 
 leftDistr : ∀{A B D} → (p : Hom A Bool) → (f : Hom A B) → (g : Hom A B) → (h : Hom B D) → h ∙ (p ⇒ f , g) ≅ p ⇒ (h ∙ f) , (h ∙ g)
 leftDistr p f g h = proof h ∙ (p ⇒ f , g)
                           ≅⟨ sym ass ⟩
                           (h ∙ [ f , g ]) ∙ cond p
                           ≅⟨ congl fusionCo ⟩
                           [ h ∙ f , h ∙ g ] ∙ cond p
                           ≅⟨ refl ⟩ 
                           (p ⇒ h ∙ f , (h ∙ g)) ∎
                           
  -- Es distributiva a derecha

 rightDistr : ∀{A B D} → (p : Hom A Bool) → (f : Hom A B) → (g : Hom A B) → (h : Hom D A) → (p ⇒ f , g) ∙ h ≅ (p ∙ h) ⇒ (f ∙ h) , (g ∙ h)
 rightDistr p f g h = proof p ⇒ f , g ∙ h
                            ≅⟨ ass ⟩
                            [ f , g ] ∙ cond p ∙ h
                            ≅⟨ congr (ass) ⟩
                            [ f , g ] ∙ copair unit unit ∙ (distr ∙ ⟨ iden , p ⟩) ∙ h
                            ≅⟨ congr (congr ass) ⟩
                            [ f , g ] ∙ copair unit unit ∙ distr ∙ ⟨ iden , p ⟩ ∙ h
                            ≅⟨ congr (congr (congr fusion)) ⟩  -- Metemos la h dentro del producto
                            [ f , g ] ∙ copair unit unit ∙ distr ∙ ⟨ iden ∙ h , p ∙ h ⟩
                            ≅⟨ congr (congr (congr (cong₂ ⟨_,_⟩ (symIden h) (sym idl)))) ⟩  -- Damos vuelta
                            [ f , g ] ∙ copair unit unit ∙ distr ∙ ⟨ h ∙ iden , iden ∙ p ∙ h ⟩
                            ≅⟨ congr (congr (congr (sym fusion-pair))) ⟩ -- sacamos el h x iden afuera
                            [ f , g ] ∙
                              copair unit unit ∙ distr ∙ pair h iden ∙ ⟨ iden , p ∙ h ⟩ 
                            ≅⟨ congr (congr (congr (congl (cong₂ pair refl (sym iden-cop))))) ⟩ -- Hacemos aparecer id + id ya que es lo mismo que id
                            [ f , g ] ∙
                              copair unit unit ∙  -- Aca abajo!
                              distr ∙ pair h (copair iden iden) ∙ ⟨ iden , p ∙ h ⟩
                            ≅⟨ congr (congr (sym ass)) ⟩
                            [ f , g ] ∙
                              copair unit unit ∙
                              (distr ∙ pair h (copair iden iden)) ∙ ⟨ iden , p ∙ h ⟩
                            ≅⟨ congr (congr (congl (natDistr h iden iden))) ⟩  -- Usamos la natDistr que decia distr ∙ (pair f (copair g h)) ≅ (copair (pair f g) (pair f h)) ∙ distr
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
                            ≅⟨ congr (congl (congl (sym comp-cop))) ⟩ -- Composición de copairs
                            [ f , g ] ∙
                              (copair (unit ∙ pair h iden) (unit ∙ pair h iden) ∙ distr) ∙
                              ⟨ iden , p ∙ h ⟩
                            ≅⟨ congr (congl (congl (cong₂ copair π₁-pair π₁-pair))) ⟩  -- recordando que unit = π₁
                            [ f , g ] ∙ (copair (h ∙ unit) (h ∙ unit) ∙ distr) ∙ ⟨ iden , p ∙ h ⟩
                            ≅⟨ congr (congl (congl comp-cop)) ⟩ -- Composición de copairs al revez
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
                            ≅⟨ congr (congr refl) ⟩ -- definición de cond
                            [ f , g ] ∙
                              copair h h ∙ cond (p ∙ h)
                            ≅⟨ sym ass ⟩
                            ([ f , g ] ∙ copair h h) ∙ cond (p ∙ h)
                            ≅⟨ congl fusion-cop ⟩
                            [ f ∙ h , g ∙ h ] ∙ cond (p ∙ h)
                            ≅⟨ refl ⟩ -- reescritura
                            (p ∙ h) ⇒ f ∙ h , (g ∙ h) ∎

 lemma : ∀{A B D X Z}(f : Hom A X) (g : Hom B Z) (h : Hom D Z) → pair f [ g , h ] ≅ [ pair f g , pair f h ] ∙ distr
 lemma {A} {B} {D} {X} {Z} f g h  = proof pair f [ g , h ]
                                           ≅⟨ sym idr ⟩
                                           pair f [ g , h ] ∙ iden  
                                           ≅⟨ congr (sym (Iso.rinv distribute)) ⟩  -- hacemos aparecer undistr ∙ distr  
                                           pair f [ g , h ] ∙ undistr ∙ distr
                                           ≅⟨ refl ⟩ -- def undistr
                                           pair f [ g , h ] ∙ [ pair iden inl , pair iden inr ] ∙ distr
                                           ≅⟨ sym ass ⟩
                                           (pair f [ g , h ] ∙ [ pair iden inl , pair iden inr ]) ∙ distr
                                           ≅⟨ congl fusionCo ⟩ -- metemos el pair f [ g , h ] adentro de los []
                                           [ pair f [ g , h ] ∙ pair iden inl ,
                                             pair f [ g , h ] ∙ pair iden inr ]
                                             ∙ distr
                                           ≅⟨ congl (cong₂ [_,_] (sym comp-pair) (sym comp-pair)) ⟩  -- composición de pairs
                                           [ pair (f ∙ iden) ([ g , h ] ∙ inl) ,
                                             pair (f ∙ iden) ([ g , h ] ∙ inr) ]
                                             ∙ distr
                                           ≅⟨ congl (cong₂ [_,_] (cong₂ pair idr (Coproducts.law1 hasCoproducts)) (cong₂ pair idr (Coproducts.law2 hasCoproducts))) ⟩
                                           [ pair f g , pair f h ] ∙ distr ∎ 
  
 -- Si tenemos la misma flecha en ambos casos de la elección, el condicional nos devuelve esa flecha
 
 same : ∀{A B} → (p : Hom A Bool) → (f : Hom A B) → p ⇒ f , f ≅ f
 same {A} {B} p f = proof p ⇒ f , f
                  ≅⟨ refl ⟩
                  [ f , f ] ∙ cond p
                  ≅⟨ sym ass ⟩
                  ([ f , f ] ∙ copair unit unit) ∙ distr ∙ ⟨ iden , p ⟩
                  ≅⟨ congl fusion-cop ⟩
                  [ f ∙ unit , f ∙ unit ] ∙ distr ∙ ⟨ iden , p ⟩
                  ≅⟨ congl (cong₂ [_,_] (sym π₁-pair) (sym π₁-pair)) ⟩ -- hacemos aparecer los f x id
                  [ unit ∙ pair f iden , unit ∙ pair f iden ] ∙ distr ∙ ⟨ iden , p ⟩
                  ≅⟨ congl (sym fusionCo) ⟩
                  (unit ∙ [ pair f iden , pair f iden ]) ∙ distr ∙ ⟨ iden , p ⟩ -- sacamos unit afuera del coproducto
                  ≅⟨ ass ⟩
                  unit ∙ [ pair f iden , pair f iden ] ∙ distr ∙ ⟨ iden , p ⟩
                  ≅⟨ congr (sym ass) ⟩
                  unit ∙ ([ pair f iden , pair f iden ] ∙ distr) ∙ ⟨ iden , p ⟩
                  ≅⟨ congr (congl (sym (lemma f iden iden))) ⟩ -- aplicamos el lemma anteriormente demostrado
                  unit ∙ pair f [ iden , iden ] ∙ ⟨ iden , p ⟩
                  ≅⟨ congr (fusion-pair) ⟩
                  unit ∙ ⟨ f ∙ iden , [ iden , iden ] ∙ p ⟩
                  ≅⟨ congr (cong₂ ⟨_,_⟩ idr refl) ⟩ -- da lo mismo lo que este a la derecha del ⟨_,_⟩ 
                  unit ∙ ⟨ f , (_) ⟩
                  ≅⟨ Products.law1 hasProducts ⟩ -- ya que unit = π₁
                  f ∎ 
