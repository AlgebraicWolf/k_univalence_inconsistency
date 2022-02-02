module Main where
open import Preamble

-- Formulating Axiom K 
AxiomK : Typeω
AxiomK = {u : Level} {A : Type u} {x : A} → (P : x ≡ x → Type u) → P refl → (h : x ≡ x) → P h

-- Equivalent axiom is Uniqueness of Identity Proof (UIP):
AxiomUIP : Typeω
AxiomUIP = {u : Level} {A : Type u} {x y : A} → (p q : x ≡ y) → p ≡ q

-- We can derive UIP from K:
K→UIP : AxiomK → AxiomUIP
K→UIP K {u} {A} {x} = J (λ y₁ p' → ((q' : x ≡ y₁) → p' ≡ q')) (K (λ q → refl ≡ q) refl)

-- And K from UIP:
UIP→K : AxiomUIP → AxiomK
UIP→K UIP P onRefl h = subst P (UIP refl h) onRefl

-- Canonical mapping of paths to isomorphisms
pathToIso' : {A B : Type} → A ≡ B → A ≅ B
pathToIso' {A} {B} p = J (λ y _ → A ≅ y) iso' p where

    iso' : {A : Type} → A ≅ A
    iso' = iso (λ x → x) (λ x → x) (λ b → refl) λ a → refl

-- The inconsistency follows from the fact that UIP pronounces any two proofs of equality to be equal.
-- However, this is not the case in HoTT, and we can show that by constructing two equalities on Bool 

-- The first equality will be derived from an isomorphism of form:
flip : Bool → Bool
flip false = true
flip true = false

-- Let's show that it is an isomorphism:
flipIso : Bool ≅ Bool
flipIso = iso flip flip rightInv leftInv where

    rightInv : section flip flip
    rightInv false = refl
    rightInv true = refl

    leftInv : retract flip flip
    leftInv false = refl
    leftInv true = refl

-- Univalence allows to derive equality:
flipPath : Bool ≡ Bool
flipPath = isoToPath flipIso

-- Another equality is trivial one 
idPath : Bool ≡ Bool
idPath = refl

-- The corresponding function
idBool : Bool → Bool
idBool x = x

-- Now, assuming Axiom K, we can apply UIP to show that these two are themselves equal 
K→idPath≡flipPath : AxiomK → idPath ≡ flipPath
K→idPath≡flipPath K = K→UIP K idPath flipPath

-- The idea is that following from true along idPath, we'd get true, and following along flipPath,
-- we'd get false. This, in turn, would give us path true ≡ false

K→true≡false : AxiomK → true ≡ false
K→true≡false K = cong (λ path → transport path true) (K→idPath≡flipPath K)

-- To show that this is absurd, we will define a nontrivial subsingleton bundle over Bool
boolBundle : Bool → Type
boolBundle false = ⊥
boolBundle true = ⊤

-- Finally, following along path true≡false, we get the proof of ⊥
K→⊥ : AxiomK → ⊥
K→⊥ K = subst boolBundle (K→true≡false K) tt

-- q. e. d.
