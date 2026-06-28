import Mathlib
import Mathlib.CategoryTheory.Category.Basic

universe u

-- Bundling a carrier term together with the class structure of monoids
structure Mon where
  carrier : Type u
  [str : Monoid carrier]
attribute [instance] Mon.str

/- Defining an instance of the class CategoryTheory.Category where a morphism is
 a monoid homomorphism, the identity is identity homomorphism, and the composition of two
 homomorphisms is just the monoid homomorphism composition. Proofs for category properties
 are automatically fulfilled  -/

instance : CategoryTheory.Category Mon where
  Hom G H := MonoidHom G.carrier H.carrier
  id G := MonoidHom.id G.carrier
  comp f g := MonoidHom.comp g f
