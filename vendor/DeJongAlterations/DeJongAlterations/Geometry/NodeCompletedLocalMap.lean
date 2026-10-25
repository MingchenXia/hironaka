import DeJongAlterations.Algebra.CompletionFlatMap
import DeJongAlterations.Algebra.CompletionLocalMapClosedFiber
import DeJongAlterations.Geometry.CompletedLocalRing
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# The actual induced map on completed local rings of an original scheme morphism

All local Noetherianity, essential finite type, and flatness hypotheses are
obtained from the original scheme morphism. No completed-map flatness is an input.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace DeJongAlterations.Geometry.NodeCompletedLocalMap

open Algebra.CompletionLocalMap Algebra.CompletionRegularityBasics

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) (x : X)

/-- The actual original structural local algebra, determined by the scheme stalk map. -/
@[instance_reducible]
def originalAlgebra : Algebra (S.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
  (f.stalkMap x).hom.toAlgebra

/-- The literal map between the actual maximal-adic completed scheme stalks. -/
def completedMap : S.completedLocalRing (f x) →+* X.completedLocalRing x :=
  completionMap (f.stalkMap x).hom

/-- The exact completed algebra of the actual original scheme stalk map. -/
@[instance_reducible]
def completedAlgebra : Algebra (S.completedLocalRing (f x)) (X.completedLocalRing x) :=
  (completedMap f x).toAlgebra

/-- Every actual original base germ has its original structural image in the completion. -/
theorem completedMap_coefficient (a : S.presheaf.stalk (f x)) :
    completedMap f x (S.toCompletedLocalRing (f x) a) =
      X.toCompletedLocalRing x (f.stalkMap x a) :=
  completionMap_algebraMap (f.stalkMap x).hom a

variable [LocallyOfFiniteType f] [IsLocallyNoetherian S]

include f in
/-- Source stalk Noetherianity is derived from the original finite type map. -/
theorem originalTarget_isNoetherianRing : IsNoetherianRing (X.presheaf.stalk x) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  infer_instance

omit [IsLocallyNoetherian S] in
/-- Original essential finite type is for precisely the actual stalk algebra. -/
theorem originalAlgebra_essFiniteType :
    letI := originalAlgebra f x
    Algebra.EssFiniteType (S.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
  LocallyOfFiniteType.stalkMap f x

omit [LocallyOfFiniteType f] [IsLocallyNoetherian S] in
/-- Original scheme flatness gives flatness of the literal original stalk algebra. -/
theorem originalAlgebra_flat [Flat f] :
    letI := originalAlgebra f x
    Module.Flat (S.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
  Flat.stalkMap f x

/-- Locality belongs to the actual induced map, with original target Noetherianity derived internally. -/
theorem completedMap_isLocalHom : IsLocalHom (completedMap f x) := by
  let := originalTarget_isNoetherianRing f x
  exact isLocalHom_completionMap (f.stalkMap x).hom

/-- Faithful flatness of the actual completed scheme stalk map. -/
theorem completedAlgebra_faithfullyFlat [Flat f] :
    letI := completedAlgebra f x
    Module.FaithfullyFlat (S.completedLocalRing (f x)) (X.completedLocalRing x) := by
  let := originalAlgebra f x
  let : IsLocalHom (algebraMap (S.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  let := originalAlgebra_essFiniteType f x
  let := originalAlgebra_flat f x
  exact Algebra.CompletionFlatMap.faithfullyFlat_completedAlgebra
    (S.presheaf.stalk (f x)) (X.presheaf.stalk x)

/-- Native ring-hom flatness for the exact completed map. -/
theorem completedMap_flat [Flat f] : (completedMap f x).Flat := by
  let := completedAlgebra f x
  let := completedAlgebra_faithfullyFlat f x
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

end DeJongAlterations.Geometry.NodeCompletedLocalMap
