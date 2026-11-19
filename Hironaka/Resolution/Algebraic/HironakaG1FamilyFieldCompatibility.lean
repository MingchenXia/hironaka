import Hironaka.Resolution.Algebraic.HironakaG1PaddedFieldComparison
import Hironaka.Resolution.Algebraic.ActualReducedAlgebraicSmoothResolutionFamily

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Hironaka.Sequence
universe u
namespace Hironaka.Resolution.Algebraic.HironakaG1FamilyFieldCompatibility
open ActualReducedAlgebraicSmoothResolutionFamily
noncomputable section

instance : HasChangeOfFields ReducedAlgebraicScheme where
  IsFieldBaseChange {_ _} _ _ σ X XL p :=
    IsPullback p XL.obj.hom X.obj.hom (Spec.map (CommRingCat.ofHom σ))

theorem resolutionFamily_commutesWithChangeOfFields :
    CommutesWithChangeOfFields resolutionFamily := by
  intro k L _ _ _ _ σ X XL p h
  let : Algebra k L := σ.toAlgebra
  let : IsReduced XL.obj.left := XL.property
  let : IsNoetherian XL.obj.left := XL.obj.hom.isNoetherian_of_field
  let : LocallyOfFiniteType XL.obj.hom := inferInstance
  let : IsSeparated XL.obj.hom := XL.obj.prop.2
  let : IsReduced X.obj.left := X.property
  let : IsNoetherian X.obj.left := X.obj.hom.isNoetherian_of_field
  let : LocallyOfFiniteType X.obj.hom := inferInstance
  let : IsSeparated X.obj.hom := X.obj.prop.2
  let : IsReduced ((𝟭 Scheme).obj XL.obj.left) := XL.property
  let : IsReduced ((𝟭 Scheme).obj X.obj.left) := X.property
  let : IsNoetherian ((𝟭 Scheme).obj XL.obj.left) := XL.obj.hom.isNoetherian_of_field
  let : IsNoetherian ((𝟭 Scheme).obj X.obj.left) := X.obj.hom.isNoetherian_of_field
  let : IsNoetherian (HasUnderlyingScheme.scheme X) := by
    change IsNoetherian X.obj.left
    exact X.obj.hom.isNoetherian_of_field
  let : IsNoetherian (HasUnderlyingScheme.scheme XL) := by
    change IsNoetherian XL.obj.left
    exact XL.obj.hom.isNoetherian_of_field
  let : IsReduced (HasUnderlyingScheme.scheme X) := by
    change IsReduced X.obj.left
    exact X.property
  let : IsReduced (HasUnderlyingScheme.scheme XL) := by
    change IsReduced XL.obj.left
    exact XL.property
  change IsPullback p XL.obj.hom X.obj.hom (Spec.map (CommRingCat.ofHom σ)) at h
  change ActualGlobalStrongResolutionSmoothNaturality.resolutionHistory XL.obj.hom =
    (ActualGlobalStrongResolutionSmoothNaturality.resolutionHistory X.obj.hom).pullback p
  exact HironakaG1PaddedFieldComparison.resolutionHistory_baseChange_of_source h

end
end Hironaka.Resolution.Algebraic.HironakaG1FamilyFieldCompatibility
