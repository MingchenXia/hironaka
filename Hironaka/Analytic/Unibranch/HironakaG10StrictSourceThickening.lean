import Hironaka.Analytic.Unibranch.HironakaG10ChowTrackedDatum
import Hironaka.Resolution.HironakaG10StrictIdealRadical

/-! # Positive source thickening preserves germ strict-transform membership -/
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
namespace Hironaka.Analytic.Unibranch.HironakaG10StrictSourceThickening
open Hironaka HironakaG10ChowArtinReesCentre
  HironakaG10StrictIdealRadical
open Hironaka.Analytic.Unibranch.HironakaG10ChowTrackedDatum

/-- The germ-level strict-transform condition of an arbitrary morphism is
unchanged by a positive power of the source ideal; the centre is unchanged. -/
theorem onStrictTransform_source_pow_iff
    {X X' : SourceReducedComplexSpace} (σ : X' ⟶ X) (x' : X'.obj.left)
    (I D : Ideal (X.obj.left.presheaf.stalk (σ.hom.left.base x')))
    {β : ℕ} (hβ : β ≠ 0) :
    OnStrictTransform σ x' (I ^ β) D ↔ OnStrictTransform σ x' I D := by
  constructor
  · intro h G hG hD htop
    apply h G hG hD
    exact (strictIdeal_source_pow_eq_top_iff (σ.hom.left.stalkMap x').hom I D G hβ).mpr htop
  · intro h G hG hD htop
    apply h G hG hD
    exact (strictIdeal_source_pow_eq_top_iff (σ.hom.left.stalkMap x').hom I D G hβ).mp htop

end Hironaka.Analytic.Unibranch.HironakaG10StrictSourceThickening
